package cs320

package object proj03 extends Project03 {
  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)
  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)

  private def assert(c: Boolean, msg: String): Unit =
    if(!c)
      error(msg)

  object T {
    import Typed._

    private type TypeEnv = Map[TypeKey, TypeValue]

    private sealed trait TypeKey
    private case class TypeName(name: String) extends TypeKey
    private case class TypeIdentifier(name: String) extends TypeKey
    private case class TypeVariable(variable: VarT) extends TypeKey

    private sealed trait TypeValue
    private case class TypeScheme(typ: Type, targs: List[VarT], mutable: Boolean) extends TypeValue
    private case class TypeDefinition(variants: List[Variant], variables: List[VarT]) extends TypeValue
    private case object TypeVariableValue extends TypeValue

    private def isWellFormed(t: Type, env: TypeEnv): Boolean =
      t match {
        case IntT => true
        case BooleanT => true
        case UnitT => true
        case vt: VarT =>
          env.get(TypeVariable(vt)) match {
            case Some(TypeVariableValue) => true
            case _ => false
          }

        case AppT(name, targs) =>
          (
            targs.forall(isWellFormed(_, env)) &&
            (env.get(TypeName(name)) match {
              case Some(TypeDefinition(variants, variables)) => {
                variables.length == targs.length
              }

              case _ => false
            })
          )
        case ArrowT(ptypes, rtype) =>
          ptypes.forall(isWellFormed(_, env)) && isWellFormed(rtype, env)
      }

    private def assertWellFormed(t: Type, env: TypeEnv): Unit =
      assert(isWellFormed(t, env), s"TypeError: $t is not well-formed")

    private def substituteType(needles: Map[String, Type], haystack: Type): Type =
      haystack match {
        case IntT => haystack
        case BooleanT => haystack
        case UnitT => haystack
        case VarT(name) =>
          needles.get(name) match {
            case Some(target) => target
            case None => haystack
          }

        case AppT(name, targs) =>
          AppT(name, targs.map(substituteType(needles, _)))

        case ArrowT(ptypes, rtype) =>
          ArrowT(ptypes.map(substituteType(needles, _)), substituteType(needles, rtype))
      }

    private def typeCheckId(x: String, ts: List[Type], env: TypeEnv): Type = {
      ts.foreach(t => assertWellFormed(t, env))
      env.get(TypeIdentifier(x)) match {
        case Some(TypeScheme(typ, targs, _)) => {
          val paramsLen = targs.length
          val argsLen = ts.length

          assert(
            targs.length == ts.length,
            s"TypeError: $x takes $paramsLen parameters, but $argsLen arguments were given"
          )

          substituteType(Map() ++ targs.map(_.name).zip(ts), typ)
        }

        case _ => error(s"ReferenceError: $x is not defined")
      }
    }

    private def typeCheckIntOp(left: Expr, right: Expr, env: TypeEnv, returnType: Type): Type = {
      assert(
        typeCheck(left, env) == IntT && typeCheck(right, env) == IntT,
        s"TypeError: Integer operation on illegal type"
      )
      returnType
    }

    private def typeCheckSequence(left: Expr, right: Expr, env: TypeEnv): Type = {
      typeCheck(left, env)
      typeCheck(right, env)
    }

    private def typeCheckIf(cond: Expr, tExpr: Expr, fExpr: Expr, env: TypeEnv): Type = {
      assert(
        typeCheck(cond, env) == BooleanT,
        s"TypeError: Boolean operation on illegal type: $cond"
      )

      val returnType = typeCheck(tExpr, env)

      assert(
        returnType == typeCheck(fExpr, env),
        s"TypeError: If-else clause has different type"
      )

      returnType
    }

    private def typeCheckVal(
      mut: Boolean, name: String, typ: Option[Type], expr: Expr, body: Expr, env: TypeEnv
    ): Type = {
      val exprType = typ match {
        case Some(typeVal) => {
          assertWellFormed(typeVal, env)

          val exprType = typeCheck(expr, env)
          assert(exprType == typeVal, s"TypeError: Cannot instantiate $typeVal variable with $exprType")

          exprType
        }
        case _ => typeCheck(expr, env)
      }

      typeCheck(body, env + (TypeIdentifier(name) -> TypeScheme(exprType, Nil, mut)))
    }

    private def typeCheckRecBinds(defs: List[RecDef], body: Expr, env: TypeEnv) = {
      val finalEnv = defs.foldLeft(env)(
        (prevEnv, recdef) => recdef match {
          case TypeDef(name, tparams, variants) => {
            assert(
              !prevEnv.contains(TypeIdentifier(name)),
              s"ReferenceError: Type name '$name' has already been declared"
            )

            val targs = tparams.map(VarT(_))

            prevEnv + (
              TypeName(name) -> TypeDefinition(variants, targs)
            ) ++ (
              variants.map(variant => (
                TypeIdentifier(variant.name) -> TypeScheme(
                  {
                    if(variant.params.length > 0)
                      ArrowT(variant.params, AppT(name, targs))

                    else
                      AppT(name, targs)
                  },
                  targs,
                  false
                )
              ))
            )
          }

          case RecFun(name, tparams, params, rtype, _) => {
            prevEnv + (TypeIdentifier(name) -> TypeScheme(
              ArrowT(params.map(_._2), rtype),
              tparams.map(VarT(_)),
              false
            ))
          }

          case Lazy(name, typ, expr) => {
            prevEnv + (TypeIdentifier(name) -> TypeScheme(
              typ,
              Nil,
              false
            ))
          }
        }
      )

      defs.foreach(_ match {
        case TypeDef(name, tparams, variants) => {
          assert(
            tparams.forall(paramName => !finalEnv.contains(TypeName(paramName))),
            s"ReferenceError: Type name '$name' has already been declared"
          )

          val newEnv = finalEnv ++ (tparams.map(param => (TypeVariable(VarT(param)) -> TypeVariableValue)))

          variants.foreach(variant =>
            variant.params.foreach(param => assertWellFormed(param, newEnv))
          )
        }

        case RecFun(name, tparams, params, rtype, body) => {
          assert(
            tparams.forall(paramName => !finalEnv.contains(TypeName(paramName))),
            s"ReferenceError: Type name '$name' has already been declared"
          )

          val newEnv = finalEnv ++ (tparams.map(param => (TypeVariable(VarT(param)) -> TypeVariableValue)))
          params.map(_._2).foreach(param => assertWellFormed(param, newEnv))
          assertWellFormed(rtype, newEnv)

          val newNewEnv = newEnv ++ (params.map(param => {
            (TypeIdentifier(param._1) -> TypeScheme(param._2, Nil, false))
          }))

          assert(
            typeCheck(body, newNewEnv) == rtype,
            s"TypeError: Return type $rtype does not match"
          )
        }

        case Lazy(name, typ, expr) => {
          assertWellFormed(typ, finalEnv)
          assert(
            typeCheck(expr, finalEnv) == typ,
            s"TypeError: the type of lazy evaluation does not match with $typ"
          )
        }
      })

      typeCheck(body, finalEnv)
    }

    private def typeCheckFun(params: List[(String, Type)], body: Expr, env: TypeEnv): Type = {
      val paramTypes = params.map(_._2)
      paramTypes.foreach(assertWellFormed(_, env))

      val newEnv = params.foldLeft(env)((env, param) => env + (TypeIdentifier(param._1) -> TypeScheme(
        param._2,
        Nil,
        true
      )))

      val rtype = typeCheck(body, newEnv)
      ArrowT(paramTypes, rtype)
    }

    private def typeCheckAssign(name: String, expr: Expr, env: TypeEnv): Type =
      env.get(TypeIdentifier(name)) match {
        case Some(TypeScheme(typ, targs, mut)) => {
          assert(targs.length == 0, s"TypeError: $name is not instantiated")
          assert(mut, s"TypeError: $name is immutable")
          assert(typ == typeCheck(expr, env), s"TypeError: assigning illegal type for $typ type")

          UnitT
        }

        case _ => error(s"ReferenceError: Not defined: $name")
      }

    private def typeCheckApp(funExpr: Expr, args: List[Expr], env: TypeEnv): Type = {
      val funType = typeCheck(funExpr, env) match {
        case at: ArrowT => at
        case _ => error(s"TypeError: function calling for illegal type")
      }

      var paramLen = funType.ptypes.length
      var argsLen = args.length
      assert(
        argsLen == paramLen,
        s"TypeError: function takes $paramLen parameters, but $argsLen arguments were given"
      )

      args.zipWithIndex.foreach(_ match {
        case (arg, index) =>
          assert(
            typeCheck(arg, env) == funType.ptypes(index),
            s"TypeError: illegal type given for $index-th parameter of function"
          )
      })

      funType.rtype
    }

    private def typeCheckMatch(expr: Expr, cases: List[Case], env: TypeEnv): Type =
      typeCheck(expr, env) match {
        case AppT(name, targs) => {
          env.get(TypeName(name)) match {
            case Some(TypeDefinition(variants, variables)) => {
              assert(
                variables.length == targs.length,
                s"TypeError: definition takes ${variables.length} parameters, but ${targs.length} arguments were given"
              )

              assert(
                cases.length == variants.length,
                s"TypeError: ${cases.length} cases exist for $name but ${variants.length} cases were given"
              )

              val variantMap = Map.empty ++ variants.map(_.name).zip(variants)
              val caseTypes = cases.map(_ match {
                case Case(variantName, names, body) => {
                  val variant = variantMap.get(variantName) match {
                    case Some(x) => x
                    case None => error(s"TypeError: no matching type variant $variantName for $name")
                  }

                  assert(
                    variant.params.length == names.length,
                    s"TypeError: variant takes${variant.params.length} arguments, but got  ${names.length}"
                  )

                  val newParams = variant.params.map(paramType => {
                    val needles = Map.empty ++ variables.map(_.name).zip(targs)
                    substituteType(needles, paramType)
                  })

                  val newEnv = env ++ names
                    .map(TypeIdentifier(_))
                    .zip(newParams.map(TypeScheme(_, Nil, false)))

                  typeCheck(body, newEnv)
                }
              })

              assert(
                caseTypes.forall(_ == caseTypes(0)),
                s"TypeError: type differs for pattern matching cases"
              )

              caseTypes(0)
            }

            case _ => error(s"TypeError: non-existing definition for pattern matching")
          }
        }
        case _ => error(s"TypeError: illegal type given for pattern matching")
      }

    private def typeCheck(expr: Expr, env: TypeEnv): Type =
      expr match {
        case Id(x, ts) => typeCheckId(x, ts, env)
        case IntE(_) => IntT
        case BooleanE(_) => BooleanT
        case UnitE => UnitT
        case Add(left, right) => typeCheckIntOp(left, right, env, IntT)
        case Mul(left, right) => typeCheckIntOp(left, right, env, IntT)
        case Div(left, right) => typeCheckIntOp(left, right, env, IntT)
        case Mod(left, right) => typeCheckIntOp(left, right, env, IntT)
        case Eq(left, right) => typeCheckIntOp(left, right, env, BooleanT)
        case Lt(left, right) => typeCheckIntOp(left, right, env, BooleanT)
        case Sequence(left, right) => typeCheckSequence(left, right, env)
        case If(cond, texpr, fexpr) => typeCheckIf(cond, texpr, fexpr, env)
        case Val(mut, name, typ, expr, body) => typeCheckVal(mut, name, typ, expr, body, env)
        case RecBinds(defs, body) => typeCheckRecBinds(defs, body, env)
        case Fun(params, body) => typeCheckFun(params, body, env)
        case Assign(name, expr) => typeCheckAssign(name, expr, env)
        case App(fun, args) => typeCheckApp(fun, args, env)
        case Match(expr, cases) => typeCheckMatch(expr, cases, env)

        case _ => UnitT
      }

    def typeCheck(expr: Expr): Type = typeCheck(expr, Map.empty)
  }

  object U {
    import Untyped._

    private type Store = Map[Addr, Value]

    private def ensureNonZero(op: (Int, Int) => Value): (Int, Int) => Value =
      (x, y) => (x * y) match {
        case 0 => error(s"Uncaught ArithmeticError: dividing by zero")
        case _ => op(x, y)
      }

    private def malloc(store: Store): Addr =
      if (store.size > 0)
        store.keysIterator.max + 1

      else
        0

    private def interpId(name: String, env: Env, sto: Store): (Value, Store) = {
      val addr = env.getOrElse(name, error(s"Uncaught ReferenceError: $name is not defined"))
      val value = sto.getOrElse(addr, error(s"Uncaught SegmentationError: $addr points to non-existing value"))
      value match {
        case ExprV(expr, eenv) => {
          interp(expr, eenv, sto) match {
            case (newValue, newSto) => (newValue, newSto + (addr -> newValue))
          }
        }

        case _ => (value, sto)
      }
    }

    private def interpIntOp(op: (Int, Int) => Value): (Expr, Expr, Env, Store) => (Value, Store) =
      (l, r, env, sto) => {
        interp(l, env, sto) match {
          case (IntV(x), newSto) => interp(r, env, newSto) match {
            case (IntV(y), newNewSto) => (op(x, y), newNewSto)
            case _ => error(s"Uncaught TypeError: making a integer operation on illegal type: $r")
          }

          case _ => error(s"Uncaught TypeError: making a integer operation on illegal type: $l")
        }
      }

    private val interpIntAdd = interpIntOp((x, y) => IntV(x + y))
    private val interpIntMul = interpIntOp((x, y) => IntV(x * y))
    private val interpIntDiv = interpIntOp(ensureNonZero((x, y) => IntV(x / y)))
    private val interpIntMod = interpIntOp(ensureNonZero((x, y) => IntV(x % y)))
    private val interpIntEq = interpIntOp((x, y) => BooleanV(x == y))
    private val interpIntLt = interpIntOp((x, y) => BooleanV(x < y))

    private def interpSeq(e1: Expr, e2: Expr, env: Env, sto: Store): (Value, Store) = {
      val (v1, newSto) = interp(e1, env, sto)
      interp(e2, env, newSto)
    }

    private def interpIf(cond: Expr, texpr: Expr, fexpr: Expr, env: Env, sto: Store): (Value, Store) = {
      val (condVal, newSto) = interp(cond, env, sto)
      condVal match {
        case BooleanV(true) => interp(texpr, env, newSto)
        case BooleanV(false) => interp(fexpr, env, newSto)
        case _=> error(s"Uncaught TypeError: Boolean operation on illegal type: $condVal")
      }
    }

    private def interpVal(name: String, expr: Expr, body: Expr, env: Env, sto: Store): (Value, Store) = {
      val (value, sto1) = interp(expr, env, sto)
      val addr = malloc(sto1)
      val newEnv = env + (name -> addr)
      val newSto = sto1 + (addr -> value)

      interp(body, newEnv, newSto)
    }

    private def interpRecBinds(defs: List[RecDef], body: Expr, env: Env, sto: Store): (Value, Store) = {
      val (newEnv, newSto) = defs.foldLeft((env, sto))((envSto, recdef) => {
        val (envi, stoi) = envSto

        recdef match {
          case Lazy(name, _) => {
            val addr = malloc(stoi)
            (envi + (name -> addr), stoi + (addr -> UnitV))
          }

          case RecFun(name, _, _) => {
            val addr = malloc(stoi)
            (envi + (name -> addr), stoi + (addr -> UnitV))
          }

          case TypeDef(variants) => {
            variants.foldLeft((envi, stoi))((envStoi, variant) => {
              val (envij, stoij) = envStoi
              val addr = malloc(stoij)

              (envij + (variant.name -> addr), stoij + (addr -> UnitV))
            })
          }
        }
      })

      val newNewSto = defs.foldLeft((newSto))((newStoi, recdef) => {
        recdef match {
          case Lazy(name, expr) => {
            val addr = newEnv.getOrElse(name, error(s"Uncaught InternalError"))
            newStoi + (addr -> ExprV(expr, newEnv))
          }

          case RecFun(name, params, body) => {
            val addr = newEnv.getOrElse(name, error(s"Uncaught InternalError"))
            newStoi + (addr -> CloV(params, body, newEnv))
          }

          case TypeDef(variants) => {
            variants.foldLeft(newStoi)((newStoij, variant) => {
              val addr = newEnv.getOrElse(variant.name, error(s"Uncaught InternalError"))

              if(variant.empty)
                newStoij + (addr -> VariantV(variant.name, Nil))

              else
                newStoij + (addr -> ConstructorV(variant.name))
            })
          }
        }
      })

      interp(body, newEnv, newNewSto)
    }

    private def interpAssign(name: String, expr: Expr, env: Env, sto: Store): (Value, Store) = {
      val addr = env.getOrElse(name, error(s"Uncaught ReferenceError: $name is not defined"))
      val (newVal, newSto) = interp(expr, env, sto)
      (UnitV, newSto + (addr -> newVal))
    }

    private def interpApp(fun: Expr, args: List[Expr], env: Env, sto: Store): (Value, Store) = {
      val (v, sto1) = interp(fun, env, sto)
      val (argv, newSto) = args.foldLeft((List[Value](), sto1))((listSto, arg) => {
        val (argList, stoi) = listSto
        val (argi, stoi1) = interp(arg, env, stoi)

        ((argList :+ argi), stoi1)
      })

      v match {
        case CloV(params, body, fenv) => {
          assert(
            params.length == argv.length,
            s"TypeError: $v takes ${params.length} parameters, but ${argv.length} arguments were given"
          )

          val (funEnv, funSto) = params.zip(argv).foldLeft((fenv, newSto))((envSto, paramArg) => {
            val (funEnv, funSto) = envSto
            val (paramName, argValue) = paramArg

            val addr = malloc(funSto)

            (funEnv + (paramName -> addr), funSto + (addr -> argValue))
          })

          interp(body, funEnv, funSto)
        }

        case ConstructorV(name) => {
          (VariantV(name, argv), newSto)
        }

        case _ => error(s"Uncaught TypeError: calling for illegal type: $v")
      }
    }

    private def interpMatch(expr: Expr, cases: List[Case], env: Env, sto: Store): (Value, Store) = {
      val (v, sto1) = interp(expr, env, sto)
      val varv = v match {
        case vv: VariantV => vv
        case _ => error(s"Uncaught TypeError: pattern matching for illegal type: $v")
      }

      val matchCase = cases.find(matchCase => matchCase.variant == varv.name).getOrElse(
        error(s"Uncaught TypeError: no matching type variant ${varv.name}")
      )

      assert(
        matchCase.names.length == varv.values.length,
        s"TypeError: definition takes ${matchCase.names.length} parameters, " +
        s"but ${varv.values.length} arguments were given"
      )

      val (newEnv, newSto) = matchCase.names.zip(varv.values).foldLeft((env, sto1))((envSto, nameValue) => {
        val (argName, argValue) = nameValue
        val (envi, stoi) = envSto

        val addr = malloc(stoi)
        (envi + (argName -> addr), stoi + (addr -> argValue))
      })

      interp(matchCase.body, newEnv, newSto)
    }

    private def interp(expr: Expr, env: Env, sto: Store): (Value, Store) =
      expr match {
        case Id(name) => interpId(name, env, sto)

        case IntE(i) => (IntV(i), sto)
        case BooleanE(b) => (BooleanV(b), sto)
        case UnitE => (UnitV, sto)
        case Fun(params, body) => (CloV(params, body, env), sto)

        case Add(l, r) => interpIntAdd(l, r, env, sto)
        case Mul(l, r) => interpIntMul(l, r, env, sto)
        case Div(l, r) => interpIntDiv(l, r, env, sto)
        case Mod(l, r) => interpIntMod(l, r, env, sto)
        case Eq(l, r) => interpIntEq(l, r, env, sto)
        case Lt(l, r) => interpIntLt(l, r, env, sto)
        case Sequence(l, r) => interpSeq(l, r, env, sto)
        case If(cond, texpr, fexpr) => interpIf(cond, texpr, fexpr, env, sto)
        case Val(name, expr, body) => interpVal(name, expr, body, env, sto)
        case RecBinds(defs, body) => interpRecBinds(defs, body, env, sto)
        case Assign(name, expr) => interpAssign(name, expr, env, sto)
        case App(fun, args) => interpApp(fun, args, env, sto)
        case Match(expr, cases) => interpMatch(expr, cases, env, sto)
      }

    def interp(expr: Expr): Value = interp(expr, Map.empty, Map.empty)._1
  }

  def tests: Unit = {
    // test-int
    test(run("42"), "42")
    // test-boolean
    test(run("true"), "true")
    // test-unit
    test(run("()"), "()")

    // test-add
    test(run("1 + 2"), "3")
    // test-mul
    test(run("2 * 4"), "8")
    // test-div
    test(run("5 / 2"), "2")
    // test-mod
    test(run("13 % 5"), "3")
    // test-eq
    test(run("1 == 1"), "true")
    // test-lt
    test(run("1 < 1"), "false")
    // test-seq
    test(run("{1; 2}"), "2")

    // test-if
    test(run("if (true) 1 else 2"), "1")

    // test-val
    test(run("""
      val x = 1 + 2;
      val y: Int = x * 4 + 1;
      y / (x - 1)
    """), "6")
    // test-lazy
    test(run("""
      lazy val f: Int => Int = (x: Int) => if (x < 1) 0 else x + f(x - 1);
      f(10)
    """), "55")
    // test-rec
    test(run("""
      def f(x: Int): Int = if (x < 1) 0 else x + f(x - 1);
      f(10)
    """), "55")

    // test-fun
    test(run("(x: Int) => x + x"), "<function>")
    // test-app
    test(run("((x: Int, y: Int) => x + y)(1, 2)"), "3")

    // test-var-assign
    test(run("""
      var x = 1;
      var y: Int = x * 4 + 8;
      { x = 3; y / (x - 1) }
    """), "6")

    // test-type-match
    test(run("""
      type Fruit {
        case Apple
        case Banana(Int)
      }
      (Apple match {
        case Apple => 1
        case Banana(x) => 0
      }) + (Banana(1) match {
        case Apple => 0
        case Banana(x) => x
      })
    """), "2")

    // test-poly1
    test(run("""
      def f['T, 'S](t: 'T, s: 'S): 'T = t;
      f[Int, Boolean](1, true)
    """), "1")
    // test-poly2
    test(run("""
      type Fruit['T] {
        case Apple
        case Banana('T)
      }
      (Apple[Boolean] match {
        case Apple => 1
        case Banana(x) => 0
      }) + (Banana[Int](1) match {
        case Apple => 0
        case Banana(x) => x
      })
    """), "2")

    // test-primitive
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

{
check(!intEquals(1, 2));
check(intEquals(3, 3));
check(intMax(3, 6) == 6);
check(intMin(3, 6) == 3);
check(!booleanEquals(true, false));
check(booleanEquals(true, true));
check(unitEquals((), ()));

score
}"""
      ),
      "7"
    )

    // test-pair
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val p1 = Pair[Int, Boolean](1, true);
val p2 = Pair[Int, Boolean](1, false);
val p3 = Pair[Int, Boolean](2, true);

val eq = pairEquals[Int, Boolean](intEquals, booleanEquals);

{
check(pairFst[Int, Boolean](p1) == 1);
check(pairSnd[Int, Boolean](p1));
check(pairFst[Int, Boolean](p2) == 1);
check(!pairSnd[Int, Boolean](p2));
check(pairFst[Int, Boolean](p3) == 2);
check(pairSnd[Int, Boolean](p3));
check(eq(p1, p1));
check(!eq(p1, p2));
check(!eq(p1, p3));

score
}"""
      ),
      "9"
    )

    // test-option
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val opt1 = Some[Int](1);
val opt2 = optionMap[Int, Int](opt1, (x: Int) => x + x);
val opt3 = optionFilter[Int](opt1, (x: Int) => x < 2);
val opt4 = optionFilter[Int](opt2, (x: Int) => x < 2);
val opt5 = optionFlatten[Int](Some[Option[Int]](opt1));
val opt6 = optionFlatten[Int](Some[Option[Int]](opt4));
val opt7 = optionFlatten[Int](None[Option[Int]]);

def aux(i: Int): Option[Int] =
  if (i == 1) Some[Int](i) else None[Int];

val opt8 = optionFlatMap[Int, Int](opt1, aux);
val opt9 = optionFlatMap[Int, Int](opt2, aux);
val opt10 = optionFlatMap[Int, Int](opt4, aux);
val opt11 = optionFilterNot[Int](opt1, (x: Int) => x < 2);
val opt12 = optionFilterNot[Int](opt2, (x: Int) => x < 2);

val eq = optionEquals[Int](intEquals);
val eql = listEquals[Int](intEquals);

{
check(eq(Some[Int](1), Some[Int](1)));
check(!eq(Some[Int](1), Some[Int](2)));
check(!eq(Some[Int](1), None[Int]));
check(eq(None[Int], None[Int]));
check(eq(opt1, Some[Int](1)));
check(eq(opt2, Some[Int](2)));
check(eq(opt3, Some[Int](1)));
check(eq(opt4, None[Int]));
check(eq(opt5, Some[Int](1)));
check(eq(opt6, None[Int]));
check(eq(opt7, None[Int]));
check(eq(opt8, Some[Int](1)));
check(eq(opt9, None[Int]));
check(eq(opt10, None[Int]));
check(eq(opt11, None[Int]));
check(eq(opt12, Some[Int](2)));
check(!optionIsEmpty[Int](opt1));
check(optionIsEmpty[Int](opt4));
check(optionNonEmpty[Int](opt1));
check(!optionNonEmpty[Int](opt4));
check(eql(optionToList[Int](opt1), List1[Int](1)));
check(eql(optionToList[Int](opt4), List0[Int]()));
check(optionGetOrElse[Int](opt1, 0) == 1);
check(optionGetOrElse[Int](opt4, 0) == 0);
optionForeach[Int](opt1, (i: Int) => check(i == 1));
optionForeach[Int](opt4, (i: Int) => check(true));

score
}"""
      ),
      "25"
    )

    // test-box
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val b = Box[Int](1);
val i1 = boxGet[Int](b);
val i2 = boxSet[Int](b, 2);
val i3 = boxGet[Int](b);
val i4 = boxSet[Int](b, 1);
val i5 = boxGet[Int](b);

{
check(i1 == 1);
check(i2 == 1);
check(i3 == 2);
check(i4 == 2);
check(i5 == 1);

score
}"""
      ),
      "5"
    )

    // test-list
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val l0 = List5[Int](1, 2, 3, 4, 5);
val l1 = List3[Int](1, 2, 3);
val l2 = List2[Int](4, 5);
val zipped0 = listZip[Int, Int](l0, l0);
val unzipped0 = listUnzip[Int, Int](zipped0);
val l3 = pairFst[List[Int], List[Int]](unzipped0);
val l4 = pairSnd[List[Int], List[Int]](unzipped0);
val zipped1 = listZip[Int, Int](l0, l1);
val unzipped1 = listUnzip[Int, Int](zipped1);
val l5 = pairFst[List[Int], List[Int]](unzipped1);
val l6 = pairSnd[List[Int], List[Int]](unzipped1);
val zipped2 = listZipWithIndex[Int](l0);
val unzipped2 = listUnzip[Int, Int](zipped2);
val l7 = pairFst[List[Int], List[Int]](unzipped2);
val l8 = pairSnd[List[Int], List[Int]](unzipped2);

val eq = listEquals[Int](intEquals);
val eqo = optionEquals[Int](intEquals);
def odd(n: Int): Boolean = n % 2 != 0;
def lt4(n: Int): Boolean = n < 4;

{
check(eq(l0, l0));
check(!eq(l0, l1));
check(!eq(l0, l2));
check(!eq(l1, l2));
check(!eq(l0, Nil[Int]));
check(eq(Nil[Int], Nil[Int]));
check(eq(listAppended[Int](listAppended[Int](l1, 4), 5), l0));
check(eq(listConcat[Int](l1, l2), l0));
check(listCount[Int](l0, odd) == 3);
check(eq(listDrop[Int](l0, 3), l2));
check(listExists[Int](l0, lt4));
check(!listExists[Int](l2, lt4));
check(eq(listFilter[Int](l0, lt4), l1));
check(eq(listFilterNot[Int](l0, lt4), l2));
check(eqo(listFind[Int](l0, lt4), Some[Int](1)));
check(eqo(listFind[Int](l2, lt4), None[Int]));
check(eq(listFlatMap[Int, Int](l1, (n: Int) => if (n == 1) l1 else if (n == 2) l2 else Nil[Int]), l0));
check(eq(listFlatten[Int](List2[List[Int]](l1, l2)), l0));
check(listFoldLeft[Int, Int](0, l0, (n: Int, m: Int) => n + m) == 15);
check(listFoldRight[Int, Int](l0, 0, (n: Int, m: Int) => n + m) == 15);
check(!listForall[Int](l0, lt4));
check(listForall[Int](l1, lt4));
listForeach[Int](l0, (n: Int) => check(odd(n)));
check(eqo(listGet[Int](l0, 4), Some[Int](5)));
check(eqo(listGet[Int](l0, 5), None[Int]));
check(!listIsEmpty[Int](l0));
check(listIsEmpty[Int](Nil[Int]));
check(listLength[Int](l0) == 5);
check(eq(listMap[Int, Int](l0, (n: Int) => n * n), List5[Int](1, 4, 9, 16, 25)));
check(listNonEmpty[Int](l0));
check(!listNonEmpty[Int](Nil[Int]));
check(eq(listPrepended[Int](listPrepended[Int](listPrepended[Int](l2, 3), 2), 1), l0));
check(eq(listReverse[Int](l0), List5[Int](5, 4, 3, 2, 1)));
check(eq(listTake[Int](l0, 3), l1));
check(eq(l0, l3));
check(eq(l0, l4));
check(eq(l1, l5));
check(eq(l1, l6));
check(eq(l0, l7));
check(eq(l0, listMap[Int, Int](l8, (n: Int) => n + 1)));

score
}"""
      ),
      "42"
    )

    // test-map
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val m0 = Map1[Int, Int](intEquals, 0, 0);
val m1 = mapUpdated[Int, Int](m0, 1, 2);
val m2 = mapUpdated[Int, Int](m1, 2, 4);
val m3 = mapUpdated[Int, Int](m2, 3, 6);
val m4 = mapRemoved[Int, Int](m3, 2);
val m5 = mapUpdated[Int, Int](m2, 3, 8);

val eqo = optionEquals[Int](intEquals);

{
check(eqo(mapGet[Int, Int](m0, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m0, 1), None[Int]));
check(eqo(mapGet[Int, Int](m0, 2), None[Int]));
check(eqo(mapGet[Int, Int](m0, 3), None[Int]));
check(eqo(mapGet[Int, Int](m0, 4), None[Int]));

check(eqo(mapGet[Int, Int](m1, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m1, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m1, 2), None[Int]));
check(eqo(mapGet[Int, Int](m1, 3), None[Int]));
check(eqo(mapGet[Int, Int](m1, 4), None[Int]));

check(eqo(mapGet[Int, Int](m2, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m2, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m2, 2), Some[Int](4)));
check(eqo(mapGet[Int, Int](m2, 3), None[Int]));
check(eqo(mapGet[Int, Int](m2, 4), None[Int]));

check(eqo(mapGet[Int, Int](m3, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m3, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m3, 2), Some[Int](4)));
check(eqo(mapGet[Int, Int](m3, 3), Some[Int](6)));
check(eqo(mapGet[Int, Int](m3, 4), None[Int]));

check(eqo(mapGet[Int, Int](m4, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m4, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m4, 2), None[Int]));
check(eqo(mapGet[Int, Int](m4, 3), Some[Int](6)));
check(eqo(mapGet[Int, Int](m4, 4), None[Int]));

check(eqo(mapGet[Int, Int](m4, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m4, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m4, 2), None[Int]));
check(eqo(mapGet[Int, Int](m4, 3), Some[Int](6)));
check(eqo(mapGet[Int, Int](m4, 4), None[Int]));

score
}"""
      ),
      "30"
    )

    // test-string
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

{
check(stringEquals("abc \n"<STRP, EOS>, List5[Int](97, 98, 99, 32, 10)));
check(stringEquals(substring("12abc \n"<STRP, EOS>, 2, 5), List3[Int](97, 98, 99)));
check("abc \n"<(n: Int, m: Int) => n + m, 0> == 336);

score
}"""
      ),
      "3"
    )

    // test-fae
    test(
      runWithStdLib(
"""
type Expr {
  case Num(Int)
  case Add(Expr, Expr)
  case Sub(Expr, Expr)
  case Id(Int)
  case Fun(Int, Expr)
  case App(Expr, Expr)
}

type Value {
  case NumV(Int)
  case CloV(Int, Expr, Map[Int, Value])
}

def interp(e: Expr, env: Map[Int, Value]): Option[Value] = e match {
  case Num(n) => Some[Value](NumV(n))
  case Add(l, r) => optionFlatMap[Value, Value](interp(l, env), (lv: Value) => lv match {
    case NumV(n) => optionFlatMap[Value, Value](interp(r, env),
      (rv: Value) => rv match {
        case NumV(m) => Some[Value](NumV(n + m))
        case CloV(x, e, fenv) => None[Value]
      }
    )
    case CloV(x, e, fenv) => None[Value]
  })
  case Sub(l, r) => optionFlatMap[Value, Value](interp(l, env), (lv: Value) => lv match {
    case NumV(n) => optionFlatMap[Value, Value](interp(r, env),
      (rv: Value) => rv match {
        case NumV(m) => Some[Value](NumV(n - m))
        case CloV(x, e, fenv) => None[Value]
      }
    )
    case CloV(x, e, fenv) => None[Value]
  })
  case Id(x) => mapGet[Int, Value](env, x)
  case Fun(x, e) => Some[Value](CloV(x, e, env))
  case App(f, a) => optionFlatMap[Value, Value](interp(f, env), (fv: Value) => fv match {
    case NumV(n) => None[Value]
    case CloV(x, e, fenv) => optionFlatMap[Value, Value](interp(a, env),
      (av: Value) => interp(e, mapUpdated[Int, Value](fenv, x, av))
    )
  })
};

lazy val digit: Parser[Expr] =
  parserMap[Int, Expr](
    () => parserCond((x: Int) => 48 <= x && x < 58),
    (x: Int) => Num(x - 48)
  );

lazy val add: Parser[Expr] =
  parserMap[Pair[Int, Pair[Expr, Expr]], Expr](
    () => parserThen[Int, Pair[Expr, Expr]](
      () => parserConst(43),
      () => parserThen[Expr, Expr](() => e, () => e)
    ),
    (p: Pair[Int, Pair[Expr, Expr]]) =>
      pairSnd[Int, Pair[Expr, Expr]](p) match {
        case Pair(l, r) => Add(l, r)
      }
  );

lazy val sub: Parser[Expr] =
  parserMap[Pair[Int, Pair[Expr, Expr]], Expr](
    () => parserThen[Int, Pair[Expr, Expr]](
      () => parserConst(45),
      () => parserThen[Expr, Expr](() => e, () => e)
    ),
    (p: Pair[Int, Pair[Expr, Expr]]) =>
      pairSnd[Int, Pair[Expr, Expr]](p) match {
        case Pair(l, r) => Sub(l, r)
      }
  );

lazy val id: Parser[Expr] =
  parserMap[Int, Expr](
    () => parserCond((x: Int) => 97 <= x && x <= 122),
    (x: Int) => Id(x)
  );

lazy val fun: Parser[Expr] =
  parserMap[Pair[Int, Pair[Int, Expr]], Expr](
    () => parserThen[Int, Pair[Int, Expr]](
      () => parserConst(47),
      () => parserThen[Int, Expr](
        () => parserCond((x: Int) => 97 <= x && x <= 122),
        () => e
      )
    ),
    (p: Pair[Int, Pair[Int, Expr]]) =>
      pairSnd[Int, Pair[Int, Expr]](p) match {
        case Pair(p, b) => Fun(p, b)
      }
  );

lazy val app: Parser[Expr] =
  parserMap[Pair[Int, Pair[Expr, Expr]], Expr](
    () => parserThen[Int, Pair[Expr, Expr]](
      () => parserConst(64),
      () => parserThen[Expr, Expr](() => e, () => e)
    ),
    (p: Pair[Int, Pair[Expr, Expr]]) =>
      pairSnd[Int, Pair[Expr, Expr]](p) match {
        case Pair(l, r) => App(l, r)
      }
  );

lazy val e: Parser[Expr] =
  parserOr[Expr](
    () => parserOr[Expr](
      () => parserOr[Expr](
        () => parserOr[Expr](
          () => parserOr[Expr](
            () => digit,
            () => add
          ),
          () => sub
        ),
        () => id
      ),
      () => fun
    ),
    () => app
  );

parseAll[Expr](e, "@@/x/y+xy23"<STRP, EOS>) match {
  case None => -1
  case Some(e) => interp(e, Map0[Int, Value](intEquals)) match {
    case None => -2
    case Some(v) => v match {
      case NumV(n) => if (n < 0) -3 else n
      case CloV(x, e, env) => -4
    }
  }
}
"""
      ),
      "5"
    )
  }

}
