package cs320

package object midterm extends Midterm {
  private def malloc(sto: ObjStore): Addr = (-1 :: sto.keys.toList).max + 1

  private def interpId(name: String, env: Env, sto: ObjStore): (Value, ObjStore) =
    env.get(name) match {
      case Some(v) => (v, sto)
      case None => error(s"ReferenceError: not defined: $name")
    }

  private def interpIntOp(op: (Int, Int) => Value): (Expr, Expr, Env, ObjStore) => (Value, ObjStore) =
    (l, r, env, sto) => {
      val (lv, ls) = interp(l, env, sto)
      val (rv, rs) = interp(r, env, ls)

      (lv, rv) match {
        case (IntV(x), IntV(y)) => (op(x, y), rs)
        case (x, y) => error(s"TypeError: making a integer operation on at least one illegal type: $x, $y")
      }
    }

  private val interpIntAdd = interpIntOp((x, y) => IntV(x + y))
  private val interpIntMul = interpIntOp((x, y) => IntV(x * y))
  private val interpIntDiv = interpIntOp((x, y) => IntV(x / y))
  private val interpIntMod = interpIntOp((x, y) => IntV(x % y))
  private val interpIntEq = interpIntOp((x, y) => BooleanV(x == y))
  private val interpIntLt = interpIntOp((x, y) => BooleanV(x < y))

  private def interpIf(c: Expr, t: Expr, f: Expr, env: Env, sto: ObjStore): (Value, ObjStore) = {
    val (cv, cs) = interp(c, env, sto)

    cv match {
      case BooleanV(condition) =>
        if(condition) interp(t, env, cs) else interp(f, env, cs)

      case _ => error(s"TypeError: evaluating condition for illegal type: $c")
    }
  }

  private def interpVal(x: String, e: Expr, b: Expr, env: Env, sto: ObjStore): (Value, ObjStore) = {
    val (value, newStore) = interp(e, env, sto)
    interp(b, env + (x -> value), newStore)
  }

  private def interpRecFuns(ds: List[FunDef], b: Expr, env: Env, sto: ObjStore): (Value, ObjStore) = {
    val funs = ds.foldLeft(Map[String, CloV]())((funs, fdef) => {
      val fun = CloV(fdef.ps, fdef.b, env)
      funs + (fdef.n -> fun)
    })

    val nenv = env ++ funs

    funs.foreach(_ match {
      case (name, fun) => {
        fun.env = nenv
      }
    })

    interp(b, nenv, sto)
  }

  private def interpApp(f: Expr, as: List[Expr], env: Env, sto: ObjStore): (Value, ObjStore) = {
    val (fv, fs) = interp(f, env, sto)

    fv match {
      case CloV(ps, b, fenv) =>
        val paramLen = ps.length
        val argsLen = as.length

        if(paramLen != argsLen)
          error(s"TypeError: function takes $paramLen parameters, but $argsLen arguments were given")
        else {
          val (argList, argStore) = as.foldLeft((List[Value](), fs))(
            (argState: (List[Value], ObjStore), currArg: Expr) => {
              val (argList, store) = argState
              val (argv, args) = interp(currArg, env, store)
              (argv :: argList, args)
            }
          )

          interp(b, fenv ++ ps.zip(argList), argStore)
        }

      case _ => error(s"TypeError: calling for illegal type: $f")
    }
  }

  private def interpObjV(env: Env, sto: ObjStore): (Value, ObjStore) = {
    val addr = malloc(sto)
    (ObjV(addr), sto + {addr -> Map[FiberKey, FiberValue]()})
  }

  private def interpObjGet(obj: Expr, key: String, env: Env, sto: ObjStore): (Value, ObjStore) = {
    val (ov, os) = interp(obj, env, sto)

    ov match {
      case ObjV(addr) => sto.get(addr) match {
          case Some(objValue) => objValue.get(key) match {
              case Some(value) => (value, os)
              case None => error(s"KeyError: the object has no such key: $key")
            }

          case None => error(s"UnknownError: the object variable points non-existing object")
        }

      case _ => error(s"TypeError: Cannot read property '$key' of illegal type: $obj")
    }
  }

  private def interpObjSet(
    obj: Expr, key: String, value: Expr, body: Expr, env: Env, sto: ObjStore
  ): (Value, ObjStore) = {
    val (ov, os) = interp(obj, env, sto)

    ov match {
      case ObjV(addr) =>
        sto.get(addr) match {
          case Some(objValue) => {
            val (vv, vs) = interp(value, env, os)
            val newStore = vs + (addr -> (objValue + (key -> vv)))

            interp(body, env, newStore)
          }
          case None => error(s"UnknownError: the object variable points non-existing object")
        }

      case _ => error(s"TypeError: Cannot read property '$key' of illegal type: $obj")
    }
  }

  private def interpProto(baseObj: Expr, env: Env, sto: ObjStore): (Value, ObjStore) = {
    val (bov, bos) = interp(baseObj, env, sto)

    val addr = malloc(sto)
    (ObjV(addr), sto + {addr -> {"$Prototype" -> bov}})
  }

  def interp(e: Expr, env: Env, sto: ObjStore): (Value, ObjStore) = e match {
    // Variables
    case Id(name) => interpId(name, env, sto)

    // Primitives
    case IntE(n) => (IntV(n), sto)
    case BooleanE(b) => (BooleanV(b), sto)
    case Fun(ps, b) => (CloV(ps, b, env), sto)
    case RecFuns(ds: List[FunDef], b: Expr) => interpRecFuns(ds, b, env, sto)

    // Operations
    case Add(l, r) => interpIntAdd(l, r, env, sto)
    case Mul(l, r) => interpIntMul(l, r, env, sto)
    case Div(l, r) => interpIntDiv(l, r, env, sto)
    case Mod(l, r) => interpIntMod(l, r, env, sto)
    case Eq(l, r) => interpIntEq(l, r, env, sto)
    case Lt(l, r) => interpIntLt(l, r, env, sto)
    case If(c, t, f) => interpIf(c, t, f, env, sto)
    case Val(x, e, b) => interpVal(x, e, b, env, sto)
    case App(f, as) => interpApp(f, as, env, sto)

    // Objects
    case ObjE => interpObjV(env, sto)
    case ObjGet(obj, key) => interpObjGet(obj, key, env, sto)
    case ObjSet(obj, key, value, body) => interpObjSet(obj, key, value, body, env, sto)

    // Prototypes
    case ProtoE(baseObj) => interpProto(baseObj, env, sto)
    case ProtoClass(const, proto) => interpProtoClass(const, proto, env, sto)
    case ProtoMethod(obj, key) => interpProtoMethod(obj, key, env, sto)
  }

  def tests: Unit = {
    // test-int
    test(run("42"), "42")
    // test-add
    test(run("1 + 2"), "3")
    // test-sub
    test(run("7 - 2"), "5")
    // test-mul
    test(run("2 * 4"), "8")
    // test-div
    test(run("5 / 2"), "2")
    // test-mod
    test(run("13 % 5"), "3")
    // test-neg
    test(run("1 - -1"), "2")

    // test-boolean
    test(run("true"), "true")
    // test-eq
    test(run("1 == 3 - 2"), "true")
    // test-lt
    test(run("1 < 3 - 2"), "false")

    // test-local1
    test(run("""
      val x = 1 + 2;
      val y = x * 4 + 1;
      y / (x - 1)
    """), "6")

    // test-fun
    test(run("x => x + x"), "<function>")
    // test-app1
    test(run("(x => x + x)(1)"), "2")
    // test-app2
    test(run("(x => y => x + y)(1)(2)"), "3")
    // test-app3
    test(run("((x, y) => x + y)(1, 2)"), "3")

    // test-if
    test(run("if (true) 1 else 2"), "1")
    // test-not
    test(run("!true"), "false")
    // test-and
    test(run("true && false"), "false")
    // test-or
    test(run("true || false"), "true")
    // test-neq
    test(run("1 != 2"), "true")
    // test-lte
    test(run("1 <= 1"), "true")
    // test-gt
    test(run("1 > 1"), "false")
    // test-gte
    test(run("1 >= 1"), "true")

    // test-rec1
    test(run("""
      def f(x) = x - 1;
      f(2)
    """), "1")
    // test-rec2
    test(run("""
      def f(x) = if (x < 1) 0 else x + f(x - 1);
      f(10)
    """), "55")

    // ================== Midterm Code ==================
    // ObjParser
    // test-objparser-obje
    test(
      Expr("{}"), ObjE
    )

    // test-objparser-objget
    test(
      Expr("{}.x"), ObjGet(ObjE, "x")
    )

    // test-objparser-objset-1
    test(
      Expr("{}.y = 3; 0"), ObjSet(ObjE, "y", IntE(3), IntE(0))
    )

    // test-objparser-objset-2
    test(
      Expr("{}.x.y = 3; 0"), ObjSet(ObjGet(ObjE, "x"), "y", IntE(3), IntE(0))
    )

    test(
      Expr(
        """
        val obj = {};
        obj.x = 1;
        obj.x
        """
      ),
      Val(
        "obj",
        ObjE,
        ObjSet(
          Id("obj"),
          "x",
          IntE(1),
          ObjGet(Id("obj"), "x")
        )
      )
    )

    // ProtoParser
    test(
      Expr("(class [(this) => this, {extends[{}]}]())->x()"),
      App(ProtoMethod(
        App(ProtoClass(
          Fun("this" :: Nil, Id("this")),
          ProtoE(ObjE)
        ), Nil),
        "x"
      ), Nil)
    )

    test(run(
      """
      val AnimalPrototype = {};
      AnimalPrototype.age = 0;
      AnimalPrototype.newYear = (this) => this.age = this.age + 1; this.age;

      val AnimalConstructor = (this, age) =>
        this.age = age;
        this;

      val Animal = class [AnimalConstructor, AnimalPrototype];

      val ImmortalAnimalPrototype = {extends [AnimalPrototype]};
      ImmortalAnimalPrototype.newYear = (this) => this.age;

      val myAnimal = Animal(15);
      val immortalJellyfish = ImmortalAnimal(0);

      myAnimal->newYear() + immortalJellyfish->newYear()
      """
    ), 16)
  }
}
