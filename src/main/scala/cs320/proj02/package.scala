package cs320

package object proj02 extends Project02 {
  
  // Please let us to use async/await/Future ...
  private type IntCont   = Int         => Value
  private type BoolCont  = Boolean     => Value
  private type TupleCont = List[Value] => Value
  private type ConsCont  = List[Value] => Value
  
  private def unwrapInt(expr: Expr, env: Env, k: IntCont, ek: ECont): Value =
    interp(expr, env, (value) => {
      value match {
        case IntV(intValue) => k(intValue)
        case _              => error(s"TypeError: Integer operation on illegal type: $value")
      }
    }, ek)
  
  private def unwrapBool(expr: Expr, env: Env, k: BoolCont, ek: ECont): Value =
    interp(expr, env, (value) => {
      value match {
        case BooleanV(boolValue) => k(boolValue)
        case _                   => error(s"TypeError: Boolean operation on illegal type: $value")
      }
    }, ek)
  
  private def unwrapTuple(expr: Expr, env: Env, k: TupleCont, ek: ECont): Value =
    interp(expr, env, (value) => {
      value match {
        case TupleV(values) => k(values)
        case _              => error(s"TypeError: Tuple operation on illegal type: $value")
      }
    }, ek)
  
  private def makeTuple(exprs: List[Expr], values: List[Value], env: Env, cb: List[Value] => Value, ek: ECont): Value =
    exprs match {
      case expr :: left =>
        interp(expr, env, (value) => {
          makeTuple(left, value :: values, env, cb, ek)
        }, ek)
      
      case Nil =>
        cb(values)
    }
  
  private def interpId(name: String, env: Env, k: Cont, ek: ECont): Value =
    env.get(name) match {
      case Some(v) => k(v)
      case None    => error(s"ReferenceError: Not defined: $name")
    }
  
  private def interpTuple(expressions: List[Expr], env: Env, k: Cont, ek: ECont): Value =
    makeTuple(expressions.reverse, Nil, env, (values) => {
      k(TupleV(values))
    }, ek)
  
  private def interpCons(head: Expr, tail: Expr, env: Env, k: Cont, ek: ECont): Value =
    interp(head, env, (headValue) => {
      interp(tail, env, (tailValue) => {
        tailValue match {
          case NilV     => k(ConsV(headValue, NilV))
          case v: ConsV => k(ConsV(headValue, v))
          case _        => error(s"TypeError: Making list with non-list: $tailValue")
        }
      }, ek)
    }, ek)
    
  private def interpIntOp(intOp: (Int, Int) => Value): (Expr, Expr, Env, Cont, ECont) => Value =
    (left, right, env, k, ek) =>
      unwrapInt(left, env, (leftInt) => {
        unwrapInt(right, env, (rightInt) => {
          k(intOp(leftInt, rightInt))
        }, ek)
      }, ek)
  
  private val interpIntAdd = interpIntOp((x, y) => IntV(x + y))
  private val interpIntMul = interpIntOp((x, y) => IntV(x * y))
  private val interpIntDiv = interpIntOp((x, y) => IntV(x / y))
  private val interpIntMod = interpIntOp((x, y) => IntV(x % y))
  private val interpIntEq  = interpIntOp((x, y) => BooleanV(x == y))
  private val interpIntLt  = interpIntOp((x, y) => BooleanV(x < y))
  
  private def interpIf(condition: Expr, trueBranch: Expr, falseBranch: Expr, env: Env, k: Cont, ek: ECont): Value =
    unwrapBool(condition, env, (condValue) => {
      if (condValue)
        interp(trueBranch, env, k, ek)
      
      else
        interp(falseBranch, env, k, ek)
    }, ek)
  
  private def interpProj(expression: Expr, index: Int, env: Env, k: Cont, ek: ECont): Value =
    unwrapTuple(expression, env, (values) => {
      values.lift(index - 1) match {
        case Some(v) => k(v)
        case None    => error(s"RangeError: Projecting on non existent index: $index")
      }
    }, ek)
  
  private def interpConsOp(
    consOp: (Value, Value) => Value,
    nilOp: () => Value = () => error(s"TypeError: making a list operation on nil type")
  ): (Expr, Env, Cont, ECont) => Value =
    (cons, env, k, ek) => interp(cons, env, consValue => {
      consValue match {
        case ConsV(h, t) => k(consOp(h, t))
        case NilV        => k(nilOp())
        case _           => error(s"TypeError: List operation on illegal type: $consValue")
      }
    }, ek)
  
  private val interpEmpty = interpConsOp((_, _) => BooleanV(false), () => BooleanV(true))
  private val interpHead = interpConsOp((h, _) => h)
  private val interpTail = interpConsOp((_, t) => t)
  
  private def interpVal(name: String, expr: Expr, body: Expr, env: Env, k: Cont, ek: ECont): Value =
    interp(expr, env, (value) => {
      interp(body, env + (name -> value), k, ek)
    }, ek)
  
  private def interpCont(name: String, body: Expr, env: Env, k: Cont, ek: ECont): Value =
    interp(body, env + (name -> ContV(k)), k, ek)
  
  private def interpRecFuns(functions: List[FunDef], body: Expr, env: Env, k: Cont, ek: ECont): Value = {
    val functionValues = functions.foldLeft(Map[String, CloV]())((functions, definition) => {
      val fun = CloV(definition.parameters, definition.body, env)
      functions + (definition.name -> fun)
    })

    val nenv = env ++ functionValues

    functionValues.foreach(_ match {
      case (name, fun) => {
        fun.env = nenv
      }
    })

    interp(body, nenv, k, ek)
  }
  
  private def interpApp(function: Expr, arguments: List[Expr], env: Env, k: Cont, ek: ECont): Value =
    interp(function, env, (value) => {
      value match {
        case CloV(params, body, fenv) =>
          makeTuple(
            arguments, Nil, env, (argumentsValue) => {
              val paramLen = params.length
              val argsLen = argumentsValue.length

              if(paramLen != argsLen)
                error(s"TypeError: function takes $paramLen parameters, but $argsLen arguments were given")
              
              else
                interp(body, fenv ++ params.zip(argumentsValue), k, ek)
            }, ek
          )
        
        case ContV(continuation) =>
          makeTuple(
            arguments, Nil, env, (argumentsValue) => {
              val argsLen = argumentsValue.length
              if(argsLen != 1)
                error(s"TypeError: continuation takes 1 parameter, but $argsLen arguments were given")
              
              else
                continuation(argumentsValue(0))
            }, ek
          )
        
        case _ => error(s"TypeError: Calling for illegal type: $value")
      }
    }, ek)
  
  private def interpTest(expression: Expr, t: Type, env: Env, k: Cont, ek: ECont): Value =
    interp(expression, env, (value) => {
      k(value match {
        case IntV(_)                  => BooleanV(t == IntT)
        case BooleanV(_)              => BooleanV(t == BooleanT)
        case TupleV(_)                => BooleanV(t == TupleT)
        case ConsV(_, _)   | NilV     => BooleanV(t == ListT)
        case CloV(_, _, _) | ContV(_) => BooleanV(t == FunctionT)
      })
    }, ek)
  
  private def interpThrow(expr: Expr, env: Env, k: Cont, ek: ECont): Value =
    interp(expr, env, (value) => {
      ek match {
        case Some(cont) =>
          cont(value)
        
        case None =>
          error("Uncaught Exception: $value")
      }
    }, ek)
  
  private def interpTry(expr: Expr, handler: Expr, env: Env, k: Cont, ek: ECont): Value =
    interp(expr, env, k, Some((errorValue) => {
      interp(handler, env, (handlerFn) => {
        handlerFn match {
          case CloV(params, body, fenv) => {
            if(params.length != 1)
              error(s"TypeError: catch handler should have 1 parameter")
            
            interp(body, fenv + (params(0) -> errorValue), k, ek)
          }
          
          case ContV(continuation) => {
            continuation(errorValue)
          }
          
          case _ =>
            error(s"TypeError: Calling for illegal type: $handlerFn")
        }
      }, ek)
    }))
  
  def interp(e: Expr, env: Env, k: Cont, ek: ECont): Value =
      e match {
        case Id(name)                                     => interpId(name, env, k, ek)
        case IntE(value)                                  => k(IntV(value))
        case BooleanE(value)                              => k(BooleanV(value))
        case TupleE(expressions)                          => interpTuple(expressions, env, k, ek)
        case NilE                                         => k(NilV)
        case ConsE(head, tail)                            => interpCons(head, tail, env, k, ek)
        case Add(left, right)                             => interpIntAdd(left, right, env, k, ek)
        case Mul(left, right)                             => interpIntMul(left, right, env, k, ek)
        case Div(left, right)                             => interpIntDiv(left, right, env, k, ek)
        case Mod(left, right)                             => interpIntMod(left, right, env, k, ek)
        case Eq(left, right)                              => interpIntEq(left, right, env, k, ek)
        case Lt(left, right)                              => interpIntLt(left, right, env, k, ek)
        case If(condition, trueBranch, falseBranch)       => interpIf(condition, trueBranch, falseBranch, env, k, ek)
        case Proj(expression, index)                      => interpProj(expression, index, env, k, ek)
        case Empty(expression)                            => interpEmpty(expression, env, k, ek)
        case Head(expression)                             => interpHead(expression, env, k, ek)
        case Tail(expression)                             => interpTail(expression, env, k, ek)
        case Val(name, expression, body)                  => interpVal(name, expression, body, env, k, ek)
        case Vcc(name, body)                              => interpCont(name, body, env, k, ek)
        case Fun(parameters, body)                        => k(CloV(parameters, body, env))
        case RecFuns(functions: List[FunDef], body: Expr) => interpRecFuns(functions, body, env, k, ek)
        case App(function: Expr, arguments: List[Expr])   => interpApp(function, arguments, env, k, ek)
        case Test(expression: Expr, typ: Type)            => interpTest(expression, typ, env, k, ek)
        case Throw(expression: Expr)                      => interpThrow(expression, env, k, ek)
        case Try(expression: Expr, handler: Expr)         => interpTry(expression, handler, env, k, ek)
        
        case _ => k(IntV(0))
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

    // test-tuple1
    test(run("(1, 2 + 3, true)"), "(1, 5, true)")
    // test-tuple2
    test(run("((42, 3 * 2), false)"), "((42, 6), false)")
    // test-proj1
    test(run("(1, 2 + 3, true)._1"), "1")
    // test-proj2
    test(run("((42, 3 * 2), false)._1._2"), "6")

    // test-nil
    test(run("Nil"), "Nil")
    // test-cons
    test(run("1 :: 1 + 1 :: Nil"), "(1 :: (2 :: Nil))")
    // test-isempty1
    test(run("Nil.isEmpty"), "true")
    // test-isempty2
    test(run("(1 :: Nil).isEmpty"), "false")
    // test-head
    test(run("(1 :: Nil).head"), "1")
    // test-tail
    test(run("(1 :: Nil).tail"), "Nil")
    // test-tail-head
    test(run("(1 :: 2 :: Nil).tail.head"), "2")

    // test-val1
    test(run("""
      val x = 1 + 2;
      val y = x * 4 + 1;
      y / (x - 1)
    """), "6")
    // test-val2
    test(run("""
      val (x, y) = (1 + 2, 3 + 4);
      val z = x * y;
      val (a, b, c) = (z, z + z, z + z + z);
      c - b
    """), "21")

    // test-fun
    test(run("x => x + x"), "<function>")
    // test-app1
    test(run("(x => x + x)(1)"), "2")
    // test-app2
    test(run("(x => y => x + y)(1)(2)"), "3")
    // test-app3
    test(run("((x, y) => x + y)(1, 2)"), "3")

    // test-type1
    test(run("1.isInstanceOf[Int]"), "true")
    // test-type2
    test(run("1.isInstanceOf[Boolean]"), "false")
    // test-type3
    test(run("(1 :: Nil).isInstanceOf[List]"), "true")
    // test-type4
    test(run("(x => x + x).isInstanceOf[Function]"), "true")

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
    // test-nonempty
    test(run("Nil.nonEmpty"), "false")

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

    // test-vcc1
    test(run("""
      vcc x;
      1 + x(1) + 1
    """), "1")
    // test-vcc2
    test(run("""
      (x => x * x)(
        1 + vcc x; 1 + x(2) + 3
      )
    """), "9")

    // test-return1
    test(run("(x => (return 1) + x)(2)"), "1")
    // test-return2
    test(run("""
      def div(x) = (x => 10 / x)(
        if (x == 0) return 0 else x
      );
      div(0) + div(10)
    """), "1")

    // test-throw1
    testExc(run("throw 1"), "")
    // test-throw2
    testExc(run("throw throw 1"), "")

    // test-try1
    test(run("""
      try {
        throw 1
      } catch (
        x => x + x
      )
    """), "2")
    // test-try2
    test(run("""
      1 + vcc x;
        try {
          throw 1
        } catch x
    """), "2")
  }
}
