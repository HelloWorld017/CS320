package cs320

package object midterm extends Midterm {
  private def interpId(name: String, env: Env): Value =
    env.get(name) match {
      case Some(v) => v
      case None => error(s"ReferenceError: not defined: $name")
    }

  private def interpIntOp(op: (Int, Int) => Value): (Expr, Expr, Env) => Value =
    (l, r, env) => (interp(l, env), interp(r, env)) match {
      case (IntV(x), IntV(y)) => op(x, y)
      case (x, y) => error(s"TypeError: making a integer operation on at least one illegal type: $x, $y")
    }

  private val interpIntAdd = interpIntOp((x, y) => IntV(x + y))
  private val interpIntMul = interpIntOp((x, y) => IntV(x * y))
  private val interpIntDiv = interpIntOp((x, y) => IntV(x / y))
  private val interpIntMod = interpIntOp((x, y) => IntV(x % y))
  private val interpIntEq = interpIntOp((x, y) => BooleanV(x == y))
  private val interpIntLt = interpIntOp((x, y) => BooleanV(x < y))

  private def interpIf(c: Expr, t: Expr, f: Expr, env: Env): Value =
    interp(c, env) match {
      case BooleanV(condition) => if(condition) interp(t, env) else interp(f, env)
      case _ => error(s"TypeError: evaluating condition for illegal type: $c")
    }

  private def interpProj(t: Expr, i: Int, env: Env): Value =
    interp(t, env) match {
      case TupleV(vs) => vs.lift(i - 1) match {
        case Some(v) => v
        case None => error(s"RangeError: projecting on non existent index: $i")
      }

      case _ => error(s"TypeError: projecting on illegal type: $t")
    }

  private def interpCons(h: Expr, t: Expr, env: Env): Value =
    interp(t, env) match {
      case NilV => ConsV(interp(h, env), NilV)
      case v: ConsV => ConsV(interp(h, env), v)
      case _ => error(s"TypeError: making a list with non-list $t")
    }

  private def interpListOp(
    listOp: (Value, Value) => Value,
    nilOp: () => Value = () => error(s"TypeError: making a list operation on nil type")
  ): (Expr, Env) => Value =
    (l, env) => interp(l, env) match {
      case ConsV(h, t) => listOp(h, t)
      case NilV => nilOp()
      case _ => error(s"TypeError: making a list operation on illegal type: $l")
    }

  private val interpEmpty = interpListOp((_, _) => BooleanV(false), () => BooleanV(true))
  private val interpHead = interpListOp((h, _) => h)
  private val interpTail = interpListOp((_, t) => t)

  private def interpVal(x: String, e: Expr, b: Expr, env: Env): Value =
    interp(b, env + (x -> interp(e, env)))

  private def interpRecFuns(ds: List[FunDef], b: Expr, env: Env): Value = {
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

    interp(b, nenv)
  }

  private def interpApp(f: Expr, as: List[Expr], env: Env): Value =
    interp(f, env) match {
      case CloV(ps, b, fenv) =>
        val paramLen = ps.length
        val argsLen = as.length

        if(paramLen != argsLen)
          error(s"TypeError: function takes $paramLen parameters, but $argsLen arguments were given")
        else
          interp(b, fenv ++ ps.zip(as.map(v => interp(v, env))))

      case _ => error(s"TypeError: calling for illegal type: $f")
    }

  private def interpTest(e: Expr, t: Type, env: Env): Value =
    interp(e, env) match {
      case IntV(_) => BooleanV(t == IntT)
      case BooleanV(_) => BooleanV(t == BooleanT)
      case TupleV(_) => BooleanV(t == TupleT)
      case ConsV(_, _) | NilV => BooleanV(t == ListT)
      case CloV(_, _, _) => BooleanV(t == FunctionT)
    }

  def interp(e: Expr, env: Env): Value = e match {
    // Variables
    case Id(name) => interpId(name, env)

    // Primitives
    case IntE(n) => IntV(n)
    case BooleanE(b) => BooleanV(b)
    case TupleE(es: List[Expr]) => TupleV(es.map(v => interp(v, env)))
    case NilE => NilV
    case ConsE(h, t) => interpCons(h, t, env)
    case Fun(ps, b) => CloV(ps, b, env)
    case RecFuns(ds: List[FunDef], b: Expr) => interpRecFuns(ds, b, env)

    // Operations
    case Add(l, r) => interpIntAdd(l, r, env)
    case Mul(l, r) => interpIntMul(l, r, env)
    case Div(l, r) => interpIntDiv(l, r, env)
    case Mod(l, r) => interpIntMod(l, r, env)
    case Eq(l, r) => interpIntEq(l, r, env)
    case Lt(l, r) => interpIntLt(l, r, env)
    case If(c, t, f) => interpIf(c, t, f, env)
    case Proj(t, i) => interpProj(t, i, env)
    case Empty(l) => interpEmpty(l, env)
    case Head(l) => interpHead(l, env)
    case Tail(l) => interpTail(l, env)
    case Val(x, e, b) => interpVal(x, e, b, env)
    case App(f, as) => interpApp(f, as, env)
    case Test(e, t) => interpTest(e, t, env)
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

    // test-local1
    test(run("""
      val x = 1 + 2;
      val y = x * 4 + 1;
      y / (x - 1)
    """), "6")
    // test-local2
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

    test(run("""
      def reduce(list, iterator, initial) =
        if(!list.isInstanceOf[List] || !iterator.isInstanceOf[Function])
          false
        else
          val next = iterator(initial, list.head);
          if(list.tail.isEmpty)
            next
          else
            reduce(list.tail, iterator, next);

      def factorial(n) =
        if(n <= 1)
          1
        else
          n * factorial(n - 1);

      def wrapFactorial(prev, n) =
        (prev, factorial(n));

      reduce(1 :: 2 :: 3 :: 4 :: 5 :: Nil, wrapFactorial, Nil)
    """), "(((((Nil, 1), 2), 6), 24), 120)")
  }
}
