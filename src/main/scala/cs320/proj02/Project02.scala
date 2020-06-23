package cs320

import scala.util.parsing.combinator._

trait Project02 extends Homework with RegexParsers {
  // Expressions
  sealed trait Expr
  case class Id(name: String) extends Expr // variable
  case class IntE(value: Int) extends Expr // integer
  case class BooleanE(value: Boolean) extends Expr // boolean
  case class Add(left: Expr, right: Expr) extends Expr // addition
  case class Mul(left: Expr, right: Expr) extends Expr // multiplication
  case class Div(left: Expr, right: Expr) extends Expr // division
  case class Mod(left: Expr, right: Expr) extends Expr // modulo
  case class Eq(left: Expr, right: Expr) extends Expr // equal-to
  case class Lt(left: Expr, right: Expr) extends Expr // less-then
  case class If(condition: Expr, trueBranch: Expr, falseBranch: Expr) extends Expr // conditional
  case class TupleE(expressions: List[Expr]) extends Expr // tuple
  case class Proj(expression: Expr, index: Int) extends Expr // projection
  case object NilE extends Expr // nil
  case class ConsE(head: Expr, tail: Expr) extends Expr // cons
  case class Empty(expression: Expr) extends Expr // is-empty
  case class Head(expression: Expr) extends Expr // head
  case class Tail(expression: Expr) extends Expr // tail
  case class Val(name: String, expression: Expr, body: Expr) extends Expr // local variable
  case class Vcc(name: String, body: Expr) extends Expr // continuation binding
  case class Fun(parameters: List[String], body: Expr) extends Expr // anonymous function
  case class RecFuns(functions: List[FunDef], body: Expr) extends Expr // recursive function
  case class App(function: Expr, arguments: List[Expr]) extends Expr // function application
  case class Test(expression: Expr, typ: Type) extends Expr // type test
  case class Throw(expression: Expr) extends Expr // throwing exception
  case class Try(expression: Expr, handler: Expr) extends Expr // handle registration

  object Expr extends ParserObject(e)

  // Function definitions
  case class FunDef(name: String, parameters: List[String], body: Expr)

  object FunDef extends ParserObject(d)

  // Types
  sealed trait Type
  case object IntT extends Type
  case object BooleanT extends Type
  case object TupleT extends Type
  case object ListT extends Type
  case object FunctionT extends Type

  object Type extends ParserObject(t)

  // Values
  sealed trait Value {
    override def toString: String = this match {
      case IntV(n) => n.toString
      case BooleanV(b) => b.toString
      case TupleV(vs) => vs.mkString("(", ", ", ")")
      case NilV => "Nil"
      case ConsV(h, t) => s"($h :: $t)"
      case CloV(_, _, _) => "<function>"
      case ContV(_) => "<continuation>"
    }
  }
  case class IntV(value: Int) extends Value
  case class BooleanV(value: Boolean) extends Value
  case class TupleV(values: List[Value]) extends Value
  case object NilV extends Value
  case class ConsV(head: Value, tail: Value) extends Value
  case class CloV(parameters: List[String], body: Expr, var env: Env) extends Value
  case class ContV(continuation: Cont) extends Value

  // Environments
  type Env = Map[String, Value]
  type Cont = Value => Value
  type ECont = Option[Value => Value]

  def run(str: String): String =
    interp(Expr(str), Map(), x => x, None).toString
  // Interpreter
  def interp(expr: Expr, env: Env, k: Cont, ek: ECont): Value

  // Parsers
  abstract class ParserObject[T](parser: Parser[T]) {
    def apply(str: String): T = parseAll(parser, str).getOrElse(error(s"bad syntax: $str"))
  }
  private def wrapR[T](e: Parser[T]): Parser[T] = "(" ~> e <~ ")"
  private def wrapC[T](e: Parser[T]): Parser[T] = "{" ~> e <~ "}"
  private def wrapS[T](e: Parser[T]): Parser[T] = "[" ~> e <~ "]"
  private lazy val keywords = Set(
    "true", "false", "val", "vcc", "def", "Nil",
    "if", "else", "throw", "try", "catch", "return"
  )
  private lazy val n: Parser[Int] = "-?[0-9]+".r ^^ (_.toInt)
  private lazy val i: Parser[Int] = "_[1-9][0-9]*".r ^^ (_.tail.toInt)
  private lazy val b: Parser[Boolean] =
    "true" ^^^ true | "false" ^^^ false
  private lazy val x: Parser[String] =
    "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(!keywords(_))
  private lazy val e: Parser[Expr] =
    (x <~ "=>") ~ e ^^ { case p ~ b => Fun(List(p), BR(b)) } |
    (wrapR(repsep(x, ",")) <~ "=>") ~ e ^^ {
      case ps ~ b =>
        if (ps.distinct.length != ps.length)
          error(s"Duplicated parameters: ${ps.mkString(", ")}")
        Fun(ps, BR(b))
    } | e0
  private lazy val e0: Parser[Expr] =
    rep1sep(e1, "::") ^^ (_.reduceRight(ConsE))
  private lazy val e1: Parser[Expr] =
    rep1sep(e2, "||") ^^ (_.reduceLeft(Or))
  private lazy val e2: Parser[Expr] =
    rep1sep(e3, "&&") ^^ (_.reduceLeft(And))
  private lazy val e3: Parser[Expr] =
    e4 ~ rep(("==" | "!=" | "<=" | "<" | ">=" | ">") ~ e4) ^^ {
      case e ~ es => es.foldLeft(e){
        case (l, "==" ~ r) => Eq(l, r)
        case (l, "!=" ~ r) => Neq(l, r)
        case (l, "<"  ~ r) => Lt(l, r)
        case (l, "<=" ~ r) => Lte(l, r)
        case (l, ">"  ~ r) => Gt(l, r)
        case (l,   _  ~ r) => Gte(l, r)
      }
    }
  private lazy val e4: Parser[Expr] =
    e5 ~ rep(("+" | "-") ~ e5) ^^ { case e ~ es => es.foldLeft(e){
      case (l, "+" ~ r) => Add(l, r)
      case (l,  _  ~ r) => Sub(l, r)
    }}
  private lazy val e5: Parser[Expr] =
    e6 ~ rep(("*" | "/" | "%") ~ e6) ^^ { case e ~ es => es.foldLeft(e){
      case (l, "*" ~ r) => Mul(l, r)
      case (l, "/" ~ r) => Div(l, r)
      case (l,  _  ~ r) => Mod(l, r)
    }}
  private lazy val e6: Parser[Expr] =
    "-" ~> e6 ^^ Neg | "!" ~> e6 ^^ Not | e7
  private lazy val e7: Parser[Expr] =
    e8 ~ rep(
      wrapR(repsep(e, ",")) ^^ AppP |
      "." ~> i ^^ ProjP |
      "." ~> "isEmpty" ^^^ EmptyP |
      "." ~> "nonEmpty" ^^^ NonEmptyP |
      "." ~> "head" ^^^ HeadP |
      "." ~> "tail" ^^^ TailP |
      "." ~> "isInstanceOf" ~> wrapS(t) ^^ TestP
    ) ^^ { case e ~ es => es.foldLeft(e){
      case (f, AppP(as)) => App(f, as)
      case (t, ProjP(i)) => Proj(t, i)
      case (l, EmptyP) => Empty(l)
      case (l, NonEmptyP) => NonEmpty(l)
      case (l, HeadP) => Head(l)
      case (l, TailP) => Tail(l)
      case (e, TestP(t)) => Test(e, t)
    }}
  private lazy val e8: Parser[Expr] =
    x ^^ Id | n ^^ IntE | b ^^ BooleanE | "Nil" ^^^ NilE |
    wrapR(rep1sep(e, ",")) ^^ {
      case e :: Nil => e
      case es => TupleE(es)
    } |
    ("if" ~> wrapR(e)) ~ e ~ ("else" ~> e) ^^ { case c ~ t ~ f => If(c, t, f) } |
    "throw" ~> e ^^ Throw |
    "return" ~> e ^^ Return |
    ("try" ~> e <~ "catch") ~ e ^^ { case e ~ h => Try(e, h) } |
    ("val" ~> x <~ "=") ~ e ~ (";" ~> e) ^^ { case x ~ e ~ b => Val(x, e, b) } |
    ("vcc" ~> x) ~ (";" ~> e) ^^ { case x ~ b => Vcc(x, b) } |
    ("val" ~> wrapR((x <~ ",") ~ rep1sep(x, ",")) <~ "=") ~ e ~ (";" ~> e) ^^ {
      case x ~ xs ~ e ~ b =>
        val xs1 = x :: xs
        if (xs1.distinct.length != xs1.length)
          error(s"Duplicated variables: ${xs1.mkString(", ")}")
        TupleVal(x :: xs, e, b)
    } |
    rep1(d) ~ e ^^ {
      case ds ~ b =>
        val names = ds.map(_.name)
        if (names.distinct.length != names.length)
          error(s"Duplicated function names: ${names.mkString(", ")}")
        RecFuns(ds, b)
    } |
    wrapC(e)
  private lazy val d: Parser[FunDef] =
    ("def" ~> x) ~ wrapR(repsep(x, ",")) ~ ("=" ~> e <~ ";") ^^ {
      case n ~ ps ~ b =>
        if (ps.distinct.length != ps.length)
          error(s"Duplicated parameters: ${ps.mkString(", ")}")
        FunDef(n, ps, BR(b))
    }
  private lazy val t: Parser[Type] =
    "Int" ^^^ IntT |
    "Boolean" ^^^ BooleanT |
    "Tuple" ^^^ TupleT |
    "List" ^^^ ListT |
    "Function" ^^^ FunctionT
  private sealed trait E6P
  private case class AppP(as: List[Expr]) extends E6P
  private case class ProjP(i: Int) extends E6P
  private case object EmptyP extends E6P
  private case object NonEmptyP extends E6P
  private case object HeadP extends E6P
  private case object TailP extends E6P
  private case class TestP(t: Type) extends E6P

  // Desugaring
  private val T = BooleanE(true)
  private val F = BooleanE(false)
  private def Neg(e: Expr): Expr = Mul(e, IntE(-1))
  private def Not(e: Expr): Expr = If(e, F, T)
  private def Sub(l: Expr, r: Expr): Expr = Add(l, Neg(r))
  private def Neq(l: Expr, r: Expr): Expr = Not(Eq(l, r))
  private def Lte(l: Expr, r: Expr): Expr = {
    val lv, rv = fresh()
    Val(lv, l,
    Val(rv, r,
    Or(Eq(Id(lv), Id(rv)), Lt(Id(lv), Id(rv)))))
  }
  private def Gt(l: Expr, r: Expr): Expr = Not(Lte(l, r))
  private def Gte(l: Expr, r: Expr): Expr = Not(Lt(l, r))
  private def And(l: Expr, r: Expr): Expr = If(l, r, F)
  private def Or(l: Expr, r: Expr): Expr = If(l, T, r)
  private def NonEmpty(l: Expr): Expr = Not(Empty(l))
  private def TupleVal(xs: List[String], e: Expr, b: Expr): Expr = {
    require(xs.length > 1)
    val t = fresh()
    Val(t, e, xs.zipWithIndex.foldRight(b){
      case ((x, i), b) => Val(x, Proj(Id(t), i + 1), b)
    })
  }
  private def Return(e: Expr): Expr = App(Id("return"), List(e))
  private def BR(e: Expr): Expr = Vcc("return", e)
  private var id = -1
  private def fresh(): String = {
    id += 1
    s"$$x$id"
  }
}
