package cs320

import scala.util.parsing.combinator._

trait Midterm extends Homework with RegexParsers {
  // Expressions
  sealed trait Expr
  case class Id(x: String) extends Expr // variable
  case class IntE(n: Int) extends Expr // integer
  case class BooleanE(b: Boolean) extends Expr // boolean
  case class Add(l: Expr, r: Expr) extends Expr // addition
  case class Mul(l: Expr, r: Expr) extends Expr // multiplication
  case class Div(l: Expr, r: Expr) extends Expr // division
  case class Mod(l: Expr, r: Expr) extends Expr // modulo
  case class Eq(l: Expr, r: Expr) extends Expr // equal-to
  case class Lt(l: Expr, r: Expr) extends Expr // less-then
  case class If(c: Expr, t: Expr, f: Expr) extends Expr // conditional
  case class Val(x: String, e: Expr, b: Expr) extends Expr // local variable
  case class Fun(ps: List[String], b: Expr) extends Expr // anonymous function
  case class RecFuns(ds: List[FunDef], b: Expr) extends Expr // recursive function
  case class App(f: Expr, as: List[Expr]) extends Expr // function application

  object Expr extends ParserObject(e)

  // Function definitions
  case class FunDef(n: String, ps: List[String], b: Expr)

  object FunDef extends ParserObject(d)

  // Values
  sealed trait Value {
    override def toString: String = this match {
      case IntV(n) => n.toString
      case BooleanV(b) => b.toString
      case CloV(_, _, _) => "<function>"
    }
  }
  case class IntV(n: Int) extends Value
  case class BooleanV(b: Boolean) extends Value
  case class CloV(ps: List[String], b: Expr, var env: Env) extends Value

  // Environments
  type Env = Map[String, Value]

  // Parsers
  abstract class ParserObject[T](parser: Parser[T]) {
    def apply(str: String): T = parseAll(parser, str).getOrElse(error(s"bad syntax: $str"))
  }
  private def wrapR[T](e: Parser[T]): Parser[T] = "(" ~> e <~ ")"
  private def wrapC[T](e: Parser[T]): Parser[T] = "{" ~> e <~ "}"
  private def wrapS[T](e: Parser[T]): Parser[T] = "[" ~> e <~ "]"
  private lazy val keywords = Set("true", "false", "val", "new", "def", "if", "else", "class")
  private lazy val n: Parser[Int] = "-?[0-9]+".r ^^ (_.toInt)
  private lazy val i: Parser[Int] = "_[1-9][0-9]*".r ^^ (_.tail.toInt)
  private lazy val b: Parser[Boolean] =
    "true" ^^^ true | "false" ^^^ false
  private lazy val x: Parser[String] =
    "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(!keywords(_))

  private lazy val e: Parser[Expr] =
    (x <~ "=>") ~ e ^^ { case p ~ b => Fun(List(p), b) } |
    ((wrapR(repsep(x, ",")) <~ "=>") ~ e).withFilter{
      case ps ~ _ => ps.distinct.length == ps.length
    } ^^ { case ps ~ b => Fun(ps, b) } | e0

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
      wrapR(repsep(e, ",")) ^^ AppP
    ) ^^ { case e ~ es => es.foldLeft(e){
      case (f, AppP(as)) => App(f, as)
    }}

  private lazy val e8: Parser[Expr] =
    x ^^ Id | n ^^ IntE | b ^^ BooleanE |
    ("if" ~> wrapR(e)) ~ e ~ ("else" ~> e) ^^ { case c ~ t ~ f => If(c, t, f) } |
    ("val" ~> x <~ "=") ~ e ~ (";" ~> e) ^^ { case x ~ e ~ b => Val(x, e, b) } |
    (("val" ~> wrapR((x <~ ",") ~ rep1sep(x, ",")) <~ "=") ~ e ~ (";" ~> e)).withFilter{
      case x ~ xs ~ e ~ b =>
        val xs1 = x :: xs
        xs1.distinct.length == xs1.length
    } |
    (rep1(d) ~ e).withFilter{ case ds ~ _ =>
      val names = ds.map(_.n)
      names.distinct.length == names.length
    } ^^ { case ds ~ b => RecFuns(ds, b) } |
    eObjProto |
    wrapC(e)

  private lazy val d: Parser[FunDef] =
    (("def" ~> x) ~ wrapR(repsep(x, ",")) ~ ("=" ~> e <~ ";")).withFilter{
      case _ ~ ps ~ _ => ps.distinct.length == ps.length
    } ^^ {
      case n ~ ps ~ b => FunDef(n, ps, b)
    }

  private case class AppP(as: List[Expr])

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
  private var id = -1
  private def fresh(): String = {
    id += 1
    s"$$x$id"
  }

  // ================== Midterm Code ==================
  private lazy val eObjProto = eObj | eProto

  // Object
  private lazy val eObj: Parser[Expr] =
    "{}" ^^^ ObjE |
    e ~ ("." ~> x <~ "=") ~ e ~ (";" ~> e) ^^ ObjSet |
    (e ~> "." <~ x) ^^ ObjGet

  type FiberKey = String
  type FiberValue = Value
  type FiberObject = Map[FiberKey, FiberValue]
  type Addr = Int
  type ObjStore = Map[Addr, FiberObject]
  case object ObjE extends Expr
  case class ObjGet(name: string) extends Expr // object get value
  case class ObjSet(name: string, value: Expr, expr: Expr) extends Expr // object set value
  case class ObjV(addr: Addr) extends Value {
    override def toString(_): String = "<object>"
  }

  // Prototype
  private lazy val eProto: Parser[Expr] =
    wrapR("new" ~> e) ^^ ProtoNew |
    "class" ~ wrapS(e ~> "," <~ e) ^^ ProtoClass |
    (e ~> "->" <~ e) ^^ ProtoMethod

  case class ProtoNew(obj: Expr) extends Expr // create object from class
  case class ProtoClass(const: Expr, proto: Expr) extends Expr // create class
  case class ProtoMethod(obj: Expr, name: string) extends Expr // get class method
  case class ClassV(constructor: Value, prototype: Value) extends Value {
    override def toString(_): String = "<class>"
  }

  // Interpreter
  def run(str: String): String = interp(Expr(str)).toString
  def interp(expr: Expr): Value = interp(expr, Map.empty, Map.empty)
  def interp(expr: Expr, env: Env, store: ObjStore): Value
}
