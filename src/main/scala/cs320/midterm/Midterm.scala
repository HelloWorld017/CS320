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

  object Expr extends ParserObject(eExpr)

  // Function definitions
  case class FunDef(n: String, ps: List[String], b: Expr)

  object FunDef extends ParserObject(eFunDef)

  // Values
  sealed trait Value {
    override def toString: String = this match {
      case IntV(n) => n.toString
      case BooleanV(b) => b.toString
      case CloV(_, _, _) => "<function>"
      case _ => "unknown"
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

  private lazy val keywords = Set("true", "false", "val", "new", "def", "if", "else", "class", "extends", "set")
  private lazy val n: Parser[Int] = "-?[0-9]+".r ^^ (_.toInt)
  private lazy val i: Parser[Int] = "_[1-9][0-9]*".r ^^ (_.tail.toInt)
  private lazy val b: Parser[Boolean] =
    "true" ^^^ true | "false" ^^^ false
  private lazy val x: Parser[String] =
    "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(!keywords(_))

  private lazy val eExpr: Parser[Expr] =
    (x <~ "=>") ~ eExpr ^^ { case p ~ b => Fun(List(p), b) } |
    ((wrapR(repsep(x, ",")) <~ "=>") ~ eExpr).withFilter{
      case ps ~ _ => ps.distinct.length == ps.length
    } ^^ { case ps ~ b => Fun(ps, b) } |
    eLogicalOr

  private lazy val eLogicalOr: Parser[Expr] =
    rep1sep(eLogicalAnd, "||") ^^ (_.reduceLeft(Or))

  private lazy val eLogicalAnd: Parser[Expr] =
    rep1sep(eComparator, "&&") ^^ (_.reduceLeft(And))

  private lazy val eComparator: Parser[Expr] =
    eAddSub ~ rep(("==" | "!=" | "<=" | "<" | ">=" | ">") ~ eAddSub) ^^ {
      case e ~ es => es.foldLeft(e){
        case (l, "==" ~ r) => Eq(l, r)
        case (l, "!=" ~ r) => Neq(l, r)
        case (l, "<"  ~ r) => Lt(l, r)
        case (l, "<=" ~ r) => Lte(l, r)
        case (l, ">"  ~ r) => Gt(l, r)
        case (l,   _  ~ r) => Gte(l, r)
      }
    }

  private lazy val eAddSub: Parser[Expr] =
    eMultDivMod ~ rep(("+" | "-") ~ eMultDivMod) ^^ { case e ~ es => es.foldLeft(e){
      case (l, "+" ~ r) => Add(l, r)
      case (l,  _  ~ r) => Sub(l, r)
    }}

  private lazy val eMultDivMod: Parser[Expr] =
    eBool ~ rep(("*" | "/" | "%") ~ eBool) ^^ { case e ~ es => es.foldLeft(e){
      case (l, "*" ~ r) => Mul(l, r)
      case (l, "/" ~ r) => Div(l, r)
      case (l,  _  ~ r) => Mod(l, r)
    }}

  private lazy val eBool: Parser[Expr] =
    "-" ~> eBool ^^ Neg | "!" ~> eBool ^^ Not | eApp

  private lazy val eApp: Parser[Expr] =
    eObjProto ~ rep(
      wrapR(repsep(eExpr, ",")) ^^ AppP
    ) ^^ { case e ~ es => es.foldLeft(e){
      case (f, AppP(as)) => App(f, as)
    }}

  private lazy val eAtom: Parser[Expr] =
    x ^^ Id | n ^^ IntE | b ^^ BooleanE |
    ("if" ~> wrapR(eExpr)) ~ eExpr ~ ("else" ~> eExpr) ^^ { case c ~ t ~ f => If(c, t, f) } |
    ("val" ~> x <~ "=") ~ eExpr ~ (";" ~> eExpr) ^^ { case x ~ e ~ b => Val(x, e, b) } |
    (rep1(eFunDef) ~ eExpr).withFilter{ case ds ~ _ =>
      val names = ds.map(_.n)
      names.distinct.length == names.length
    } ^^ { case ds ~ b => RecFuns(ds, b) } |
    wrapR(eExpr)

  private lazy val eFunDef: Parser[FunDef] =
    (("def" ~> x) ~ wrapR(repsep(x, ",")) ~ ("=" ~> eExpr <~ ";")).withFilter{
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
  // Parsers
  private lazy val eObjProto: Parser[Expr] =
    // "set" keyword: A temporal workaround for catastrophic backtracking
    "set" ~> eObjGet ~ ("=" ~> eExpr <~ ";") ~ eExpr ^^ {
      case ObjGet(obj, key) ~ value ~ body => ObjSet(obj, key, value, body)
      // case ProtoMethod(obj, key) ~ value ~ body => ObjSet(obj, key, value, body)
      case _ => error(s"SyntaxError: cannot set a value with prototype method expression.")
    } |
    eObjProtoAtom

  private lazy val eObjGet: Parser[Expr] =
    eObjProtoAtom2 ~ rep1(("." | "->") ~ x) ^^ {
      case obj ~ keys => keys.foldLeft(obj) {
        case (targetObj, "." ~ key) => ObjGet(targetObj, key)
        case (targetObj,  _  ~ key) => ProtoMethod(targetObj, key)
      }
    }

  private lazy val eObjProtoAtom: Parser[Expr] = eObjGet | eObjProtoAtom2

  private lazy val eObjProtoAtom2: Parser[Expr] =
    "{}" ^^^ ObjE |
    wrapC("extends" ~> wrapS(eExpr)) ^^ {
      case baseObj => ProtoE(baseObj)
    } |
    "class" ~> wrapS(eExpr) ^^ {
      case proto => ProtoClass(proto)
    } |
    eAtom

  // Object
  type FiberKey = String
  type FiberValue = Value
  type FiberObject = Map[FiberKey, FiberValue]
  type Addr = Int
  type ObjStore = Map[Addr, FiberObject]
  case object ObjE extends Expr
  case class ObjGet(obj: Expr, key: String) extends Expr // object get value
  case class ObjSet(obj: Expr, key: String, value: Expr, body: Expr) extends Expr // object set value
  case class ObjV(addr: Addr) extends Value {
    override def toString: String = s"<object $addr>"
  }

  // Prototype
  case class ValueE(value: Value) extends Expr
  case class ProtoE(baseObj: Expr) extends Expr // create object from prototype object
  case class ProtoClass(proto: Expr) extends Expr // create class
  case class ProtoMethod(obj: Expr, key: String) extends Expr // get class method

  // Interpreter
  def run(str: String): String = interp(Expr(str))._1.toString
  def interp(expr: Expr): (Value, ObjStore) = interp(expr, Map.empty, Map.empty)
  def interp(expr: Expr, env: Env, store: ObjStore): (Value, ObjStore)
}
