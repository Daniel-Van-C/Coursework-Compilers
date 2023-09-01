import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import ammonite.ops._

abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val

// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r1) => nullable(r1)
}

def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
}

// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}

// extracts an environment from a value;
// used for tokenise a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// The Injection Part of the lexer

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case _ => { println ("Injection error") ; sys.exit(-1) } 
}

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else { println ("Lexing Error") ; sys.exit(-1) }
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList))

// The Lexing Rules for the Fun Language
def PLUS(r: Rexp) = r ~ r.%

val SYM = "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" | "T" | "_"
val DIGIT = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
val ID = SYM ~ (SYM | DIGIT).% 
val NUM = PLUS(DIGIT)
val KEYWORD : Rexp = "if" | "then" | "else" | "write" | "def" | "val"
val SEMI: Rexp = ";"
val OP: Rexp = "=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
val WHITESPACE = PLUS(" " | "\n" | "\t" | "\r")
val RPAREN: Rexp = ")" | "}"
val LPAREN: Rexp = "(" | "{"
val COMMA: Rexp = ","

val CAPITAL: Rexp = "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z"

val ALL = SYM | CAPITAL | DIGIT | OP | " " | ":" | ";" | "\"" | "=" | "," | "(" | ")" | "."
val ALL2 = ALL | "\n"
val COMMENT = ("/*" ~ ALL2.% ~ "*/") | ("//" ~ ALL.% ~ "\n")

val COLON: Rexp = ":"
val TYPE: Rexp = "Int" | "Double" | "Void"
val GLOBALID: Rexp = CAPITAL ~ (SYM | DIGIT).%
val FNUM: Rexp = ("-" | "") ~ NUM ~ ("." | "") ~ (NUM).%
val ARGS: Rexp = """','""" | """'\n'""" | """'-'""" | """'>'""" 

val FUN_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("s" $ SEMI) | 
                  ("c" $ COMMA) |
                  ("l" $ COLON) |
                  ("t" $ TYPE) |   
                  ("g" $ GLOBALID) | 
                  ("f" $ FNUM) |            
                  ("a" $ ARGS) |                                                                                                                                      
                  ("pl" $ LPAREN) |
                  ("pr" $ RPAREN) |
                  ("w" $ (WHITESPACE | COMMENT))).%

// The tokens for the Fun language
abstract class Token extends Serializable 
case object T_SEMI extends Token
case object T_COMMA extends Token
case object T_COLON extends Token
case object T_LPAREN extends Token
case object T_RPAREN extends Token
case class T_ID(s: String) extends Token
case class T_GLOBAL(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_FNUM(n: Float) extends Token
case class T_ARGS(n: String) extends Token
case class T_KWD(s: String) extends Token
case class T_TYPE(s: String) extends Token

val token : PartialFunction[(String, String), Token] = {
  case ("k", s) => T_KWD(s)
  case ("i", s) => T_ID(s)
  case ("o", s) => T_OP(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("s", _) => T_SEMI
  case ("c", _) => T_COMMA
  case ("l", _) => T_COLON
  case ("t", s) => T_TYPE(s)
  case ("g", s) => T_GLOBAL(s)
  case ("f", s) => T_FNUM(s.toFloat)    
  case ("a", s) => T_ARGS(s)   
  case ("pl", _) => T_LPAREN
  case ("pr", _) => T_RPAREN
}

def tokenise(s: String) : List[Token] = {
  val tks = lexing_simp(FUN_REGS, s).collect(token)
  if (tks.length != 0) tks
  else { println (s"Tokenise Error") ; sys.exit(-1) }
}


// Parser combinators
//    type parameter I needs to be of Seq-type
//
abstract class Parser[I, T](implicit ev: I => Seq[_]) {
  def parse(ts: I): Set[(T, I)]

  def parse_single(ts: I) : T = 
    parse(ts).partition(_._2.isEmpty) match {
      case (good, _) if !good.isEmpty => {
        good.head._1}
      case (_, err) => { 
        println (s"Parse Error\n${err.minBy(_._2.length)}") ; sys.exit(-1) }
      }
}

// convenience for writing grammar rules
case class ~[+A, +B](_1: A, _2: B)

class SeqParser[I, T, S](p: => Parser[I, T], 
                         q: => Parser[I, S])(implicit ev: I => Seq[_]) extends Parser[I, ~[T, S]] {
  def parse(sb: I) = 
    for ((head1, tail1) <- p.parse(sb); 
         (head2, tail2) <- q.parse(tail1)) yield (new ~(head1, head2), tail2)
}

class AltParser[I, T](p: => Parser[I, T], 
                      q: => Parser[I, T])(implicit ev: I => Seq[_]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)   
}

class FunParser[I, T, S](p: => Parser[I, T], 
                         f: T => S)(implicit ev: I => Seq[_]) extends Parser[I, S] {
  def parse(sb: I) = 
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

// convenient combinators
implicit def ParserOps[I, T](p: Parser[I, T])(implicit ev: I => Seq[_]) = new {
  def || (q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S] (f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

def ListParser[I, T, S](p: => Parser[I, T], 
                        q: => Parser[I, S])(implicit ev: I => Seq[_]): Parser[I, List[T]] = {
  (p ~ q ~ ListParser(p, q)) ==> { case x ~ _ ~ z => x :: z : List[T] } ||
  (p ==> ((s) => List(s)))
}

case class TokParser(tok: Token) extends Parser[List[Token], Token] {
  def parse(ts: List[Token]) = ts match {
    case t::ts if (t == tok) => Set((t, ts)) 
    case _ => Set ()
  }
}

implicit def token2tparser(t: Token) = TokParser(t)

implicit def TokOps(t: Token) = new {
  def || (q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](t, q)
  def ==>[S] (f: => Token => S) = new FunParser[List[Token], Token, S](t, f)
  def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](t, q)
}

case object NumParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_NUM(n)::ts => Set((n, ts)) 
    case _ => Set ()
  }
}

case object IdParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_ID(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object TypeParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_TYPE(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object GlobalParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_GLOBAL(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object FNumParser extends Parser[List[Token], Float] {
  def parse(ts: List[Token]) = ts match {
    case T_FNUM(f)::ts => Set((f, ts)) 
    case _ => Set ()
  }
}

case object ArgsParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_ARGS(f)::ts => Set((f, ts)) 
    case _ => Set ()
  }
}

// Abstract syntax trees for the Fun language
abstract class Exp extends Serializable 
abstract class BExp extends Serializable 
abstract class Decl extends Serializable 

case class Def(name: String, args: List[(String, String)], ty: String, body: Exp) extends Decl
case class Main(e: Exp) extends Decl
case class Const(name: String , v: Int) extends Decl
case class FConst(name: String , x: Float) extends Decl

case class Call(name: String, args: List[Exp]) extends Exp
case class If(a: BExp, e1: Exp, e2: Exp) extends Exp
case class Write(e: Exp) extends Exp
case class Var(s: String) extends Exp
case class Num(i: Int) extends Exp                          // integer numbers
case class FNum(i: Float) extends Exp                       // floating numbers
case class ChConst(c: Int) extends Exp                      // char constants
case class Aop(o: String, a1: Exp, a2: Exp) extends Exp
case class Sequence(e1: Exp, e2: Exp) extends Exp
case class Bop(o: String, a1: Exp, a2: Exp) extends BExp

case class Func(f: String, e: Exp) extends Exp
case class Str(f: String) extends Exp

// Grammar Rules for the Fun language
// arithmetic expressions
{
lazy val Exp: Parser[List[Token], Exp] = 
  (T_KWD("if") ~ BExp ~ T_KWD("then") ~ Exp ~ T_KWD("else") ~ Exp) ==>
    { case _ ~ x ~ _ ~ y ~ _ ~ z => If(x, y, z): Exp } ||
  (ArgsParser) ==> { case a => Str(a) } ||
  (M ~ T_SEMI ~ Exp) ==> { case x ~ _ ~ y => Sequence(x, y): Exp } || M
lazy val M: Parser[List[Token], Exp] =
  (T_KWD("write") ~ L) ==> { case _ ~ y => Write(y): Exp } || L
lazy val L: Parser[List[Token], Exp] = 
  (T ~ T_OP("+") ~ Exp) ==> { case x ~ _ ~ z => Aop("+", x, z): Exp } ||
  (T ~ T_OP("-") ~ Exp) ==> { case x ~ _ ~ z => Aop("-", x, z): Exp } || T  
lazy val T: Parser[List[Token], Exp] = 
  (F ~ T_OP("*") ~ T) ==> { case x ~ _ ~ z => Aop("*", x, z): Exp } || 
  (F ~ T_OP("/") ~ T) ==> { case x ~ _ ~ z => Aop("/", x, z): Exp } || 
  (F ~ T_OP("%") ~ T) ==> { case x ~ _ ~ z => Aop("%", x, z): Exp } || F
lazy val F: Parser[List[Token], Exp] = 
  (IdParser ~ T_LPAREN ~ ListParser(Exp, T_COMMA) ~ T_RPAREN) ==> 
    { case x ~ _ ~ z ~ _ => Call(x, z): Exp } ||
  (IdParser ~ T_LPAREN ~ T_RPAREN) ==> 
    { case x ~ _ ~ _ => Call(x, List()): Exp } ||
  (T_LPAREN ~ Exp ~ T_RPAREN) ==> { case _ ~ y ~ _ => y: Exp } || 
  IdParser ==> { case x => Var(x): Exp } ||
  GlobalParser ==> { case x => Var(x): Exp } ||
  FNumParser ==> { case x => FNum(x): Exp } ||
  NumParser ==> { case x => Num(x): Exp } 

// boolean expressions
lazy val BExp: Parser[List[Token], BExp] = 
  (Exp ~ T_OP("==") ~ Exp) ==> { case x ~ _ ~ z => Bop("==", x, z): BExp } || 
  (Exp ~ T_OP("!=") ~ Exp) ==> { case x ~ _ ~ z => Bop("!=", x, z): BExp } || 
  (Exp ~ T_OP("<") ~ Exp)  ==> { case x ~ _ ~ z => Bop("<",  x, z): BExp } || 
  (Exp ~ T_OP(">") ~ Exp)  ==> { case x ~ _ ~ z => Bop("<",  z, x): BExp } || 
  (Exp ~ T_OP("<=") ~ Exp) ==> { case x ~ _ ~ z => Bop("<=", x, z): BExp } || 
  (Exp ~ T_OP("=>") ~ Exp) ==> { case x ~ _ ~ z => Bop("<=", z, x): BExp }  

lazy val Defn: Parser[List[Token], Decl] =
  (T_KWD("val") ~ GlobalParser ~ T_COLON ~ T_TYPE("Int") ~ T_OP("=") ~ NumParser) ==> { case _ ~ a ~ _ ~ b ~ _ ~ c => Const(a, c) : Decl } ||
  (T_KWD("val") ~ GlobalParser ~ T_COLON ~ T_TYPE("Double") ~ T_OP("=") ~ FNumParser) ==> { case _ ~ a ~ _ ~ b ~ _ ~ c => FConst(a, c) : Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN ~ T_RPAREN ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp) ==> //0 arguments
    { case _ ~ y ~ _ ~ _ ~ _ ~ x ~ _ ~ r => Def(y, List(), x, r): Decl} ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN ~ IdParser ~ T_COLON ~ TypeParser ~ T_RPAREN ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp) ==> //1 argument
    { case _ ~ y ~ _ ~ w1 ~ _ ~ w2 ~ _ ~ _ ~ x ~ _ ~ r => Def(y, List((w1, w2)), x, r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_RPAREN ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp) ==> //2 arguments
    { case _ ~ y ~ _ ~ w1 ~ _ ~ w2 ~ _ ~ w3 ~ _ ~ w4 ~ _ ~ _ ~ x ~ _ ~ r => Def(y, List((w1, w2), (w3, w4)), x, r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_RPAREN ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp) ==> //3 arguments
    { case _ ~ y ~ _ ~ w1 ~ _ ~ w2 ~ _ ~ w3 ~ _ ~ w4 ~ _ ~ w5 ~ _ ~ w6 ~ _ ~ _ ~ x ~ _ ~ r => Def(y, List((w1, w2), (w3, w4), (w5, w6)), x, r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_RPAREN ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp) ==> //4 arguments
    { case _ ~ y ~ _ ~ w1 ~ _ ~ w2 ~ _ ~ w3 ~ _ ~ w4 ~ _ ~ w5 ~ _ ~ w6 ~ _ ~ w7 ~ _ ~ w8 ~ _ ~ _ ~ x ~ _ ~ r => Def(y, List((w1, w2), (w3, w4), (w5, w6), (w7, w8)), x, r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_COMMA ~ IdParser ~ T_COLON ~ TypeParser ~ T_RPAREN ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp) ==> //5 arguments
    { case _ ~ y ~ _ ~ w1 ~ _ ~ w2 ~ _ ~ w3 ~ _ ~ w4 ~ _ ~ w5 ~ _ ~ w6 ~ _ ~ w7 ~ _ ~ w8 ~ _ ~ w9 ~ _ ~ w10 ~ _ ~ _ ~ x ~ _ ~ r => Def(y, List((w1, w2), (w3, w4), (w5, w6), (w7, w8), (w9, w10)), x, r): Decl }

lazy val Prog: Parser[List[Token], List[Decl]] =
  (Defn ~ T_SEMI ~ Prog) ==> { case x ~ _ ~ z => {
    x :: z : List[Decl]} } ||
  (Exp ==> ((s) => List(Main(s)) : List[Decl]))
}

// Reading tokens and Writing parse trees
def parse_tks(tks: List[Token]) : List[Decl] = 
  Prog.parse_single(tks)

def tokenise_file(fname: String) = {
  tokenise(os.read(os.pwd / fname))
}

def parse_file(fname: String) : Unit = {
  val tks = tokenise(os.read(os.pwd / fname))
  println(parse_tks(tks))
}

// tokenise_file("mand.fun")
// parse_file("mand.fun")



// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// Internal CPS language for FUN
abstract class KExp
abstract class KVal

type Ty = String
case class KVar(s: String , ty: Ty = "UNDEF") extends KVal
case class KNum(i: Int) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(o: String, vrs: List[KVal]) extends KVal
case class KWrite(v: KVal) extends KVal

case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal) extends KExp
val voidFun = List("skip", "new_line", "print_int", "print_space", "print_star", "print_char", "top", "all", "hanoi")

// def typ_val(v: KVal , ts: TyEnv) = {}
// def typ_exp(a: KExp , ts: TyEnv) = {}

// CPS translation from Exps to KExps using a continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  case Var(s) => k(KVar(s)) 
  case Num(i) => k(KNum(i))
  case Str(s) => k(KNum(s(1).toInt))
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => KLet(z, Kop(o, y1, y2), k(KVar(z)))))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => 
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))))
  }
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
          val z = Fresh("tmp")
          if (voidFun.contains(name)) KLet(z, KCall(name, vs), k(KVar(z, "void")))
          else KLet(z, KCall(name, vs), k(KVar(z)))
      }
      case e::es => {
        CPS(e)(y => aux(es, vs ::: List(y)))}
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))
  case Write(e) => {
    val z = Fresh("tmp")
    CPS(e)(y => KLet(z, KWrite(y), k(KVar(z))))
  }
}   

// initial continuation
def CPSi(e: Exp) = CPS(e)(KReturn)

// convenient string interpolations 
// for instructions, labels and methods
implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}

// mathematical and boolean operations
def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "/" => "sdiv i32 "
  case "%" => "srem i32 "
  case "==" => "icmp eq i32 "
  case "<=" => "icmp sle i32 "     // signed less or equal
  case "<"  => "icmp slt i32 "     // signed less than
  case "!=" => "icmp ne i32 "
}

def compile_dop(op: String) = op match {
case "+" => "fadd double "
case "*" => "fmul double "
case "-" => "fsub double "
case "==" => "fcmp oeq double "
case "!=" => "fcmp one double "
case " <=" => "fcmp ole double "
case "<" => "fcmp olt double "
}

// compile K values
def compile_val(v: KVal) : String = v match {
  case KNum(i) => s"$i"
  case KVar(s, ty) => s"%$s"
  case Kop(op, x1, x2) => 
    s"${compile_op(op)} ${compile_val(x1)}, ${compile_val(x2)}"
  case KCall(x1, args) => {
    if (voidFun.contains(x1)) {
      if (args.isEmpty) s"call void @$x1 ()"
      else s"call void @$x1 (${args.map(compile_val).mkString("i32 ", ", i32 ", "")})"}
    else {
      if (args.isEmpty) s"call i32 @$x1 ()"
      else s"call i32 @$x1 (${args.map(compile_val).mkString("i32 ", ", i32 ", "")})"}
    }
  case KWrite(x1) =>
    s"call i32 @printInt (i32 ${compile_val(x1)})"
}

// compile K expressions
def compile_exp(a: KExp) : String = a match {
  case KReturn(v) => {
    v match {
      case KVar(_, x) if (x == "void") => i"ret void"
      case KVar(a, _) if (a == "skip") => i"ret void"
      case _ => i"ret i32 ${compile_val(v)}"
      }
    }
  case KLet(x: String, v: KVal, e: KExp) => {
    v match {
      case KCall(x, _) if (voidFun.contains(x)) => i"${compile_val(v)}" ++ compile_exp(e)
      case _ => i"%$x = ${compile_val(v)}" ++ compile_exp(e)
      }
    }
  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1) ++
    l"\n$else_br" ++ 
    compile_exp(e2)
  }
}

// compile function for declarations and main
def compile_decl(d: Decl) : String = d match {
  case Def(name, args, "Int", body) => {
    m"define i32 @$name (${args.map({case (x,y) => x}).mkString("i32 %", ", i32 %", "")}) {" ++
    compile_exp(CPSi(body)) ++
    m"}\n"
  }
  case Def(name, args, "Double", body) => { 
    m"define double @$name (${args.map({case (x,y) => x}).mkString("i32 %", ", i32 %", "")}) {" ++
    compile_exp(CPSi(body)) ++
    m"}\n"
  }
  case Def(name, args, "Void", body) => {
    if (args.isEmpty) {
      m"define void @$name () {" ++
      compile_exp(CPSi(body)) ++
      m"}\n"
    }
    else {
      m"define void @$name (${args.map({case (x,y) => x}).mkString("i32 %", ", i32 %", "")}) {" ++
      compile_exp(CPSi(body)) ++
      m"}\n"
    }
  }
  case Const(name, v) => {
    val z = Fresh("tmp")
    m"@$name = global i32 $v" ++
    m"%$name = load i32, i32* @$name" ++
    m"\n"
  }
  case FConst(name, x) => {
    m"@$name = global double $x" ++
    m"\n"
  }
  case Main(body) => {
    m"define i32 @main() {" ++
    compile_exp(CPS(body)(_ => KReturn(KNum(0)))) ++
    m"}\n"
  }
}

val prelude = """
declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @skip() #0 {
  ret void
}

@.str = private constant [4 x i8] c"%d\0A\00"

define void @print_int(i32 %x) {
   %t0 = getelementptr [4 x i8], [4 x i8]* @.str, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

@.format = private constant [4 x i8] c"%c\0A\00"

define void @print_char(i32 %x) {
   %t0 = getelementptr [4 x i8], [4 x i8]* @.format, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}


"""

// main compiler functions
def compile(prog: List[Decl]) : String = 
  prelude ++ (prog.map(compile_decl).mkString)

def write(ast: List[Decl]) = {
    val code = compile(ast)
    print(code)
    os.write.over(os.pwd / ("test" ++ ".ll"), code)
}

def write_file(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    val code = compile(ast)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}



// These can take more than a couple of minutes to run
// write_file("fact.fun")
// write_file("sqr.fun")
// write_file("hanoi.fun")
// write_file("mand.fun") // Does not run
// write_file("mand2.fun") // Does not run
