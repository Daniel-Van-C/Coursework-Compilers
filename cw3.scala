// regular expressions including records
abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp
case class RANGE(s: Set[Char]) extends Rexp 
case class PLUS(r: Rexp) extends Rexp 
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
case class RECD(x: String, r: Rexp) extends Rexp
// records for extracting strings or tokens

// values  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Optional(v: Val) extends Val
case class Ntimes(vs: List[Val]) extends Val
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

def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case RECD(_, r1) => nullable(r1)
}

def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RANGE(x) =>
    if (x.isEmpty) ZERO
    else if (x.contains(c)) ONE else ZERO
  case PLUS(r1) => SEQ(der(c, r1), STAR(r1))
  case OPTIONAL(r1) => der(c, r1)
  case NTIMES(r, i) => if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
  case RECD(_, r1) => der(c, r1)
}

// extracts a string from a value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Optional(v) => flatten(v)
  case Rec(_, v) => flatten(v)
}

// extracts an environment from a value;
// used for tokenising a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Optional(v) => env(v)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// The injection and mkeps part of the lexer
//===========================================

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case PLUS(r) => Stars(List(mkeps(r)))
  case OPTIONAL(r) => Stars(Nil)
  case NTIMES(r, n) => Stars(List.fill(n)(mkeps(r)))
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

  case (RANGE(_), Empty) => Chr(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), v) => Stars(inj(r, c, v)::Nil)
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)

  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}

val KEYWORD : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip" 
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | "<=" | ">=" | ":=" | "&&" | "||"
val LETTER = RANGE(('a' to 'z').toSet ++ ('A' to 'Z').toSet)
val SYM = LETTER | "." | "_" | ">" | "<" | "=" | ";" | "," | """\""" | ":"
val WS = PLUS(" ") | "\n" | "\t"
val STRING = "\"" ~ PLUS(SYM | WS | RANGE(('0' to '9').toSet)) ~ "\"" 
val PAREN : Rexp = "(" | "{" | ")" | "}"
val SEMI : Rexp = ";"
val ID = LETTER ~ (LETTER | RANGE(('0' to '9').toSet) | "_").%
val NUM = CHAR('0') | (RANGE(('1' to '9').toSet) ~ (RANGE(('0' to '9').toSet)).%)
val COM = "//" ~ (SYM | " " | RANGE(('0' to '9').toSet)).% ~ "\n"

val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("op" $ OP) | 
                  ("w" $ WS) | 
                  ("str" $ STRING) |
                  ("p" $ PAREN) | 
                  ("s" $ SEMI) |
                  ("i" $ ID) |
                  ("n" $ NUM) |
                  ("c" $ COM)).%

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

def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification
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
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = 
  env(lex_simp(r, s.toList))


// The tokens for the WHILE language
abstract class Token 
case object T_SEMI extends Token
case class T_PAREN(s: String) extends Token
case class T_KWD(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_STR(s: String) extends Token
case class T_ID(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_COM(s: String) extends Token

val token : PartialFunction[(String, String), Token] = {
  case ("s", _) => T_SEMI
  case ("p", s) => T_PAREN(s)
  case ("k", s) => T_KWD(s)
  case ("op", s) => T_OP(s)
  case ("str", s) => T_STR(s)
  case ("i", s) => T_ID(s)
  case ("n", s) => T_NUM(s.toInt)
  //case ("c", s) => T_COM(s) #Comments are not tokenised.
}

// by using collect we filter out all unwanted tokens
def tokenise(s: String) : List[Token] = 
  lexing_simp(WHILE_REGS, s).collect(token)



case class ~[+A, +B](x: A, y: B)

// constraint for the input
type IsSeq[A] = A => Seq[_]


abstract class Parser[I : IsSeq, T]{
  def parse(in: I): Set[(T, I)]

  def parse_all(in: I) : Set[T] =
    for ((hd, tl) <- parse(in);
        if tl.isEmpty) yield hd
}

// parser combinators

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}

// atomic parser for (particular) strings
case class StrParser(s: String) extends Parser[String, String] {
  def parse(sb: String) = {
    val (prefix, suffix) = sb.splitAt(s.length)
    if (prefix == s) Set((prefix, suffix)) else Set()
  }
}

// atomic parser for identifiers (variable names)
case object IdParser extends Parser[String, String] {
  val reg = "[A-Za-z][A-Za-z,0-9]*".r
  def parse(sb: String) = reg.findPrefixOf(sb) match {
    case None => Set()
    case Some(s) => Set(sb.splitAt(s.length))
  }
}

// atomic parser for numbers (transformed into ints)
case object NumParser extends Parser[String, Int] {
  val reg = "[0-9]+".r
  def parse(sb: String) = reg.findPrefixOf(sb) match {
    case None => Set()
    case Some(s) => {
      val (hd, tl) = sb.splitAt(s.length)
      Set((hd.toInt, tl)) 
    }
  }
}

// the following string interpolation allows us to write 
// StrParser(_some_string_) more conveniently as 
//
// p"<_some_string_>" 

implicit def parser_interpolation(sc: StringContext) = new {
    def p(args: Any*) = StrParser(sc.s(args:_*))
}    

// more convenient syntax for parser combinators
implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}


// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp 

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(s: String) extends Stmt
case class Read(s: String) extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp

// arithmetic expressions
{
lazy val AExp: Parser[String, AExp] = 
  (Te ~ p"+" ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("+", x, z) } ||
  (Te ~ p"-" ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("-", x, z) } || Te
lazy val Te: Parser[String, AExp] = 
  (Fa ~ p"*" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("*", x, z) } || 
  (Fa ~ p"/" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("/", x, z) } ||
  (Fa ~ p"%" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("%", x, z) } || Fa  
lazy val Fa: Parser[String, AExp] = 
   (p"(" ~ AExp ~ p")").map{ case _ ~ y ~ _ => y } || 
   IdParser.map(Var) || 
   NumParser.map(Num)
}

// boolean expressions with some simple nesting
{
lazy val BExp: Parser[String, BExp] = 
   (AExp ~ p"==" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z) } || 
   (AExp ~ p"!=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z) } || 
   (AExp ~ p"<" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z) } || 
   (AExp ~ p">" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">", x, z) } ||
   (AExp ~ p">=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">=", x, z) } ||
   (AExp ~ p"<=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z) } ||
   (p"(" ~ BExp ~ p")" ~ p"&&" ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => And(y, v) } ||
   (p"(" ~ BExp ~ p")" ~ p"||" ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => Or(y, v) } ||
   (p"true".map[BExp]{ _ => True }) || 
   (p"false".map[BExp]{ _ => False }) ||
   (p"(" ~ BExp ~ p")").map[BExp]{ case _ ~ x ~ _ => x }
}

// a single statement
{
lazy val Stmt: Parser[String, Stmt] =
  ((p"skip".map[Stmt]{_ => Skip }) ||
   (IdParser ~ p":=" ~ AExp).map[Stmt]{ case x ~ _ ~ z => Assign(x, z) } ||
   (p"write" ~ IdParser).map[Stmt]{ case _ ~ y => Write(y) } ||
   (p"write(" ~ IdParser ~ p")").map[Stmt]{ case _ ~ y ~ _ => Write(y) } ||
   (p"""write"""" ~ IdParser ~ p""""""").map[Stmt]{ case _ ~ y ~ _ => Write(y) } ||
   (p"read" ~ IdParser).map[Stmt]{ case _ ~ y => Read(y) } ||
   (p"if" ~ BExp ~ p"then" ~ Block ~ p"else" ~ Block)
     .map[Stmt]{ case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
   (p"while" ~ BExp ~ p"do" ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ w => While(y, w) }
   )

// statements
lazy val Stmts: Parser[String, Block] =
  (Stmt ~ p";" ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[String, Block] =
  ((p"{" ~ Stmts ~ p"}").map{ case _ ~ y ~ _ => y } || 
   (Stmt.map(s => List(s))))
}


def tokenExtractor(t: Token) : String = t match {
  case T_SEMI => ";"
  case T_PAREN(s) => s
  case T_KWD(s) => {
    if (s == "while") "while("
    else if (s == "do") ")do"
    else s 
  }
  case T_OP(s) => s
  case T_STR(s) => s.replaceAll("\\s", "")
  case T_ID(s) => s
  case T_NUM(n) => n.toString
  case T_COM(s) => s
}

def tokenParser(tList: List[Token]) : Set[Block] = {
  val temp = tList.map(t => tokenExtractor(t))
  Stmts.parse_all(temp.mkString)
}


// an interpreter for the WHILE language
type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env) : Int = a match {
  case Num(i) => i
  case Var(s) => env(s)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)
}

def eval_bexp(b: BExp, env: Env) : Boolean = b match {
  case True => true
  case False => false
  case Bop("==", a1, a2) => eval_aexp(a1, env) == eval_aexp(a2, env)
  case Bop("!=", a1, a2) => !(eval_aexp(a1, env) == eval_aexp(a2, env))
  case Bop(">", a1, a2) => eval_aexp(a1, env) > eval_aexp(a2, env)
  case Bop("<", a1, a2) => eval_aexp(a1, env) < eval_aexp(a2, env)

  case Bop(">=", a1, a2) => eval_aexp(a1, env) >= eval_aexp(a2, env)
  case Bop("<=", a1, a2) => eval_aexp(a1, env) <= eval_aexp(a2, env)
  
  case And(b1, b2) => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Or(b1, b2) => eval_bexp(b1, env) || eval_bexp(b2, env)
}

{
def eval_stmt(s: Stmt, env: Env) : Env = s match {
  case Skip => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env) 
  case While(b, bl) => 
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case Write(x) => {
    try {println(env(x))}
    catch {case _: Throwable => println(x)}
    env
    }
  case Read(x) => env
}

def eval_bl(bl: Block, env: Env) : Env = bl match {
  case Nil => env
  case s::bl => eval_bl(bl, eval_stmt(s, env))
}
}

def eval(s: Set[Block], e: Env) : Env = {
  eval_bl(s.head, e)
}


tokenParser(tokenise("if (a < b) then skip else a := a * b + 1"))

val prog1 = """
write "Fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do {
  temp := minus2;
  minus2 := minus1 + minus2;
  minus1 := temp;
  n := n - 1
};
write "Result";
write minus2
"""

tokenParser(tokenise(prog1))
eval(tokenParser(tokenise(prog1)), Map("n" -> 10))

val prog2 = """
start := 1000; 
x := start;
y := start;
z := start;
while 0 < x do {
 while 0 < y do {
  while 0 < z do { z := z - 1 };
  z := start;
  y := y - 1
 };     
 y := start;
 x := x - 1
}
"""

tokenParser(tokenise(prog2))
eval(tokenParser(tokenise(prog2)), Map()) //This takes about a minute to run on my PC

val prog3 = """
// Find all factors of a given input number


write "Input n please";
read n;
write "The factors of n are";
f := 2;
while (f < n / 2 + 1) do {
  if ((n / f) * f == n) then  { write(f) } else { skip };
  f := f + 1
}
"""

tokenParser(tokenise(prog3))
eval(tokenParser(tokenise(prog3)), Map("n" -> 12))

val prog4 = """
// Collatz series
//
// needs writing of strings and numbers; comments

bnd := 1;
while bnd < 101 do {
  write bnd;
  write ": ";
  n := bnd;
  cnt := 0;

  while n > 1 do {
    write n;
    write ",";
    
    if n % 2 == 0 
    then n := n / 2 
    else n := 3 * n+1;

    cnt := cnt + 1
  };

  write " => ";
  write cnt;
  write "\n";
  bnd := bnd + 1
}
"""

//tokenParser(tokenise(prog4)) //Does not work