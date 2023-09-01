import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import ammonite.ops._

// Rexp
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

case class RANGE(s: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp 

// Values
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val


// Convenience typing
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

// nullable
def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true

  case RECD(_, r1) => nullable(r1)
  case RANGE(_) => false
  case PLUS(r1) => nullable(r1)
  case OPTIONAL(_) => true
  case NTIMES(r1, i) => if (i == 0) true else nullable(r1)
}

// der
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))

  case RECD(_, r1) => der(c, r1)
  case RANGE(s) => if (s.contains(c)) ONE else ZERO 
  case PLUS(r1) => SEQ(der(c, r1), STAR(r1))
  case OPTIONAL(r1) => ALT(der(c, r1), ZERO)
  case NTIMES(r, i) => 
    if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
}

// Flatten
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}

// Env
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// Mkeps
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))

  case PLUS(r) => Stars(List(mkeps(r)))   // the first copy must match the empty string
  case OPTIONAL(r) => Right(Empty)
  case NTIMES(r, i) => Stars(List.fill(i)(mkeps(r)))
}

// Inj
def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))

  case (RANGE(_), Empty) => Chr(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), Left(v1)) => Left(inj(r, c, v1))
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
}

// Rectification functions
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

// Simp
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

// Lex
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList))

// Language specific code
val KEYWORD : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip" | "upto"
val OP : Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | ">=" | "<=" | ":=" | "&&" | "||"
val LET: Rexp = RANGE(('A' to 'Z').toSet ++ ('a' to 'z'))
val SYM : Rexp = LET | RANGE(Set('.', '_', '>', '<', '=', ';', ',', ':'))
val PARENS : Rexp = "(" | "{" | ")" | "}"
val SEMI : Rexp = ";"
val WHITESPACE : Rexp = PLUS(" ") | "\n" | "\t"
val DIGIT : Rexp = RANGE(('0' to '9').toSet)
val DIGIT1 : Rexp = RANGE(('1' to '9').toSet)
val STRING : Rexp = "\"" ~ (SYM | " " | "\\n" | DIGIT).% ~ "\""
val ID : Rexp = LET ~ (LET | "_" | DIGIT).%
val NUM : Rexp = "0" | (DIGIT1 ~ DIGIT.%)
val COMMENT : Rexp = "//" ~ (SYM | " " | DIGIT).% ~ "\n" 

val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("o" $ OP) | 
                  ("str" $ STRING) |
                  ("p" $ PARENS) |
                  ("s" $ SEMI) | 
                  ("w" $ WHITESPACE) | 
                  ("i" $ ID) | 
                  ("n" $ NUM) |
		  ("c" $ COMMENT)).%

// Token
abstract class Token extends Serializable 
case class T_KEYWORD(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_STRING(s: String) extends Token
case class T_PAREN(s: String) extends Token
case object T_SEMI extends Token
case class T_ID(s: String) extends Token
case class T_NUM(n: Int) extends Token

val token : PartialFunction[(String, String), Token] = {
  case ("k", s) => T_KEYWORD(s)
  case ("o", s) => T_OP(s)
  case ("str", s) => T_STRING(s)
  case ("p", s) => T_PAREN(s)
  case ("s", _) => T_SEMI
  case ("i", s) => T_ID(s)
  case ("n", s) => T_NUM(s.toInt)
}

// Tokenise
def tokenise(s: String) : List[Token] = 
  lexing_simp(WHILE_REGS, s).collect(token)

case class ~[+A, +B](_1: A, _2: B)
type IsSeq[A] = A => Seq[_]

abstract class Parser[I : IsSeq, T] {
  def parse(ts: I): Set[(T, I)]

  def parse_all(ts: I) : Set[T] =
    for ((head, tail) <- parse(ts); if tail.isEmpty) yield head
}

class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(sb: I) = 
    for ((head1, tail1) <- p.parse(sb); 
         (head2, tail2) <- q.parse(tail1)) yield (new ~(head1, head2), tail2)
}

class AltParser[I : IsSeq, T](p: => Parser[I, T], q: => Parser[I, T]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)   
}

class FunParser[I : IsSeq, T, S](p: => Parser[I, T], f: T => S) extends Parser[I, S] {
  def parse(sb: I) = 
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

// New parser that takes as input a list of tokens
case class TokenListParser(ts: List[Token]) extends Parser[List[Token], List[Token]] {
    def parse(tsb: List[Token]) = {
        val (prefix, suffix) = tsb.splitAt(ts.length)
        if (prefix == ts) Set((prefix, suffix)) else Set()
    }
}

// Implicit definitions to go from a token 
// or a list of tokens to a TokenListParser
implicit def token2parser(t: Token) = TokenListParser(List(t))
implicit def tokenList2parser(ts: List[Token]) = TokenListParser(ts)

implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def || (q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S] (f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

implicit def TokenOps(t: Token) = new {
    def || (q : => Parser[List[Token], List[Token]]) = new AltParser[List[Token], List[Token]](List(t), q)
    def || (qs : List[Token]) = new AltParser[List[Token], List[Token]](List(t), qs)
    def ==>[S] (f: => List[Token] => S) = new FunParser[List[Token], List[Token], S](List(t), f)
    def ~[S](q : => Parser[List[Token], S]) =
        new SeqParser[List[Token], List[Token], S](List(t), q)
    def ~ (qs : List[Token]) =
        new SeqParser[List[Token], List[Token], List[Token]](List(t), qs)
}

implicit def TokenListOps(ts: List[Token]) = new {
    def || (q : => Parser[List[Token], List[Token]]) = new AltParser[List[Token], List[Token]](ts, q)
    def || (qs : List[Token]) = new AltParser[List[Token], List[Token]](ts, qs)
    def ==>[S] (f: => List[Token] => S) = new FunParser[List[Token], List[Token], S](ts, f)
    def ~[S](q : => Parser[List[Token], S]) =
        new SeqParser[List[Token], List[Token], S](ts, q)
    def ~ (qs : List[Token]) =
        new SeqParser[List[Token], List[Token], List[Token]](ts, qs)
}

// Abstract Syntax Trees
abstract class Stmt
abstract class AExp
abstract class BExp

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class For(id: String, a: AExp, u: AExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Read(s: String) extends Stmt
case class WriteId(s: String) extends Stmt  // for printing values of variables
case class WriteString(s: String) extends Stmt  // for printing words

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp

case class IdParser() extends Parser[List[Token], String] {
    def parse(tsb: List[Token]) = tsb match {
        case T_ID(id) :: rest => Set((id, rest))
        case _ => Set()
    }
}

case class NumParser() extends Parser[List[Token], Int] {
    def parse(tsb: List[Token]) = tsb match {
        case T_NUM(n) :: rest => Set((n, rest))
        case _ => Set()
    }
}

case class StringParser() extends Parser[List[Token], String] {
    def parse(tsb: List[Token]) = tsb match {
        case T_STRING(s) :: rest => Set((s, rest))
        case _ => Set()
    }
}

// WHILE Language Parsing
{
lazy val AExp: Parser[List[Token], AExp] = 
  (Te ~ T_OP("+") ~ AExp) ==> { case x ~ _ ~ z => Aop("+", x, z): AExp } ||
  (Te ~ T_OP("-") ~ AExp) ==> { case x ~ _ ~ z => Aop("-", x, z): AExp } || Te
lazy val Te: Parser[List[Token], AExp] = 
  (Fa ~ T_OP("*") ~ Te) ==> { case x ~ _ ~ z => Aop("*", x, z): AExp } || 
  (Fa ~ T_OP("/") ~ Te) ==> { case x ~ _ ~ z => Aop("/", x, z): AExp } || 
  (Fa ~ T_OP("%") ~ Te) ==> { case x ~ _ ~ z => Aop("%", x, z): AExp } || Fa  
lazy val Fa: Parser[List[Token], AExp] = 
   (T_PAREN("(") ~ AExp ~ T_PAREN(")")) ==> { case _ ~ y ~ _ => y } || 
   IdParser() ==> Var || 
   NumParser() ==> Num

lazy val BExp: Parser[List[Token], BExp] = 
   (AExp ~ T_OP("==") ~ AExp) ==> { case x ~ _ ~ z => Bop("==", x, z): BExp } || 
   (AExp ~ T_OP("!=") ~ AExp) ==> { case x ~ _ ~ z => Bop("!=", x, z): BExp } || 
   (AExp ~ T_OP("<") ~ AExp) ==> { case x ~ _ ~ z => Bop("<", x, z): BExp } || 
   (AExp ~ T_OP(">") ~ AExp) ==> { case x ~ _ ~ z => Bop(">", x, z): BExp } ||
   (AExp ~ T_OP(">=") ~ AExp) ==> { case x ~ _ ~ z => Bop(">=", x, z) } ||
   (AExp ~ T_OP("<=") ~ AExp) ==> { case x ~ _ ~ z => Bop("<=", x, z) } ||
   (T_PAREN("(") ~ BExp ~ List(T_PAREN(")"), T_OP("&&")) ~ BExp) ==> { case _ ~ y ~ _ ~ v => And(y, v): BExp } ||
   (T_PAREN("(") ~ BExp ~ List(T_PAREN(")"), T_OP("||")) ~ BExp) ==> { case _ ~ y ~ _ ~ v => Or(y, v): BExp } ||
   (T_KEYWORD("true") ==> (_ => True: BExp )) || 
   (T_KEYWORD("false") ==> (_ => False: BExp )) ||
   (T_PAREN("(") ~ BExp ~ T_PAREN(")")) ==> { case _ ~ x ~ _ => x }

lazy val Stmt: Parser[List[Token], Stmt] =
    T_KEYWORD("skip") ==> (_ => Skip: Stmt) ||
    (IdParser() ~ T_OP(":=") ~ AExp) ==> { case id ~ _ ~ z => Assign(id, z): Stmt } ||
    (T_KEYWORD("if") ~ BExp ~ T_KEYWORD("then") ~ Block ~ T_KEYWORD("else") ~ Block) ==> { case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w): Stmt } ||
    (T_KEYWORD("while") ~ BExp ~ T_KEYWORD("do") ~ Block) ==> { case _ ~ y ~ _ ~ w => While(y, w) : Stmt } ||
    (T_KEYWORD("for") ~ IdParser() ~ T_OP(":=") ~ AExp ~ T_KEYWORD("upto") ~ AExp ~ T_KEYWORD("do") ~ Block) ==> { case _ ~ id ~ _ ~ a ~ _ ~ u ~ _ ~ bl => For(id, a, u, bl) : Stmt } ||
    (T_KEYWORD("read") ~ IdParser()) ==> { case _ ~ id => Read(id): Stmt} ||
    (T_KEYWORD("write") ~ IdParser()) ==> { case _ ~ id => WriteId(id): Stmt} ||
    (T_KEYWORD("write") ~ StringParser()) ==> { case _ ~ s => WriteString(s): Stmt}

lazy val Stmts: Parser[List[Token], Block] =
    (Stmt ~ T_SEMI ~ Stmts) ==> { case x ~ _ ~ z => x :: z : Block } ||
    (Stmt ==> (s => List(s) : Block))

lazy val Block: Parser[List[Token], Block] =
    (T_PAREN("{") ~ Stmts ~ T_PAREN("}")) ==> { case x ~ y ~ z => y} ||
    (Stmt ==> (s => List(s)))
}

//While(Bop("<=", y, n), (w;y:=y+1)) THIS IS THE ERROR, MORE SPECICIFALY Bop("<=", y, n)
///////////////////////////////////////////////////////////////////////////////////

// compiler headers needed for the JVM
// (contains methods for read and write)
val beginning = """
.class public XXX.XXX
.super java/lang/Object

.method public static write(I)V 
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    iload 0
    invokevirtual java/io/PrintStream/println(I)V 
    return 
.end method

.method public static writes(Ljava/lang/String;)V
    .limit stack 2
    .limit locals 1
    getstatic java/lang/System/out Ljava/io/PrintStream;
    aload 0
    invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
    return
.end method

.method public static read()I
    .limit locals 10
    .limit stack 10
    ldc 0
    istore 1 ; this will hold our final integer
Label1:
    getstatic java/lang/System/in Ljava/io/InputStream;
    invokevirtual java/io/InputStream/read()I
    istore 2
    iload 2
    ldc 13 ; the newline delimiter for Unix (Windows 13)
    isub
    ifeq Label2
    iload 2
    ldc 32 ; the space delimiter
    isub
    ifeq Label2
    iload 2
    ldc 48 ; we have our digit in ASCII , have to subtract it from 48
    isub
    ldc 10
    iload 1
    imul
    iadd
    istore 1
    goto Label1
Label2:
    ; when we come here we have our integer computed
    ; in local variable 1
    iload 1
    ireturn
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS

"""

val ending = """
; COMPILED CODE ENDS
   return

.end method
"""

// Compiler functions


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
}

// this allows us to write things like
// i"iadd" and l"Label"


// environments 
type Env = Map[String, Int]


def compile_op(op: String) = op match {
  case "+" => i"iadd"
  case "-" => i"isub"
  case "*" => i"imul"
  case "/" => i"idiv"
  case "%" => i"irem"
}

// arithmetic expression compilation
def compile_aexp(a: AExp, env : Env) : String = a match {
  case Num(i) => i"ldc $i"
  case Var(s) => i"iload ${env(s)} \t\t; $s"
  case Aop(op, a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ compile_op(op)
}

// boolean expression compilation
//  - the jump-label is for where to jump if the condition is not true
def compile_bexp(b: BExp, env : Env, jmp: String) : String = b match {
  case True => ""
  case False => i"goto $jmp"
  case Bop("==", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpne $jmp"
  case Bop("!=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpeq $jmp"
  case Bop("<", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpge $jmp" //Changed from if_icmpgt to if_icmpge
  case Bop(">", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmple $jmp"
  case Bop("<=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpgt $jmp"
  case Bop(">=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmplt $jmp"
}

{
def forLoopConstructor(index: Int, id: String, env: Env, a: AExp, u: AExp, bl: Block) : (String, Env) = {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env + (id -> index))
    val tempBop = Bop("<=", Var(id), u)
    (compile_aexp(a, env1) ++
     i"istore $index \t\t; $id" ++
     l"$loop_begin" ++
     compile_bexp(tempBop, env1, loop_end) ++
     instrs1 ++
     i"iload ${env1(id)} \t\t; $id" ++
     i"bipush 1" ++
     i"iadd" ++
     i"istore $index \t\t; $id" ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
}

// statement compilation
def compile_stmt(s: Stmt, env: Env) : (String, Env) = s match {
  case Skip => ("", env)
  case Assign(x, a) => {
    val index = env.getOrElse(x, env.keys.size)
    (compile_aexp(a, env) ++ i"istore $index \t\t; $x", env + (x -> index))
  } 
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
     instrs1 ++
     i"goto $if_end" ++
     l"$if_else" ++
     instrs2 ++
     l"$if_end", env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (l"$loop_begin" ++
     compile_bexp(b, env, loop_end) ++
     instrs1 ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
  }
  case For(id, a, u, bl) => {
    if (env.get(id) == None) {
      val index = env.keys.size
      val newId = id
      forLoopConstructor(index, newId, env, a, u, bl)
    }
    else {
      val index = env.keys.size + 1
      val newId = id + index.toString
      forLoopConstructor(index, newId, env, a, u, bl)
    }
  }
  case WriteId(x) => {
    //print(env)
    (i"iload ${env(x)} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/write(I)V", env)
  }
  case WriteString(x) => {
    (i"ldc ${x} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/writes(Ljava/lang/String;)V", env)
    }
  case Read(x) => {
   val index = env.getOrElse(x, env.keys.size) 
   (i"invokestatic XXX/XXX/read()I" ++ 
    i"istore $index \t\t; $x", env + (x -> index))
  }
}

// compilation of a block (i.e. list of instructions)
def compile_block(bl: Block, env: Env) : (String, Env) = bl match {
  case Nil => ("", env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}

// main compilation function for blocks
def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions ++ ending).replaceAllLiterally("XXX", class_name)
}

def compile_to_file(bl: Block, class_name: String) : Unit = {
  println(s"Start of compilation")
  write.over(pwd / s"$class_name.j", compile(bl, class_name))  
  println(s"generated $class_name.j file")
  os.proc("java", "-jar", "jasmin.jar", s"$class_name.j").call()
  println(s"generated $class_name.class file ")
}
}

val fib = """
write "Fib: ";
read n;
minus1 := 1;
minus2 := 0;
while n > 0 do {
  temp := minus2;
  minus2 := minus1 + minus2;
  minus1 := temp;
  n := n - 1
};
write "Result: ";
write minus2 ;
write "\n"
"""

// println(compile(Stmts.parse_all(tokenise(fib)).head, "fib"))
compile_to_file(Stmts.parse_all(tokenise(fib)).head, "fib")

val factor = """
write "Input n please";
read n;
write "The factors of n are:\n";
i := 1;
while i != ((n/2) + 1) do {
  if (n % i == 0) then { write i } else { skip };
  i := i + 1
}
"""

// println(compile(Stmts.parse_all(tokenise(factor)).head, "factor"))
compile_to_file(Stmts.parse_all(tokenise(factor)).head, "factor")

val testProg = """
for i := 2 upto 4 do {
  write i
}
"""

// println(compile(Stmts.parse_all(tokenise(testProg)).head, "for"))
compile_to_file(Stmts.parse_all(tokenise(testProg)).head, "for")

val testProg2 = """
for i := 1 upto 10 do {
  for i := 1 upto 10 do {
    write i
  }
}
"""

// println(compile(Stmts.parse_all(tokenise(testProg2)).head, "for2"))
compile_to_file(Stmts.parse_all(tokenise(testProg2)).head, "for2")