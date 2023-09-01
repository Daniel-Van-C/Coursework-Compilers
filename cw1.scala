// regular expressions
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RANGE(c: Set[Char]) extends Rexp 
case class PLUS(r: Rexp) extends Rexp 
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
case class UPTO(r: Rexp, m: Int) extends Rexp 
case class FROM(r: Rexp, n: Int) extends Rexp 
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class NEGATION(r: Rexp) extends Rexp 
case class CFUN(f: Char => Boolean) extends Rexp

// the nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RANGE(_) => false
  case PLUS(_) => false
  case OPTIONAL(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case UPTO(r, m) => true
  case FROM(r, n) => if (n == 0) true else nullable(r)
  case BETWEEN(r, n, m) => if (n == 0) true else nullable(r)
  case NEGATION(r) => if (nullable(r)) false else true
  case CFUN(f) => false
}

// the derivative of a regular expression w.r.t. a character
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) =>
    if (c == d) ONE else ZERO
  case ALT(r1, r2) =>
    ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))
  case RANGE(x) =>
    if (x.isEmpty) ZERO
    else if (x.contains(c)) ONE else ZERO
  case PLUS(r1) =>
    SEQ(der(c, r1), STAR(r1))
  case OPTIONAL(r1) =>
    ALT(ONE, der(c, r1))
  case NTIMES(r, i) => 
    if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
  case UPTO(r, m) =>
    if (m == 0) ZERO else ALT(ONE, SEQ(der(c, r), UPTO(r, m - 1)))
  case FROM(r, n) =>
    if (n == 0) STAR(r) else SEQ(der(c, r), FROM(r, n - 1))
  case BETWEEN(r1, n, m) =>
    if (m == 0) ZERO
    else if (n == 0) der(c, UPTO(r1, m))
    else if (n == m) der(c, NTIMES(r1, n))
    else SEQ(der(c, r1), BETWEEN(r1, n - 1, m - 1))
  case NEGATION(r) =>
    SEQ(RANGE(('a' to 'z').toSet), NEGATION(der(c, r)))
  case CFUN(f) => 
    if (f(c)) CFUN(f)
    else ZERO
}

def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}

// the derivative w.r.t. a string (iterates der)
def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}

// the main matcher function
def matcher(r: Rexp, s: String) : Boolean = 
  nullable(ders(s.toList, r))

// one or zero
def OPT(r: Rexp) = ALT(r, ONE)


// def c(c: Char) : Boolean = 
//   true

// def r(c: Char) : Boolean = 
//   true

// def all(c: Char) : Boolean = c match {
//   case n: Char => true
//   case _ => false
// }


//val r = PLUS(PLUS(SEQ(CHAR('a'), SEQ(CHAR('a'), CHAR('a')))))
//val r = SEQ(BETWEEN(CHAR('a'), 19, 19), OPTIONAL(CHAR('a')))
//matcher(r, "")

val aList: List[String] = List("", "a", "aa", "aaa", "aaaaa", "aaaaaa")
val rList: List[Rexp] = List(
                            OPTIONAL(CHAR('a')),
                            NEGATION(CHAR('a')),
                            NTIMES(CHAR('a'), 3),
                            NTIMES(OPTIONAL(CHAR('a')), 3),
                            UPTO(CHAR('a'), 3),
                            UPTO(OPTIONAL(CHAR('a')), 3),
                            BETWEEN(CHAR('a'), 3, 5),
                            BETWEEN(OPTIONAL(CHAR('a')), 3, 5)
                            )

// for (r <- rList) {
//     for (a <- aList) {
//         println(r + "    " + a + "    " + matcher(r, a))
//     }
// }

val alphabet = ('a' to 'z').toSet
val lhs = RANGE(alphabet ++ ('0' to '9').toSet ++ Set('_', '.', '-'))
val mid = RANGE(alphabet ++ ('0' to '9').toSet ++ Set('.', '-'))
val rhs = RANGE(alphabet ++ Set('.'))
val full = SEQ(PLUS(lhs), SEQ(CHAR('@'), SEQ(PLUS(mid), SEQ(CHAR('.'), BETWEEN(rhs, 2, 6)))))

// print(ders("daniel.van_cuylenburg@kcl.ac.uk".toList, full))
// matcher(full, "daniel.van_cuylenburg@kcl.ac.uk")