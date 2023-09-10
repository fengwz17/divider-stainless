package libraryUInt

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

@opaque @library
object range {
  /* Range from start (inclusive) to until (exclusive) */
  def apply(start: BigInt, until: BigInt): List[BigInt] = {
    require(start <= until)
    decreases(until - start)
    if(until <= start) Nil[BigInt]() else Cons(start, range(start + 1, until))
  } ensuring{(res: List[BigInt]) => res.size == until - start }
}

@opaque @library
object max {
  def apply(a: BigInt, b: BigInt): BigInt = {
    if (a > b) a else b
  }
  def apply(ns: List[BigInt]): BigInt = {
    require(ns.size > 0)
    def f(n: BigInt, ns: List[BigInt]): BigInt = {
      require(ns.size >= 0)
      decreases(ns)
      ns match {
        case Cons(head, tail) => f(max(n, head), tail)
        case Nil()            => n
      }
    }
    f(ns.head, ns.tail)
  }
}

@opaque @library
object until {
  def apply(l: BigInt, r: BigInt): List[BigInt] = {
    require(l <= r)
    def f(res: List[BigInt], i: BigInt): List[BigInt] = {
      if (l <= i) f(i :: res, i - 1)
      else res
    }
    f(Nil[BigInt](), r - 1)
  }
}