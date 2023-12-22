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
    // require(start <= until)
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
    // require(ns.size > 0)
    def f(n: BigInt, ns: List[BigInt]): BigInt = {
      // require(ns.size >= 0)
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
    // require(l <= r)
    def f(res: List[BigInt], i: BigInt): List[BigInt] = {
      if (l <= i) f(i :: res, i - 1)
      else res
    }
    f(Nil[BigInt](), r - 1)
  }
}

@opaque @library
object << {
  def apply(a: BigInt, b: BigInt): BigInt = {
    // require(b >= 0)
    if (b == 0) a else a * Pow2(b)
  }
}

// @library
// def Sum(l: List[Boolean]): BigInt = {
//   l match {
//     case Cons(h, t) => {
//       h match {
//         case true => BigInt(1) + Sum(t)
//         case false => BigInt(0) + Sum(t)
//       }
//     }
//     case Nil() => BigInt(0)
//   }
// } ensuring(res => res >= 0)

// @library
// def SumZ(l: List[BigInt]): BigInt = {
//   require(l.forall(_ >= BigInt(0)))
//   l match {
//     case Cons(h, t) => {
//       h + SumZ(t)
//     }
//     case Nil() => BigInt(0)
//   }
// } ensuring(res => res >= 0)

// // proof needs to be finished
// @library
// def lemma_Sum_take(l: List[Boolean], l1: List[Boolean], l2: List[Boolean]): Unit = {
//   require(l == l1 ++ l2)
// }.ensuring(_ => Sum(l) == Sum(l1) + Sum(l2))

// // proof needs to be finished
// @library
// def lemma_take(l: List[Boolean], l1: List[Boolean], l2: List[Boolean]): Unit = {
// }.ensuring(_ => l == l1 ++ l2)

// // e.g. List = (a3 a2 a1 a0) = a3 -> a2 -> a1 -> a0, 
// // note that the head is the least significant bit
// // toZ(List) = a0 + 2 * a1 + 4 * a2 + 8 * a3
// @library
// def toZ(l: List[BigInt]): BigInt = {
//   decreases(l.size)
//   l match {
//     case Cons(h, t) => {
//       h + BigInt(2) * toZ(t)
//       }
//     case Nil() => BigInt(0)
//   }
// } ensuring(res => res >= 0)

// @library
// def lemma_toZ_append(l1: List[BigInt], l2: List[BigInt], last: BigInt): Unit = {
//   require(l1 != Nil())
//   require(l1 == l2 :+ last)
//   decreases(l2.size)
//   assert(l2.size >= BigInt(0))
//   // val x = Cons[BigInt](BigInt(10), Nil[BigInt]())
//   // assert(x.size == 1)
//   l2.size match {
//     case BigInt(0) => {
//       assert(l2 == Nil())
//       assert(l1 == Cons(last, Nil[BigInt]()))
//       toZ(l1) ==:| trivial |:
//       toZ(l2) + last ==:| trivial |:
//       toZ(l2) + Pow2(0) * last
//     }.qed
//     case BigInt(1) => {
//       toZ(l1)              ==:| trivial |:
//       toZ(l2 :+ last)      ==:| trivial |:
//       toZ(l2) + 2 * last   ==:| trivial |:
//       toZ(l2) + Pow2(1) * last 
//     }.qed
//     case n if n > 1 => {
//       assert(l2.size > 1)
//       assert(l2.tail.size >= 1)

//       toZ(l1) ==:| trivial |:
//       toZ(l2 :+ last)                               ==:| trivial |:
//       toZ((l2.head :: l2.tail) :+ last)             ==:| trivial |:
//       toZ(l2.head :: (l2.tail :+ last))             ==:| trivial |:
//       l2.head + BigInt(2) * toZ(l2.tail :+ last)                          ==:| {lemma_toZ_append(l2.tail :+ last, l2.tail, last)} |:
//       l2.head + BigInt(2) * (toZ(l2.tail) + Pow2(l2.tail.size) * last)    ==:| trivial |:
//       l2.head + BigInt(2) * toZ(l2.tail) + BigInt(2) * Pow2(l2.tail.size) * last  ==:| trivial |:
//       toZ(l2) + Pow2(l2.size)  * last
//     }.qed
//     case _ => ()
//   }
// }.ensuring(_ => toZ(l1) == toZ(l2) + Pow2(l2.size) * last)

// @library
// def getRows_head(l: List[List[Boolean]]): List[Boolean] = {
//   require(l != Nil())
//   val row_head: List[Boolean] = l.map(_ match {
//     case Cons(h, t) => h
//     case Nil() => false
//   })
//   row_head
// }
  
// @library
// def getRows_tail(l: List[List[Boolean]]): List[List[Boolean]] = {
//   require(l != Nil())
//   val row_tail: List[List[Boolean]] = l.map(_ match {
//     case Cons(h, t) => t
//     case Nil() => Nil()
//   })
//   row_tail
// }

// // e.g. List = (list_3 list_2 list_1 list_0)
// //  res = (toZ(list_3) :: toZ(list_2) :: toZ(list_1) :: toZ(list_0))
// //  post-condition 
// @library
// def ToZ_matrix(l: List[List[Boolean]]): List[BigInt] = {
//   decreases(l)
//   // require(l.forall(_.size == BigInt(2)))
//   // val l_row_head = getRows_head(l)
//   // val l_row_tail = getRows_tail(l)
//   val toZ_row = l match {
//     case Cons(h, t) => toZ(h.map(asBigInt(_))) :: ToZ_matrix(t)
//     case Nil() => Nil[BigInt]()
//   }
//   toZ_row
// } ensuring(res => res.forall(_ >= 0))

// // proof
// @library
// def lemmaListTailHead(l: List[List[Boolean]]): Unit = {
//   require(l.size >= 2)
// }.ensuring(_ => l.tail.head != Nil())

// // check
// @library
// def maxList(l: List[BigInt], max: BigInt): BigInt = {
//   require(max >= BigInt(0))
//   decreases(l.size)
//   l match {
//     case Cons(h, t) => {
//       if (h > max) maxList(t, h)
//       else maxList(t, max)
//     }
//     case Nil() => max
//   }
// } ensuring(res => res >= BigInt(0))