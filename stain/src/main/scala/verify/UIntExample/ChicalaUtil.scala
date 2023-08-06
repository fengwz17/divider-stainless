package UIntExample

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

object bitLength {
  def apply(x: BigInt): BigInt = {
    require(x >= 0)
    def f(base: BigInt, res: BigInt): BigInt = {
      require(base >= 0 && res >= 0)
      if (res > 0) {
        f(base + 1, res / 2) 
      } else {
        base
      }
    } ensuring(res => res >= 0)
    f(0, x)
  } ensuring(res => res >= 0)// && Pow2(res) > x)
}

object log2Ceil {
  def apply(x: BigInt): BigInt = {
    require(x > 0)
    bitLength(x - 1)
  }
}

object Mux {
  def apply[T <: Bits](cond: Bool, con: T, alt: T): T = {
    if (cond.value) con else alt
  }
}

// @opaque @library
// object Cat {
//   def apply(left: Bits, right: Bits): UInt = {
//     val l = left.asUInt
//     val r = right.asUInt
//     UInt(
//       (l.value * Pow2(r.width)) + r.value,
//       l.width + r.width
//     )
//   }
//   // `[T <: Bits]` then `List[T]` is not supported
//   // `List[T]` in stainless lib is not covariant
//   def apply(ls: List[UInt]): UInt = {
//     ls.tail.foldLeft(ls.head) { case (res, r) => Cat(res, r) }
//   }
// }

// @opaque @library
// object Fill {
//   def apply(times: BigInt, bool: Bool): UInt = {
//     require(times > 0)
//     def f(result: UInt, times: BigInt): UInt = {
//       if (times > 0)
//         f(Cat(result, bool), times - 1)
//       else
//         result
//     }
//     f(bool.asUInt, times - 1)
//   }
// }

// @opaque @library
// object MuxLookup {
//   def apply[T <: Bits](key: UInt, default: T, mapping: List[(UInt, T)]): T = {
//     mapping.foldLeft(default) { case (res, (k, v)) => Mux(k === key, v, res) }
//   }
// }

object Pow2 {
  // def apply(p: Int): BigInt = {
  //   // Only literal arguments are allowed for BigInt.
  //   // can't cast Int to BigInt
  //   def f(base: BigInt, p: Int): BigInt = {
  //     if (p > 0) {
  //       2 * f(base, p - 1)
  //     } else {
  //       base
  //     }
  //   }
  //   f(BigInt(1), p)
  // } ensuring(res => res > 0)

  def apply(p: BigInt): BigInt = {
    require(p >= 0)
    def f(base: BigInt, p: BigInt): BigInt = {
      require(base >= 1 && p >= 0)
      if (p > 0) {
        2 * f(base, p - 1)
      } else {
        base
      }
    } ensuring(res => res > 0)
    f(BigInt(1), p)
  } ensuring(res => res > 0)

  // Pow2 lemmas
  @opaque  @library
  def Pow2Mul(s: BigInt, x: BigInt, y: BigInt): Unit = {
    require(x >= 0)
    require(y >= 0)
    require(s == x + y)
    decreases(x)
    x match {
      case BigInt(0) => ()
      case _ => {
        Pow2(s)                           ==:| trivial |:
        Pow2(x + y)                       ==:| trivial |:
        BigInt(2) * Pow2(x - 1 + y)       ==:| Pow2Mul(x + y - 1, x - 1, y) |:
        BigInt(2) * Pow2(x - 1) * Pow2(y) ==:| trivial |:
        Pow2(x) * Pow2(y) 
      }.qed
    }
  }.ensuring(_ => Pow2(s) == Pow2(x) * Pow2(y))

  @opaque  @library
  def Pow2Monotone(c: BigInt, b: BigInt): Unit = {
    require(0 <= b)
    require(b <= c)
    {
      Pow2(c)         ==:| trivial |:
      Pow2(c - b + b) ==:| Pow2Mul(c, c - b, b) |:
      Pow2(b) * Pow2(c - b)
    }.qed
    assert(c - b >= 0)
    assert(Pow2(c - b) >= 1)
    assert(Pow2(c) >= Pow2(b))
  }.ensuring(_ => Pow2(c) >= Pow2(b))
}

// @dropVCs
// object Log2 {
//   def apply(x: UInt): UInt = {
//     val log2 = bitLength(x.value) - 1
//     UInt(log2, bitLength(log2))
//   }
// }

// object when {
//   def apply(x: Bool): Boolean = {
//     x.value
//   }
// }
