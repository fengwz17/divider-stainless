package libraryUInt

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

@library
object bitLength {
  def apply(x: BigInt): BigInt = {
    require(x >= 0)
    decreases(x)
    val result = x match {
      case BigInt(0) => BigInt(0)
      case _ => bitLength(x / 2) + 1 
    }
    result
  } ensuring(res => res >= 0)
}

@library
object log2Ceil {
  def apply(x: BigInt): BigInt = {
    require(x > 0)
    bitLength(x - 1)
  }
}

@library
object Mux {
  def apply[T <: Bits](cond: Bool, con: T, alt: T): T = {
    if (cond.value) con else alt
  }
}

@opaque @library
object Cat {
  def apply(left: UInt, right: UInt): UInt = {
    val l = left
    val r = right
    UInt(
      (l.value * Pow2(r.width)) + r.value,
      l.width + r.width
    )
  } ensuring(res => res.value == left.value * Pow2(right.width) + right.value 
    && res.width == left.width + right.width)
  // `[T <: Bits]` then `List[T]` is not supported
  // `List[T]` in stainless lib is not covariant
  def apply(ls: List[UInt]): UInt = {
    ls.tail.foldLeft(ls.head) { case (res, r) => Cat(res, r) }
  } ensuring(res => ls.size == 2 ==> (res.value == ls.head.value * Pow2(ls.tail.head.width) + ls.tail.head.value 
      && res.width == ls.head.width + ls.tail.head.width) 
      && ls.size > 2 ==> (res.value == ls.head.value * Pow2(Cat(ls.tail).width) + Cat(ls.tail).value 
      && res.width == ls.head.width + Cat(ls.tail).width))
  // ensuring(res => res.value == ls.foldLeft(BigInt(0)) { case (res, r) => res * Pow2(r.width) + r.value } && res.width == ls.foldLeft(BigInt(0)) { case (res, r) => res + r.width })
}

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

@library
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
    decreases(p)
    val result = p match {
      case BigInt(0) => BigInt(1)
      case _ => BigInt(2) * Pow2(p - 1)
    }
    result
  } ensuring(res => res > 0)

  // Pow2 lemmas
  @opaque @inlineOnce @library
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

  @opaque @inlineOnce @library
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

  @opaque @inlineOnce @library
  def Pow2MonotoneStrict(c: BigInt, b: BigInt): Unit = {
    require(0 <= b)
    require(b < c)
    {
      Pow2(c)         ==:| trivial |:
      Pow2(c - b + b) ==:| Pow2Mul(c, c - b, b) |:
      Pow2(b) * Pow2(c - b)
    }.qed
    assert(c - b > 0)
    assert(Pow2(c - b) > 1)
    assert(Pow2(c) > Pow2(b))
  }.ensuring(_ => Pow2(c) > Pow2(b))

  @opaque @inlineOnce @library
  def Pow2BitLength(x: BigInt): Unit = {
    require(x >= 0)
    decreases(x)
    x match {
      case BigInt(0) => ()
      case _ => {
        {
          Pow2(bitLength(x))          ==:| trivial |:
          Pow2(bitLength(x / 2) + 1)  ==:| trivial |:
          2 * Pow2(bitLength(x / 2)) 
        }.qed
        Pow2BitLength(x / 2) 
        assert(Pow2(bitLength(x / 2)) >= x / 2 + 1)
        assert(2 * Pow2(bitLength(x / 2)) >= 2 * (x / 2) + 2)
        assert(2 * (x / 2) + 2 >= x + 1)
        assert(Pow2(bitLength(x)) >= x + 1)
        assert(Pow2(bitLength(x)) > x)
      }
    }
  }.ensuring(_ => Pow2(bitLength(x)) > x)

  @opaque @inlineOnce @library
  def Pow2ModReduce(a: BigInt, x: BigInt, y: BigInt): Unit = {
      require(a >= 0)
      require(x >= 0 && y >= 0)
      require(x >= y)
      val h = a / Pow2(x) 
      val l = a % Pow2(x)
      val hl = l / Pow2(y)
      val ll = l % Pow2(y)
      assert(ll < Pow2(y))
      assert(ll == l - hl * Pow2(y))
      assert(l == a - h * Pow2(x))
      assert(ll == a - h * Pow2(x) - hl * Pow2(y))
      assert((Pow2(y) * (h * Pow2(x - y) + hl) + ll) / Pow2(y) == h * Pow2(x - y) + hl) 
      Pow2Mul(x, x - y, y)
      assert(h * Pow2(x) == h * Pow2(x - y) * Pow2(y))
      {
        a % Pow2(y)                                                             ==:| trivial |:
        a - a / Pow2(y) * Pow2(y)                                               ==:| trivial |:
        a - (h * Pow2(x) + hl * Pow2(y) + ll) / Pow2(y) * Pow2(y)               ==:| Pow2Mul(x, x - y, y) |:
        a - (h * Pow2(x - y) * Pow2(y) + hl * Pow2(y) + ll) / Pow2(y) * Pow2(y) ==:| trivial |:
        a - (Pow2(y) * (h * Pow2(x - y) + hl) + ll) / Pow2(y) * Pow2(y)         ==:| trivial |:
        a - (h * Pow2(x - y) + hl) * Pow2(y)                                    ==:| trivial |:
        a - (h * Pow2(x - y) * Pow2(y) + hl * Pow2(y))                          ==:| Pow2Mul(x, x - y, y) |:
        a - h * Pow2(x) - hl * Pow2(y)                                          ==:| trivial |:
        ll                                                                      ==:| trivial |:
        l % Pow2(y)                                                             ==:| trivial |:
        a % Pow2(x) % Pow2(y)                               
      }.qed 
  }.ensuring(a % Pow2(y) == a % Pow2(x) % Pow2(y))

  @opaque @inlineOnce @library
  def Pow2ModLowBits(t: BigInt, a: BigInt, pow2b: BigInt, c: BigInt): Unit = {
    require(c >= BigInt(0))
    require(a >= c)
    require(pow2b >= 0)
    // lemmaPow2lt(c, b)
    // require(pow2b < Pow2(c))
    require(t >= 0)
    assert(Pow2(a - c) >= 0)
    {
      ((Pow2(a - c) * Pow2(c) + pow2b)) / Pow2(c) ==:| trivial |:
      Pow2(a - c) + pow2b / Pow2(c)
    }.qed
    {
      (t * Pow2(a) + pow2b) % Pow2(c)                                                 ==:| trivial |:
      (t * Pow2(a) + pow2b) - (t * Pow2(a) + pow2b) / Pow2(c) * Pow2(c)                 ==:| Pow2Mul(a, a - c, c) |:
      (t * Pow2(a) + pow2b) - ((t * Pow2(a - c) * Pow2(c) + pow2b)) / Pow2(c) * Pow2(c) ==:| trivial |:
      (t * Pow2(a) + pow2b) - (t * Pow2(a - c) + pow2b / Pow2(c)) * Pow2(c)       ==:| trivial |:
      (t * Pow2(a) + pow2b) - t * Pow2(a - c) * Pow2(c) - pow2b / Pow2(c) * Pow2(c) ==:| Pow2Mul(a, a - c, c) |:
      (t * Pow2(a) + pow2b) - t * Pow2(a) - pow2b / Pow2(c) * Pow2(c)               ==:| trivial |:
      pow2b - pow2b / Pow2(c) * Pow2(c)                                             ==:| trivial |:
      pow2b % Pow2(c)
    }.qed
  }.ensuring((t * Pow2(a) + pow2b) % Pow2(c) == pow2b % Pow2(c))

}

@library
object Log2 {
  def apply(x: UInt): UInt = {
    val log2 = bitLength(x.value) - 1
    UInt(log2, bitLength(log2))
  }
}

@library
object when {
  def apply(x: Bool): Boolean = {
    x.value
  } ensuring(res => res == x.value)
}
