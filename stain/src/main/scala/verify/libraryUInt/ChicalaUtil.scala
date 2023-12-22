package libraryUInt

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

@library
object bitLength {
  def apply(x: BigInt): BigInt = {
    // require(x >= 0)
    decreases(x)
    val result = x match {
      case BigInt(0) => BigInt(0)
      case _ => bitLength(x / 2) + 1 
    }
    result
  } ensuring(res => res >= 0)
}


/*
 * @example {{{
 * log2Ceil(1)  // returns 0
 * log2Ceil(2)  // returns 1
 * log2Ceil(3)  // returns 2
 * log2Ceil(4)  // returns 2
 * }}}
 */
@library
object log2Ceil {
  def apply(x: BigInt): BigInt = {
    // require(x > 0)
    if (x == 1) 0 else bitLength(x - 1)
  }
}

/*
 * @example {{{
 * log2Up(1)  // returns 1
 * log2Up(2)  // returns 1
 * log2Up(3)  // returns 2
 * log2Up(4)  // returns 2
 * }}}
 */
@library
object log2Up {
  def apply(x: BigInt): BigInt = {
    // require(x > 0)
    if (x == 1) 1 else bitLength(x - 1)
  }
}

/** Compute the log2 of a Scala integer, rounded down.
  *
  * Can be useful in computing the next-smallest power of two.
  *
  * @example {{{
  * log2Floor(1)  // returns 0
  * log2Floor(2)  // returns 1
  * log2Floor(3)  // returns 1
  * log2Floor(4)  // returns 2
  * }}}
  */
@library
object log2Floor {
  def apply(in: BigInt): BigInt = {
    // require(in > 0)
    if (in == 1) 0 else (log2Ceil(in) - (if (isPow2(in)) 0 else 1))
  }
}

/** Returns whether a Scala integer is a power of two.
  *
  * @example {{{
  * isPow2(1)  // returns true
  * isPow2(2)  // returns true
  * isPow2(3)  // returns false
  * isPow2(4)  // returns true
  * }}}
  */
@library
object isPow2 {
  def apply(in: BigInt): Boolean = {
    // require(in > 0)
    // stainless does not support bitwise '&' in BigInt
    // in > 0 && ((in & (in - BigInt(1))) == 0)
    if (in == 1) true else (Pow2(bitLength(in - 1)) == in)
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
  def apply(left: Bits, right: Bits): UInt = {
    val l = left.asUInt
    val r = right.asUInt
    UInt(
      (l.value * Pow2(r.width)) + r.value,
      l.width + r.width
    )
  } 
  // ensuring(res => res.value == left.value * Pow2(right.width) + right.value 
    // && res.width == left.width + right.width)
  // `[T <: Bits]` then `List[T]` is not supported
  // `List[T]` in stainless lib is not covariant
  def apply(ls: List[Bits]): UInt = {
    ls.tail.foldLeft(ls.head.asUInt) { case (res, r) => Cat(res, r) }
  } 
  // ensuring(res => ls.size == 2 ==> (res.value == ls.head.value * Pow2(ls.tail.head.width) + ls.tail.head.value 
  //    && res.width == ls.head.width + ls.tail.head.width) 
  //    && ls.size > 2 ==> (res.value == ls.head.value * Pow2(Cat(ls.tail).width) + Cat(ls.tail).value 
  //    && res.width == ls.head.width + Cat(ls.tail).width))
  // ensuring(res => res.value == ls.foldLeft(BigInt(0)) { case (res, r) => res * Pow2(r.width) + r.value } && res.width == ls.foldLeft(BigInt(0)) { case (res, r) => res + r.width })
}

@opaque @library
object Fill {
  def apply(times: BigInt, bool: Bool): UInt = {
    // require(times > 0)
    def f(result: UInt, times: BigInt): UInt = {
      if (times > 0)
        f(Cat(result, bool), times - 1)
      else
        result
    }
    f(bool.asUInt, times - 1)
  }
}

@opaque @library @ignore 
object MuxLookup {
  def apply[T <: Bits](key: UInt, default: T, mapping: List[(UInt, T)]): T = {
    mapping.foldLeft(default) { case (res, (k, v)) => Mux(k === key, v, res) }
  }
}

@library
object Pow2 {
  // def apply(p: Int): BigInt = {
  //   // Only literal arguments are allowed for BigInt.
  //   // can't cast Int to BigInt in stainless
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
    // require(p >= 0)
    decreases(p)
    val result = p match {
      case BigInt(0) => BigInt(1)
      case _ => BigInt(2) * Pow2(p - 1)
    }
    result
  } ensuring(res => res > 0 && res > p)

  // Pow2 lemmas
  @opaque @inlineOnce @library
  def Pow2Mul(s: BigInt, x: BigInt, y: BigInt): Unit = {
    // require(x >= 0)
    // require(y >= 0)
    // require(s == x + y)
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
    // require(0 <= b)
    // require(b <= c)
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
    // require(0 <= b)
    // require(b < c)
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
    // require(x >= 0)
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
      // require(a >= 0)
      // require(x >= 0 && y >= 0)
      // require(x >= y)
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
    // require(c >= BigInt(0))
    // require(a >= c)
    // require(pow2b >= 0)
    // lemmaPow2lt(c, b)
    // require(pow2b < Pow2(c))
    // require(t >= 0)
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

  // (a / Pow2(i - 1)) == (2 * a / Pow2(i))
  @opaque  @library
  def lemmaPow2div(i: BigInt, a: BigInt, len: BigInt): Unit = {
    // require(len >= 5)
    // require(i >= BigInt(2) && i < len && i % 2 == 0)
    // require(a >= 0 && a <= Pow2(len - 2) - 1)
    val x = a / Pow2(i - 1)
    val y = a - x * Pow2(i - 1)
    assert(y < Pow2(i - 1))
    {
      2 * a / Pow2(i)                           ==:| trivial |:
      2 * (y + x * Pow2(i - 1)) / Pow2(i)       ==:| trivial |:
      (2 * y + x * Pow2(i)) / Pow2(i)           ==:| {2 * y < Pow2(i)} |:
      x                                         ==:| trivial |:
      a / Pow2(i - 1)
    }.qed
  }.ensuring(a / Pow2(i - 1) == (2 * a / Pow2(i)))

  // a / Pow2(x) / Pow2(y)  == a / Pow2(x + y)
  @opaque  @library
  def lemmaPow2DivAdd(a: BigInt, x: BigInt, y: BigInt): Unit = {
    // require(x >= 0 && y >= 0)
    // require(a >= 0)
    val h = a / Pow2(x + y)
    val l = a - h * Pow2(x + y)
    assert(l < Pow2(x + y))
    {
      Pow2(x + y) ==:| Pow2Mul(x + y, x, y) |:
      Pow2(x) * Pow2(y)
    }.qed
    assert(l < Pow2(x) * Pow2(y))
    val lh = l / Pow2(x)
    val ll = l - lh * Pow2(x)
    assert(lh * Pow2(x) <= l)
    assert(lh < Pow2(y))
    assert(ll < Pow2(x))
    {
      a / Pow2(x) / Pow2(y)                                             ==:| trivial |:
      (l + h * Pow2(x + y)) / Pow2(x) / Pow2(y)                         ==:| Pow2Mul(x + y, x, y) |:
      (l + h * Pow2(x) * Pow2(y)) / Pow2(x) / Pow2(y)                   ==:| trivial |:
      (ll + lh * Pow2(x) + h * Pow2(x) * Pow2(y)) / Pow2(x) / Pow2(y)   ==:| trivial |:
      (lh + h * Pow2(y)) / Pow2(y)                                      ==:| trivial |:
      h                                                                 ==:| trivial |:
      a / Pow2(x + y)
    }.qed
  }.ensuring(a / Pow2(x) / Pow2(y) == a / Pow2(x + y))

   
  @library
  def lemma_Pow2ModZero(a: BigInt, i: BigInt, j: BigInt): Unit = {
    // require(a >= 0)
    // require(i >= 0)
    // require(j >= 0 && j <= i)
    {
      a * Pow2(i) % Pow2(j) ==:| trivial |:
      a * Pow2(i) - a * Pow2(i) / Pow2(j) * Pow2(j) ==:| trivial |:
      a * Pow2(i) - a * Pow2(j + i - j) / Pow2(j) * Pow2(j) ==:| Pow2Mul(i, j, i - j) |:
      a * Pow2(i) - a * Pow2(j) * Pow2(i - j) / Pow2(j) * Pow2(j) ==:| trivial |:
      a * Pow2(i) - a * Pow2(i - j) * Pow2(j) ==:| Pow2Mul(i, j, i - j) |:
      a * Pow2(i) - a * Pow2(i) ==:| trivial |:
      BigInt(0)
    }.qed
  }.ensuring(a * Pow2(i) % Pow2(j) == BigInt(0))
 
  @library
  def lemma_Pow2Modilj(a: BigInt, i: BigInt, j: BigInt): Unit = {
    // require(a >= 0)
    // require(i >= 0)
    // require(j >= 0 && j >= i)
    // require(a * Pow2(i) < Pow2(j))
    {
      a * Pow2(i) % Pow2(j) ==:| trivial |:
      a * Pow2(i) - a * Pow2(i) / Pow2(j) * Pow2(j) ==:| trivial |:
      a * Pow2(i) - BigInt(0) ==:| trivial |:
      a * Pow2(i)
    }.qed
  }.ensuring(a * Pow2(i) % Pow2(j) == a * Pow2(i))
}

@library
object Log2 {
  def apply(x: UInt): UInt = {
    val log2 = bitLength(x.value) - 1
    UInt(log2, bitLength(log2))
  }
  def apply(x: UInt, w: BigInt): UInt = {
    val log2 = bitLength(x.value) - 1
    UInt(log2, w)
  }
}

@library
object when {
  def apply(x: Bool): Boolean = {
    x.value
  } ensuring(res => res == x.value)
}
