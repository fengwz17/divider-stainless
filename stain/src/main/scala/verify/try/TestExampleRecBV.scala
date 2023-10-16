package verify.`try`

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

case class TestExampleRecBV(len: Int = 4) {
 
  @library
  def Pow2(exp: BigInt): BigInt = {
      require(exp >= 0) 
      val result = exp match {
        case BigInt(0) => BigInt(1)
        case _ => 2 * Pow2(exp - 1)
      }
      result
  } ensuring(res => res > 0)

  @opaque @library
  def Pow2Mul(x: BigInt, y: BigInt): Unit = {
    require(x >= 0)
    require(y >= 0)
    decreases(x)
    x match {
      case BigInt(0) => ()
      case _ => {
        Pow2(x + y)                       ==:| trivial  |:
        BigInt(2) * Pow2(x - 1 + y)       ==:| Pow2Mul(x - 1, y)  |:
        BigInt(2) * Pow2(x - 1) * Pow2(y) ==:| trivial  |:
        Pow2(x) * Pow2(y) 
      }.qed
    }
  }.ensuring(_ => Pow2(x + y) == Pow2(x) * Pow2(y))

  def Mux(x: BigInt, y: BigInt, z: BigInt): BigInt = {
    require(x == BigInt(1) || x == BigInt(0))
    x match {
      case BigInt(1) => y
      case _ => z
    }
  }

  @opaque @inlineOnce
  def fooWhilePropShiftReg(shiftReg: BigInt, cnt: BigInt, len: BigInt): Unit = {
      require(len >= BigInt(1))
      require(cnt >= BigInt(0) && cnt <= len)
      require(shiftReg >= 0)
      val hc = shiftReg / Pow2(cnt)
      val lc = shiftReg - hc * Pow2(cnt)

      val hl = shiftReg / Pow2(len)
      val ll = shiftReg - hl * Pow2(len)
      {
        shiftReg / Pow2(cnt)                                ==:| trivial |:
        (ll + Pow2(len) * hl) / Pow2(cnt)                   ==:| Pow2Mul(cnt, len - cnt) |:
        (ll + Pow2(cnt) * Pow2(len - cnt) * hl) / Pow2(cnt) ==:| trivial |:
        Pow2(len - cnt) * hl + ll / Pow2(cnt)               ==:| trivial |:
        shiftReg / Pow2(len) * Pow2(len - cnt) + ll / Pow2(cnt)        
      }.qed
  }.ensuring(_ => shiftReg / Pow2(cnt) >= shiftReg / Pow2(len) * Pow2(len - cnt))

  @opaque @inlineOnce
  def fooWhileProp(a: BigInt, b: BigInt, len: BigInt, e:BigInt, cnt: BigInt, R: BigInt, shiftReg: BigInt): Unit = {
      require(len >= BigInt(1))
      require(a < Pow2(len) && a >= BigInt(0))
      require(b < Pow2(len) && b > BigInt(0))

      require(cnt >= BigInt(1) && cnt <= len)
      require(0 <= e && e <= 1)
      require(shiftReg >= 0)
      require(shiftReg / Pow2(len) >= b * e)
      require(R >= 0)
      require(R == shiftReg / Pow2(cnt))

      // val e = Mux(hi >= b, BigInt(1), BigInt(0))

      val R1 = R - b * Pow2(len - cnt) * e
      assert(R1 == shiftReg / Pow2(cnt) - b * Pow2(len - cnt) * e)

      val shiftReg1 = 2 * shiftReg - b * e * Pow2(len + 1) + e

      val cnt1 = cnt + BigInt(1)

      val h = shiftReg / Pow2(cnt)
      val l = shiftReg - h * Pow2(cnt)
      assert(shiftReg == h * Pow2(cnt) + l)
      assert(l <= Pow2(cnt) - 1)
      assert(2 * l + e < Pow2(cnt + 1))
      fooWhilePropShiftReg(shiftReg, cnt, len)
      assert(h - b * e * Pow2(len - cnt) >= 0)

      cnt match {
        case cnt if cnt <= len => {
          shiftReg1 / Pow2(cnt + 1)                                                   ==:| trivial |:
          (2 * shiftReg - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)                  ==:| trivial |:
          (2 * (h * Pow2(cnt) + l) - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)       ==:| trivial |:
          (2 * h * Pow2(cnt) + 2 * l - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)     ==:| Pow2Mul(cnt + 1, len - cnt) |:
          (Pow2(cnt + 1) * (h - b * e * Pow2(len - cnt)) + 2 * l + e) / Pow2(cnt + 1) ==:| {2 * l + e < Pow2(cnt + 1)} |:
          h - b * e * Pow2(len - cnt)                                                 ==:| trivial |:
          shiftReg / Pow2(cnt) - b * e * Pow2(len - cnt)                              ==:| trivial |:
          R1
        }.qed
      }      
  }.ensuring(_ => R - b * Pow2(len - cnt) * e == (2 * shiftReg - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)) 

  @library
  def fooWhile(a: BigInt, b: BigInt, len: BigInt, cnt: BigInt, R: BigInt, shiftReg: BigInt): (BigInt, BigInt, BigInt) = {
      require(len >= BigInt(1))
      require(a < Pow2(len) && a >= BigInt(0))
      require(b < Pow2(len) && b > BigInt(0))

      require(cnt >= BigInt(1) && cnt <= len)
      require(shiftReg >= 0)
      require(R >= 0)
      require(R == shiftReg / Pow2(cnt))
      decreases(len + 1 - cnt)
      
      val hi = shiftReg / Pow2(len)
      val lo = shiftReg - hi * Pow2(len)

      val e = if (hi >= b) BigInt(1) else BigInt(0)

      // assert(shiftReg / Pow2(len) >= b * e)

      // val shiftReg1 = Cat(Mux(e, hi - b, hi)(len - 1, 0), lo, e)     
      val R1 = R - b * Pow2(len - cnt) * e
      val shiftReg1 = 2 * shiftReg - b * e * Pow2(len + 1) + e

      val cnt1 = cnt + BigInt(1)
      assert(R1 == R - b * Pow2(len - cnt) * e)
      assert(shiftReg1 == 2 * shiftReg - b * e * Pow2(len + 1) + e)
      fooWhileProp(a, b, len, e, cnt, R, shiftReg)
      if (cnt1 <= len) {
        fooWhile(a, b, len, cnt1, R1, shiftReg1)
      } else {
        (cnt1, R1, shiftReg1)
      }
      
  } // ensuring(res => 0 <= res._1 && res._1 <= len + 1 && res._1 > len && res._2 == res._3 / Pow2(res._1)) // && res._3 == res._2 / Pow2(res._1))

  // @ignore
  // def foo(len: BigInt, a: BigInt, b: BigInt): (BigInt, BigInt) = {  
  //   require(len >= 1)
  //   require(a < Pow2(len) && a >= 0)
  //   require(b < Pow2(len) && b > 0)
  //   var cnt = BigInt(1)
  //   var R = a
  //   var Q = BigInt(0)
  //   var shiftReg = a * 2
  //   // var compare_shiftReg = a
  //   val t: (BigInt, BigInt, BigInt) = if (cnt <= len) {
  //     fooWhile(a, b, len, cnt, R, shiftReg)
  //   } else {
  //     (cnt, R, shiftReg)
  //   }
  //   assert(t._1 == len + 1)
  //   assert(t._2 == t._3 / Pow2(t._1))
  //   val hi = t._3 / Pow2(len)
  //   val resR = hi / 2
  //   val resQ = t._3 - hi * Pow2(len)
  //   // println(resQ, resR)
  //   (resQ, resR)
  // } // ensuring(res => res > 0)
}