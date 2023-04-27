package verify

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import stainless.lang.Real

object TestExample {

  def Pow2(exp: BigInt): BigInt = {
      require(exp >= 0) 
      val result = exp match {
        case BigInt(0) => BigInt(1)
        case _ => 2 * Pow2(exp - 1)
      }
      result
  } ensuring(res => res > 0)

  @opaque @inlineOnce
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

  def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
    case true => y
    case _ => z
  } // ensuring(res => (x && (res == y)) || (!x && (res == z)))

  def Cat(a: BigInt, b: BigInt, len: BigInt): BigInt = {
    require(len >= 0 && a >= 0 && b >= 0)
    val result = len match {
      case zero if (len == 0) => a
      case _ => a * Pow2(len) + b
    }
    result
  } ensuring(res => res >= 0)

  def Extract(a: BigInt, index: BigInt): (BigInt, BigInt) = {
      require(a >= 0 && index >= 0) // && Pow2(index) > 0)
      // high = a(n - 1, index)
      // low = a(index - 1, 0)
      val high = a / Pow2(index)
      val low = a - high * Pow2(index)
      (high, low)
  } ensuring(res => a == res._1 * Pow2(index) + res._2 && 0 <= res._2 && res._2 < Pow2(index))

  @opaque @inlineOnce
  def fooWhilePropShiftRegRange(shiftReg: BigInt, cnt: BigInt, len: BigInt): Unit = {
      require(len >= BigInt(1))
      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(shiftReg >= 0)

      val hl = shiftReg / Pow2(len)
      val ll = shiftReg - hl * Pow2(len)
      {
        shiftReg / Pow2(cnt)                                        ==:| trivial |:
        (ll + Pow2(len) * hl) / Pow2(cnt)                           ==:| Pow2Mul(cnt, len - cnt) |:
        (ll + Pow2(cnt) * Pow2(len - cnt) * hl) / Pow2(cnt)         ==:| trivial |:
        Pow2(len - cnt) * hl + ll / Pow2(cnt)                       ==:| trivial |:
        shiftReg / Pow2(len) * Pow2(len - cnt) + ll / Pow2(cnt)        
      }.qed
  }.ensuring(_ => shiftReg / Pow2(cnt) >= shiftReg / Pow2(len) * Pow2(len - cnt))

  @opaque @inlineOnce 
  def fooWhilePropRshiftReg(a: BigInt, b: BigInt, len: BigInt, e:BigInt, cnt: BigInt, R: BigInt, shiftReg: BigInt): Unit = {
      require(len >= BigInt(1))
      require(a < Pow2(len) && a >= BigInt(0))
      require(b < Pow2(len) && b > BigInt(0))

      require(cnt >= BigInt(0) && cnt <= len - 1)
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
      
      // shiftReg / Pow2(cnt) >= shiftReg / Pow2(len) * Pow2(len - cnt)
      // h >= shiftReg / Pow2(len) * Pow2(len - cnt), shifteg / Pow2(len) >= b * e
      // h >= b * e * Pow2(len - cnt)
      fooWhilePropShiftRegRange(shiftReg, cnt, len)
      assert(h - b * e * Pow2(len - cnt) >= 0)

      cnt match {
        case cnt if cnt <= len => {
          shiftReg1 / Pow2(cnt + 1)                                                                             ==:| trivial |:
          (2 * shiftReg - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)                                            ==:| trivial |:
          (2 * (h * Pow2(cnt) + l) - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)                                 ==:| trivial |:
          (h * Pow2(cnt + 1) + 2 * l + e - b * e * Pow2(len + 1)) / Pow2(cnt + 1)                               ==:| Pow2Mul(len - cnt, cnt + 1) |:
          (h * Pow2(cnt + 1) + 2 * l + e - b * e * Pow2(len - cnt) * Pow2(cnt + 1)) / Pow2(cnt + 1)             ==:| trivial |:
          (Pow2(cnt + 1) * (h - b * e * Pow2(len - cnt)) + 2 * l + e) / Pow2(cnt + 1)                           ==:| {2 * l + e < Pow2(cnt + 1)} |:
          h - b * e * Pow2(len - cnt)                                                                           ==:| trivial |:
          (shiftReg / Pow2(cnt)) - b * e * Pow2(len - cnt)                                                      ==:| trivial |:
          R1 
        }.qed
      }      
  }.ensuring(_ => R - b * Pow2(len - cnt) * e == (2 * shiftReg - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)) 

  @opaque @inlineOnce 
  def fooWhilePropQshiftReg(len: BigInt, b: BigInt, e:BigInt, cnt: BigInt, R: BigInt, Q: BigInt, shiftReg: BigInt): Unit = {
      require(len >= BigInt(1))
      // require(a < Pow2(len) && a >= BigInt(0))
      require(b < Pow2(len) && b > BigInt(0))

      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(0 <= e && e <= 1)
      require(shiftReg >= 0)
      require(R >= 0)
      require(R == shiftReg / Pow2(cnt))
      require(shiftReg == Q + R * Pow2(cnt))

      cnt match {
        case cnt if cnt <= len - 1 => {
          2 * shiftReg - b * e * Pow2(len + 1) + e                 ==:| trivial |:
          2 * (R * Pow2(cnt) + Q) - b * e * Pow2(len + 1) + e      ==:| trivial |:
          2 * Q + e + R * Pow2(cnt + 1) - b * e * Pow2(len + 1)    ==:| Pow2Mul(cnt + 1, len - cnt) |:
          2 * Q + e + Pow2(cnt + 1) * (R - b * e * Pow2(len - cnt))        
        }.qed
      }      
  }.ensuring(_ => 2 * shiftReg - b * e * Pow2(len + 1) + e == (R - b * Pow2(len - cnt) * e) * Pow2(cnt + 1) + Q * 2 + e) 

  @opaque @inlineOnce 
  def fooWhileR(b: BigInt, len: BigInt, cnt: BigInt, e: BigInt, R: BigInt): Unit = {
      require(len >= BigInt(1))
      // require(a < Pow2(len) && a >= BigInt(0))
      require(b < Pow2(len) && b > BigInt(0))
      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(0 <= e && e <= 1)
      require(R >= 0)
      require(R == (R / 2) * 2)
      {
        ((R - b * Pow2(len - cnt) * e) / 2) * 2 ==:| trivial |:
        ((2 * (R / 2) - 2 * b * Pow2(len - cnt - 1) * e) / 2) * 2 ==:| trivial |:
        (R / 2 - b * Pow2(len - cnt - 1) * e) * 2 ==:| trivial |:
        (R / 2) * 2 - b * Pow2(len - cnt - 1) * e * 2 ==:| trivial |:
        R - b * Pow2(len - cnt) * e
      }.qed
  }.ensuring(R - b * Pow2(len - cnt) * e == ((R - b * Pow2(len - cnt) * e) / 2) * 2)

  @opaque @inlineOnce 
  def fooWhilePropabQR(a: BigInt, b: BigInt, len: BigInt, e:BigInt, cnt: BigInt, R: BigInt, Q: BigInt): Unit = {
      require(len >= BigInt(1))
      require(a < Pow2(len) && a >= BigInt(0))
      require(b < Pow2(len) && b > BigInt(0))

      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(0 <= e && e <= 1)
      require(R >= 0)
      require(2 * a == 2 * b * Q * Pow2(len - cnt) + R)
      
      val R1 = R - b * Pow2(len - cnt) * e
      val Q1 = 2 * Q + e
      val cnt1 = cnt + 1

      {
        2 * b * Q1 * Pow2(len - cnt1) + R1                                                  ==:| trivial |:
        2 * b * (2 * Q + e) * Pow2(len - cnt - 1) + (R - b * Pow2(len - cnt) * e)           ==:| trivial |:
        b * (2 * Q + e) * Pow2(len - cnt) + R - b * Pow2(len - cnt) * e                     ==:| trivial |:
        2 * b * Q * Pow2(len - cnt) + b * e * Pow2(len - cnt) + R - b * Pow2(len - cnt) * e ==:| trivial |:
        2 * b * Q * Pow2(len - cnt) + R                                                     ==:| trivial |:
        2 * a 
      }.qed
   }.ensuring(_ => 2 * b * (2 * Q + e) * Pow2(len - cnt - 1) + R - b * Pow2(len - cnt) * e == 2 * a)

  def fooWhile(a: BigInt, b: BigInt, len: BigInt, cnt: BigInt, R: BigInt, Q: BigInt, shiftReg: BigInt): (BigInt, BigInt, BigInt, BigInt) = {
      require(len >= BigInt(1))
      require(a < Pow2(len) && a >= BigInt(0))
      require(b < Pow2(len) && b > BigInt(0))

      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(shiftReg >= 0)
      require(R >= 0)
      require(R == shiftReg / Pow2(cnt))
      require(R == (R / 2) * 2)
      require(shiftReg == Q + R * Pow2(cnt))
      require(2 * a == 2 * b * Q * Pow2(len - cnt) + R)
      
      decreases(len + 1 - cnt)
      
      // val hi = shiftReg / Pow2(len)
      // val lo = shiftReg - hi * Pow2(len)
      val hi = Extract(shiftReg, len)._1
      val lo = Extract(shiftReg, len)._2

      val e = Mux(hi >= b, BigInt(1), BigInt(0))

      assert(shiftReg / Pow2(len) >= b * e)
      
      val R1 = R - b * Pow2(len - cnt) * e
      val Q1 = Q * 2 + e

      // val hi_tmp = Mux(hi >= b, hi - b, hi)
      val hi_tmp = hi - b * e
      val shiftReg_cat_tmp = lo * 2 + e 
      val shiftReg1 = hi_tmp * Pow2(len + 1) + shiftReg_cat_tmp
      val shiftReg_next = 2 * shiftReg - b * e * Pow2(len + 1) + e
      val cnt1 = cnt + BigInt(1)

      // prove the pre-condition of fooWhile

      // shiftReg_next == (hi - b * e) * Pow2(len + 1) + (lo * 2 + e)
      //               == hi * Pow2(len + 1) + lo * 2 + e - b * e * Pow2(len + 1)
      //               == 2 * (lo + hi * Pow2(len)) + e - b * e * Pow2(len + 1)
      //               == 2 * shiftReg - b * e * Pow2(len + 1) + e 
      //               == shiftReg1              
      assert(shiftReg1 == shiftReg_next)
     
      assert(R1 == R - b * Pow2(len - cnt) * e)
      assert(shiftReg1 == 2 * shiftReg - b * e * Pow2(len + 1) + e)
      assert(shiftReg1 >= 0)

      // R1 = shiftReg1 / Pow2(cnt1)
      fooWhilePropRshiftReg(a, b, len, e, cnt, R, shiftReg)
      assert(R1 == shiftReg1 / Pow2(cnt1))
      assert(R1 >= 0)

      // shiftReg == Q + R * Pow2(cnt)
      // shiftReg1 == Q1 + R1 * Pow2(cnt + 1)
      // 2 * shiftReg - b * e * Pow2(len + 1) + e == Q * 2 + e + (R - b * Pow2(len - cnt) * e) * Pow2(cnt + 1)
      // 2 * Q + R * Pow2(cnt + 1) - b * e * Pow2(len + 1) + e == Q * 2 + e + (R - b * Pow2(len - cnt) * e) * Pow2(cnt + 1)
      // fooWhilePropQshiftReg(len, b, e, cnt, R, Q, shiftReg)
      {
        shiftReg1                                                 ==:| trivial |:
        2 * shiftReg - b * e * Pow2(len + 1) + e                  ==:| fooWhilePropQshiftReg(len, b, e, cnt, R, Q, shiftReg) |:
        (R - b * Pow2(len - cnt) * e) * Pow2(cnt + 1) + Q * 2 + e ==:| trivial |:
        R1 * Pow2(cnt1) + Q1 
      }.qed
      assert(shiftReg1 == Q1 + R1 * Pow2(cnt1))

      // 2 * a == 2 * b * Q1 * Pow2(len - cnt1) + R1
      fooWhilePropabQR(a, b, len, e, cnt, R, Q)
      assert(2 * b * (2 * Q + e) * Pow2(len - cnt - 1) + R - b * Pow2(len - cnt) * e == 2 * a)
      assert(2 * a == 2 * b * Q1 * Pow2(len - cnt1) + R1)

      // R1 == (R1 / 2) * 2
      fooWhileR(b, len, cnt, e, R)
      assert(R1 == (R1 / 2) * 2)

      if (cnt1 <= len - 1) {
        fooWhile(a, b, len, cnt1, R1, Q1, shiftReg1)
      } else {
        (cnt1, R1, Q1, shiftReg1)
      }
      
  } ensuring(res => 0 <= res._1 && res._1 <= len && res._1 > len - 1 && res._4 >= 0 
      && res._2 == res._4 / Pow2(res._1) && res._4 == res._2 * Pow2(res._1) + res._3 && res._2 == (res._2 / 2) * 2
      && 2 * a == 2 * b * res._3 * Pow2(len - res._1) + res._2)

  def DividerFixedClock(len: BigInt, in1: BigInt, in2: BigInt): (BigInt, BigInt) = {  
    require(len >= 1)
    require(in1 < Pow2(len) && in1 >= 0)
    require(in2 < Pow2(len) && in2 > 0)

    var state = "s_compute"
    val a = in1 
    val b = in2

    var shiftReg = Cat(a, BigInt(0), 1)

    var cnt = BigInt(0)

    var R = 2 * a
    var Q = BigInt(0)
    
    val t: (BigInt, BigInt, BigInt, BigInt) = if (cnt <= len - 1) {
      fooWhile(a, b, len, cnt, R, Q, shiftReg)
    } else {
      (cnt, R, Q, shiftReg)
    }

    val hi = t._4 / Pow2(len)
    val lo = t._4 - hi * Pow2(len)
    val r = Extract(hi, 1)._1

    {
      r                             ==:| trivial |:
      Extract(hi, 1)._1             ==:| trivial |:
      hi / 2                        ==:| trivial |:
      (t._4 / Pow2(len)) / 2        ==:| trivial |:
      t._2 / 2                    
    }.qed

    {
      lo                            ==:| trivial |:
      t._4 - hi * Pow2(len)         ==:| trivial |:
      t._4 - t._2 * Pow2(len)       ==:| trivial |:
      t._3
    }.qed

    {
      2 * in1                      ==:| trivial |:
      2 * a                        ==:| trivial |:
      2 * b * t._3 + t._2          ==:| trivial |:
      2 * b * lo + t._2            ==:| trivial |:
      2 * b * lo + (t._2 / 2) * 2  ==:| trivial |:
      2 * b * lo + r * 2
    }.qed
    assert(in1 == b * lo + r)
        
    val resQ = lo
    val resR = r
    // println(resQ, resR)
    (resQ, resR)
  } ensuring(res => in1 == in2 * res._1 + res._2)
}