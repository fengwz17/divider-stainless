package verify

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import stainless.lang.Real

object TestExample {
  def main(args: Array[String]): Unit = {
    // foo(4, 10, 3)
  }

  def Pow2(exp: BigInt): BigInt = {
      require(exp >= 0) 
      val result = exp match {
        case BigInt(0) => BigInt(1)
        case _ => 2 * Pow2(exp - 1)
      }
      result
  } ensuring(res => res > 0)

  //  def RealPow2(exp: BigInt): Real = {
  //     require(exp >= 0) 
  //     val result = exp match {
  //       // case neg if (neg < 0) => 1
  //       // case 0 => 1
  //       // case 1 => result
  //       case zero if (zero == 0) => Real(1)
  //       case _ => Real(2) * RealPow2(exp - 1)
  //     }
  //     result
  // } ensuring(res => res > Real(0))

  // Pow2(x + y) = Pow2(x) * Pow2(y)
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

  // @opaque @inlineOnce
  // def Pow2MulBoolean(x: BigInt, y: BigInt): Boolean = {
  //   require(x >= 0)
  //   require(y >= 0)
  //   decreases(x)
  //   x match {
  //     case BigInt(0) => ()
  //     case _ => {
  //       Pow2(x + y)                       ==:| trivial  |:
  //       BigInt(2) * Pow2(x - 1 + y)       ==:| Pow2Mul(x - 1, y)  |:
  //       BigInt(2) * Pow2(x - 1) * Pow2(y) ==:| trivial  |:
  //       Pow2(x) * Pow2(y) 
  //     }.qed
  //   }
  //   Pow2(x + y) == Pow2(x) * Pow2(y)
  // }.ensuring(res => res == true)

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
      val low = a % Pow2(index)
      // val high = (a - low) / Pow2(index)
      val high = a / Pow2(index)
      (high, low)
  } ensuring(res => a == res._1 * Pow2(index) + res._2 && 0 <= res._2 && res._2 < Pow2(index))

  def foo(len: BigInt, a: BigInt, b: BigInt): (BigInt, BigInt) = {
    require(len >= 1)
    require(a < Pow2(len) && a >= 0)
    require(b < Pow2(len) && b > 0)
    var cnt = BigInt(0)
    var R = a
    var Q = BigInt(0)
    var shiftReg = a * 2
    // var compare_shiftReg = a
    
    (while (cnt < len) {
      decreases(len - cnt)
      Pow2Mul(cnt + 2, len - cnt - 1)
  
      val hi = shiftReg / Pow2(len)
      val lo = shiftReg - hi * Pow2(len)

      val e = Mux(hi >= b, BigInt(1), BigInt(0))

      assert(shiftReg / Pow2(len) >= b * e)

      R = R - b * Pow2(len - cnt - 1) * e
      Q = Q * 2 + e

      // shiftReg = ((hi - b * e) * Pow2(len + 1) + lo * 2 + e)
      // shiftReg = (shiftReg / Pow2(len) - b * e) * Pow2(len + 1) + 2 * (shiftReg - shiftReg / Pow2(len)) + e
      shiftReg = 2 * shiftReg - b * e * Pow2(len + 1) + e

      cnt = cnt + 1
    }) invariant (0 <= cnt && cnt <= len && shiftReg >= 0 && shiftReg / Pow2(cnt + 1) == R)
    
    val hi = shiftReg / Pow2(len)
    val resR = hi / 2
    val resQ = shiftReg - hi * Pow2(len)
    // println(resQ, resR)
    (resQ, resR)
  } // ensuring(res => res > 0)

  // def minitest(S: BigInt, b: BigInt, n: BigInt, cnt: BigInt): (BigInt, BigInt) = {
  //   require(n >= 1)
  //   require(S >= 0 && S < Pow2(2 * n + 1))
  //   require(b > 0 && b < Pow2(n))
  //   // require(e >= 0 && e <= 1)
  //   require(cnt >= 0 && cnt <= n - 1)
  //   // require(S / Pow2(cnt + 1) >= b * Pow2(n - cnt - 1))
  //   Pow2Mul(cnt + 2, n - cnt - 1)

  //   val e = if (S / Pow2(cnt + 1) >= b * Pow2(n - cnt - 1)) BigInt(1) else BigInt(0)
  //   val R = S / Pow2(cnt + 1) - b * e * Pow2(n - cnt - 1)
  //   val shiftRegHi = (S * 2 - b * e * Pow2(n + 1) + e) / Pow2(cnt + 2)
    
  //   // val R = S / Pow2(cnt + 1) - b * Pow2(n - cnt - 1)
  //   // val shiftRegHi = (S * 2 - b * Pow2(n + 1) + 1) / Pow2(cnt + 2)
  //   // val hi = S / Pow2(cnt + 1)
  //   // val lo = S - hi * Pow2(cnt + 1)
  //   // val tmpShiftRegHi1 = S * 2 - b * Pow2(n + 1)
  //   // val tmpShiftRegHi2 = Pow2(cnt + 2) * (hi - Pow2(n - cnt - 1) * b) + 2 * lo
    
  //   (R, shiftRegHi)
  // } ensuring(res => res._1 == res._2)

  // def PowMulDis(a: BigInt, b: BigInt, cnt: BigInt): (BigInt, BigInt) = {
  //   require(cnt >= 0)
  //   val r1 = a * Pow2(cnt) + b * Pow2(cnt)
  //   val r2 = (a + b) * Pow2(cnt)
  //   (r1, r2)
  // } ensuring(res => res._1 == res._2)

  // // cannot prove
  // def Pow2MulTest(a: BigInt, b: BigInt): (BigInt, BigInt) = {
  //   require(a >= 0 && b >= 0)
  //   Pow2Mul(a, b)
  //   val p1 = Pow2(a + b)
  //   val p2 = Pow2(a)
  //   val p3 = Pow2(b)
  //   val mul = p2 * p3
    
  //   (p1, mul)
  // } // ensuring(res => res._1 == res._2)

  // def BigIntDiv(a: BigInt, b: BigInt, d: BigInt): (BigInt, BigInt) = {
  //   require(a >= 0)
  //   require(d > 0)
  //   require(b >= 0 && b < d)
  
  //   val S = a * d + b
  //   val div = S / d

  //   (a, div)
  // } // ensuring(res => res._1 == res._2)

  //  def real_minitest(S: Real, b: Real, n: BigInt, cnt: BigInt): (Real, Real) = {
  //   require(n >= 1)
  //   require(S >= Real(0) && S < RealPow2(2 * n + 1))
  //   require(b > Real(0) && b < RealPow2(n))
  //   // require(e >= 0 && e <= 1)
  //   require(cnt >= 0 && cnt <= n - 1)

  //   val e = if (S / RealPow2(cnt + 1) >= b * RealPow2(n - cnt - 1)) Real(1) else Real(0)
  //   val R = S / RealPow2(cnt + 1) - b * e * RealPow2(n - cnt - 1) + e / RealPow2(cnt + 2)
  //   val shiftRegHi = (S * Real(2) - b * e * RealPow2(n + 1) + e) / RealPow2(cnt + 2)

  //   (R, shiftRegHi)
  // } // ensuring(res => res._1 == res._2)
}