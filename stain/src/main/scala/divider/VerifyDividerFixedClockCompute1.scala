import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

object StainVerifyDividerFixedClockCompute1 {
  // case class RegVar(var state: String, var shiftReg: BigInt, var cnt: BigInt, var valid: Boolean)

  def main(args: Array[String]): Unit = {
    // println(VerifyDividerFixedClock(5, 20, 21))
  }

  def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
    case true => y
    case _ => z
  } // ensuring(res => (x && (res == y)) || (!x && (res == z)))

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


  /* (h, l) = Extract(a, i)
   * a = an-1an-2...a1a0
   * h = an-1...ai
   * l = ai-1...a0
  */ 
  def Extract(a: BigInt, index: BigInt): (BigInt, BigInt) = {
    require(a >= 0 && index >= 0) // && Pow2(index) > 0)
    // val low = a % Pow2(index)
    val high = a / Pow2(index)
    val low = a - high * Pow2(index)
    (high, low)
  } ensuring(res => a == res._1 * Pow2(index) + res._2 && 0 <= res._2 && res._2 < Pow2(index))

  // res = (a, b)
  def Cat(a: BigInt, b: BigInt, len: BigInt): BigInt = {
    require(len >= 0 && a >= 0 && b >= 0)
    val result = len match {
      case zero if (len == 0) => a
      case _ => a * Pow2(len) + b
    }
    result
  } ensuring(res => res >= 0)

  def VerifyDividerFixedClock(len: BigInt, in1: BigInt, in2: BigInt): (BigInt, BigInt) = {
    require(len >= 1 && in1 >= 0 && in1 < Pow2(len) && in2 > 0 && in2 < Pow2(len))

    var state = "s_compute"

    val a = in1
    val b = in2 

    var shiftReg = Cat(a, BigInt(0), 1)

    var cnt = BigInt(0)
    
    var out = (BigInt(0), BigInt(0))

    var R = a
    var Q = BigInt(0)

    (while (cnt < len) {
      decreases(len - cnt)

      Pow2Mul(cnt + 2, len - cnt - 1)

      val hi = Extract(shiftReg, len)._1
      val lo = Extract(shiftReg, len)._2

      val enough = hi >= b

      val enoughValue = Mux(enough, BigInt(1), BigInt(0))

      val shiftReg_tmp = Cat(lo, enoughValue, 1)
      // val hi_tmp = Extract(Mux(enough, hi - b, hi), len)._2
      val hi_tmp = Mux(enough, hi - b, hi)
      
      assert(hi_tmp == hi - b * enoughValue)

      val shiftReg_next = Cat(hi_tmp, shiftReg_tmp, len + 1)
      val cnt_next = cnt + 1
      val state_next = cnt match {
        case finish if finish == (len - 1) => "s_finish"
        case _ => "s_compute"
      }

      val r = Extract(hi, 1)._1
      val resQ = lo
      val resR = r
      out = (resQ, resR)

      R = Mux(enough, R - b * Pow2(len - cnt - 1), R)
      Q = Q * 2 + Mux(enough, BigInt(1), BigInt(0))

      state = state_next
      shiftReg = shiftReg_next
      cnt = cnt_next

      // R + Q * Pow2(len - cnt) * b == a
      // R' + Q' * Pow2(len - cnt - 1) * b == a
      // Extract(shiftReg, cnt + 1)._1 / Pow2(len - cnt) + Extract(shiftReg, cnt + 1)._2 * b == a / Pow2(len - cnt)
      // Extract(shiftReg, cnt + 2)._1 / Pow2(len - cnt - 1) + Extract(shiftReg, cnt + 2)._2 * b == a / Pow2(len - cnt - 1)

      // shiftReg / Pow2(len + 1) + shiftReg mod Pow2(cnt + 1) * b == a / Pow2(len - cnt)
      

    }) invariant (cnt >= 0 && cnt <= len && shiftReg >= 0 && shiftReg < Pow2(cnt + len + 1)) // && (R, Q) == Extract(shiftReg, cnt + 1))
    // update hi, lo and (resQ, resR)
    out
  } // ensuring (res => (input1 == input2 * res._2 + res._1) && (res._1 >= 0) && (res._1 < input2)) 
}