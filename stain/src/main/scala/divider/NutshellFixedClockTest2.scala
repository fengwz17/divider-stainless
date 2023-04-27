package divider

import stainless.collection._
import stainless.lang._
import stainless.math.BitVectors._

object NutshellFixedClockTest2 {

  def main(args: Array[String]): Unit = {
    // for (i <- 0 to 1) {
    //   for (j <- 1 to 1) {
    //     val res = NutshellFixedClock(1, i, j)
    //     println(i , j, res._1, res._2)
    //   }
    // }
  }

  def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
    case true => y
    case _ => z
  } // ensuring(res => (x && (res == y)) || (!x && (res == z)))

  def Pow2(exp: BigInt): BigInt = {
      require(exp >= 0) 
      exp match {
        // case neg if (neg < 0) => 1
        // case 0 => 1
        // case 1 => result
        case zero if (zero == 0) => 1
        case one if (one == 1) => 2
        case _ => 2 * Pow2(exp - 1)
      }
  }

  def Extract(a: BigInt, index: BigInt): (BigInt, BigInt) = {
    require(index >= 0) // && Pow2(index) > 0)
    // high = a(n - 1, index)
    // low = a(index - 1, 0)
    val low = a % Pow2(index)
    // val high = (a - low) / Pow2(index)
    val high = a / Pow2(index)
    (high, low)
  } ensuring(res => a == res._1 * Pow2(index) + res._2 && 0 <= res._2 && res._2 < Pow2(index))

  // @law
  // def law_extract(a: BigInt, index: BigInt) = {
  //   a == Extract(a, index)._1 * Pow2(index) + Extract(a, index)._2 && 0 <= Extract(a, index)._2 && Extract(a, index)._2 < Pow2(index)
  // }

  // res = (a, b)
  def Cat(a: BigInt, b: BigInt, len: BigInt): BigInt = {
    require(len >= 0)
    len match {
      case zero if (len == 0) => a
      case _ => a * Pow2(len) + b
    }
  }

  def NutshellFixedClockVerify(len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt) = {
    require(len >= 1 && input1 >= 0 && input1 < Pow2(len) && input2 > 0 && input2 < Pow2(len))

    val a = input1
    val b = input2
    val divBy0 = (b == 0)
    val bReg = b
    val aValx2Reg = a * 2 
 
    // var shiftReg = BigInt(0)
    var shiftReg = 2 * a
    var shiftReg_next = 2 * a

    // var hi = BigInt(0)
    var hi = 2 * a
    var lo = BigInt(0)
    var hi_next = a // Extract(shiftReg_next, len)._1
    var lo_next = BigInt(0)

    val stateArray = Array("s_log2", "s_shift", "s_compute", "s_finish")
    var state = "s_log2"
    // var stateNext = "s_log2"

    hi = Extract(shiftReg, len)._1
    lo = Extract(shiftReg, len)._2

    // var R = Extract(shiftReg, 1)._1
    // var R = BigInt(0)
    var R = a
    var Q = BigInt(0)
    var R_next = shiftReg_next / 2
    var Q_next = BigInt(0)

    var cnt = len
    (while (cnt > 0) {
      val enough = hi >= bReg
      val enough2BigInt = Mux(enough, 1, 0)

      val tmp_hi_0 = Mux(enough, hi - bReg, hi)
      val tmp_hi_1 = Extract(tmp_hi_0, len)._2
      val tmp_shiftReg = Cat(lo, enough2BigInt, 1)
      shiftReg_next = Cat(tmp_hi_1, tmp_shiftReg, len + 1) 

      hi_next = Extract(shiftReg_next, len)._1
      lo_next = Extract(shiftReg_next, len)._2

      // val enoughR = Extract(R, len - cnt + 1)._1 >= bReg
      val enoughR = R >= bReg * Pow2(cnt - 1)
      val enoughR2BigInt = Mux(enoughR, 1, 0)
      R_next = Mux(enoughR, R - bReg * Pow2(cnt - 1), R)
      Q_next = Q * 2 + enoughR2BigInt

      cnt = cnt - 1

      R = R_next
      Q = Q_next

      shiftReg = shiftReg_next
      hi = hi_next
      lo = lo_next

    }) invariant(cnt >= 0 && cnt <= len && R + Q * Pow2(cnt) * b == a && R >= 0 && R < input2 * Pow2(cnt) && 
      R == Extract(shiftReg, len - cnt + 1)._1 && shiftReg == hi * Pow2(len) + lo && 
      0 <= lo && lo < Pow2(len) && 
      0 <= hi && hi < Pow2(len + 1)) 
    // && hi == Extract(shiftReg, len)._1 && hi == Extract(R, cnt)._1
    val resQ = lo
    val resR = Extract(hi, 1)._1

    (resR, resQ)
  } // ensuring (res => (input1 == input2 * res._2 + res._1) && (res._1 >= 0) && (res._1 < input2)) 
}
