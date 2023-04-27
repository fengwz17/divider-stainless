package divider

import stainless.collection._
import stainless.lang._
import stainless.math.BitVectors._

object NutshellFixedClockTest1 {
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
    require(index >= 0 && Pow2(index) > 0)
    // high = a(n - 1, index)
    // low = a(index - 1, 0)
    val low = a % Pow2(index)
    // val high = (a - low) / Pow2(index)
    val high = a / Pow2(index)
    return (high, low)
  } 

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

    var hi = BigInt(0)
    var lo = BigInt(0)
    // var shiftReg = BigInt(0)

    var hi_next = BigInt(0)
    var lo_next = BigInt(0)
    var shiftReg = a * 2

    var state = "s_log2"
    var stateNext = "s_log2"

    var cnt = len

    var R = Extract(shiftReg, 1)._1
    var Q = BigInt(0)

    (while (cnt > 0) {

      hi = Extract(R, cnt - 1)._1
      val loR = Extract(R, cnt - 1)._2

      val enough = hi >= bReg
      hi = Mux(enough, hi - bReg, hi)
      hi = Extract(hi, len)._2
      R = Cat(hi, loR, cnt - 1)

      val enough2BigInt = Mux(enough, 1, 0)
      Q = Q * 2 + enough2BigInt 

      cnt = cnt - 1

    }) invariant(cnt >= 0 && cnt <= len && R + Q * Pow2(cnt) * b == a && R >= 0 && R < input2 * Pow2(cnt))
      // R == Extract(shiftReg, len - cnt + 1)._1 && (Q == Extract(shiftReg, len - cnt + 1)._2))
    
    lo = Q
    hi = Cat(R, 0, 1)

    val resQ = lo
    val resR = Extract(hi, 1)._1
    (resR, resQ)
  } ensuring (res => (input1 == input2 * res._2 + res._1) && (res._1 >= 0) && (res._1 < input2)) 
}
