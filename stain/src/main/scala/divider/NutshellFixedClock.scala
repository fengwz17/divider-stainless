package divider

import stainless.collection._
import stainless.lang._
import stainless.math.BitVectors._

object NutshellFixedClock {
    def main(args: Array[String]): Unit = {
      // val res = NutshellFixedClock(4, 5, 3)
      // println(res)
    }

    def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
      case true => y
      case _ => z
    } // ensuring(res => (x && (res == y)) || (!x && (res == z)))

    def pow2while(n: BigInt): BigInt = {
        var res = BigInt(1)
        var x = n
        while (x > 0) {
            res = res * BigInt(2)
            x = x - 1
        }
        res
    } // ensuring(res => res == 2^n)

    // another implementation: case _ => result * _pow(result, exp - 1)
    def pow2(result: BigInt, exp: BigInt): BigInt = {
        require(exp >= 0) 
        exp match {
          // case neg if (neg < 0) => 1
          // case 0 => 1
          // case 1 => result
          case zero if (zero == 0) => 1
          case one if (one == 1) => result
          case _ => 2 * pow2(result, exp - 1)
        }
    } 

    // input1.length = 2n, 0 <= input1 <= input2 * 2^{n} - 1
    // input2.length = n, 0 <= input2 <= 2^{n} - 1
    // input1 = input2 * Q + R 
    // pow2 = pow2(2, len)
    def NutshellFixedClock(len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt) = {
      require(len >= 2 && input1 >= 0 && input1 < pow2(2, len) && input2 > 0 && input2 < pow2(2, len))
      
      // val stateArray = Array("s_idle", "s_log2", "s_shift", "s_compute", "s_finish")
      val a = input1
      val b = input2
      val divBy0 = (b == 0)
      val bReg = b
      val aValx2Reg = a * 2 
      var hi = BigInt(0)
      var lo = BigInt(0)
      var hi_hi = BigInt(0)
      var hi_lo = BigInt(0)
      var lo_hi = BigInt(0)
      var lo_lo = BigInt(0)
      var hi_next = BigInt(0)
      var lo_next = BigInt(0)
      var hi_hi_next = BigInt(0)
      var hi_lo_next = BigInt(0)
      var lo_hi_next = BigInt(0)
      var lo_lo_next = BigInt(0)
      // var shiftReg = BigInt(0)

      var state = "s_log2"
      var stateNext = ""

      var cnt = BigInt(0)

      (while (state != "s_finish") {

        state = stateNext
        hi_hi = hi_hi_next
        hi_lo = hi_lo_next
        lo_hi = lo_hi_next
        lo_lo = lo_lo_next
        hi = hi_next
        lo = lo_next

        // shiftReg = shiftRegNext
        if (state == "s_log2") {
          stateNext = "s_shift"
        }
        else if (state == "s_shift") {
          // shiftRegNext = aValx2Reg
          val a_hi_0 = Mux(a >= pow2(2, len - 1), 1, 0)
          // val a_hi_1 = Mux(a - a_hi_0 * pow2(2, len - 1) >= pow2(2, len - 2), 1, 0)
  
          hi_next = a_hi_0
          lo_next = (a - a_hi_0 * pow2(2, len - 1)) * 2

          hi_hi_next = Mux(hi_next >= pow2(2, len), 1, 0)
          hi_lo_next = hi_next - hi_hi_next * pow2(2, len)
          lo_hi_next = Mux(lo_next >= pow2(2, len - 1), 1, 0)
          lo_lo_next = lo_next - lo_hi_next * pow2(2, len - 1)

          stateNext = "s_compute"
        }
        else if (state == "s_compute") {
          val enough = hi >= bReg

          // shiftReg := Cat(Mux(enough, hi - bReg, hi)(len - 1, 0), lo, enough)
          hi = Mux(enough, hi - bReg, hi)
          val enoughBigInt = Mux(enough, 1, 0)

          hi_hi = Mux(hi >= pow2(2, len), 1, 0)
          hi_lo = hi - hi_hi * pow2(2, len)

          hi_next = hi_lo * 2 + lo_hi
          lo_next = lo_lo * 2 + enoughBigInt

          hi_hi_next = Mux(hi_next >= pow2(2, len), 1, 0)
          hi_lo_next = hi_next - hi_hi_next * pow2(2, len)
          lo_hi_next = Mux(lo_next >= pow2(2, len - 1), 1, 0)
          lo_lo_next = lo_next - lo_hi_next * pow2(2, len - 1)

          cnt = cnt + 1

          if (cnt == len) {
            stateNext = "s_finish"
          }
        }
      })

      val R = (hi - hi % 2) / 2
      val Q = lo
      (R, Q)
    } ensuring (res => res._1 >= 0 && res._1 < input2 && input1 == input2 * res._2 + res._1)
}
