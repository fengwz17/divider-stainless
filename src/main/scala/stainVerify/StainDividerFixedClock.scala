package divider

// import stainless.collection._
// import stainless.lang._
// import stainless.math.BitVectors._

object StainDividerFixedClock {
    def main(args: Array[String]): Unit = {
      for (i <- 0 to 5) {
        for (j <- 1 to 5) {
          val res = NutshellFixedClock(3, i, j)
          println(i , j, res._1, res._2)
        }
      }
    }

    def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
      case true => y
      case _ => z
    } // ensuring(res => (x && (res == y)) || (!x && (res == z)))

    // another implementation: case _ => result * _pow(result, exp - 1)
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
      // high = a(n - 1, index + 1)
      // low = a(index, 0)
      val low = a % Pow2(index + 1)
      val high = (a - low) / Pow2(index + 1)
      return (high, low)
    } 

    def Cat(a: BigInt, b: BigInt, len: BigInt): BigInt = {
      // res = (a, b)
      val res = a * Pow2(len) + b
      res
    }

    def NutshellFixedClock(len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt) = {
      require(len >= 1 && input1 >= 0 && input1 < Pow2(len) && input2 > 0 && input2 < Pow2(len))
      
      val a = input1
      val b = input2
      val divBy0 = (b == 0)
      val bReg = b
      val aValx2Reg = a * 2 

      var hi = BigInt(0)
      var lo = BigInt(0)
      var shiftReg = BigInt(0)

      var hi_next = BigInt(0)
      var lo_next = BigInt(0)
      var shiftReg_next = BigInt(0)

      var state = "s_log2"
      var stateNext = "s_log2"

      var cnt = BigInt(0)

      (while (state != "s_finish") {
        state = stateNext
        shiftReg = shiftReg_next
        hi = hi_next
        lo = lo_next
        if (state == "s_log2") {
          stateNext = "s_shift"
        }
        else if (state == "s_shift") {
          shiftReg_next = a * 2

          // val hi = shiftReg(len * 2, len)
          // val lo = shiftReg(len - 1, 0)
          hi_next = Extract(shiftReg_next, len - 1)._1
          lo_next = Extract(shiftReg_next, len - 1)._2

          stateNext = "s_compute"
        }
        else if (state == "s_compute") {
          val enough = hi >= bReg

          // shiftReg := Cat(Mux(enough, hi - bReg, hi)(len - 1, 0), lo, enough)
          hi = Mux(enough, hi - bReg, hi)
          hi = Extract(hi, len - 1)._2
          val enough2BigInt = Mux(enough, 1, 0)

          shiftReg_next = Cat(lo, enough2BigInt, 1)
          shiftReg_next = Cat(hi, shiftReg_next, len + 1)
          hi_next = Extract(shiftReg_next, len - 1)._1
          lo_next = Extract(shiftReg_next, len - 1)._2
 
          cnt = cnt + 1

          if (cnt == len) {
            stateNext = "s_finish"
          }
        }
      })

      // val r    = hi(len, 1)
      // val resQ = Mux(qSignReg, -lo, lo)
      // val resR = Mux(aSignReg, -r, r)
      val r = Extract(hi, 0)._1
      val resQ = lo
      val resR = r
      (resR, resQ)
    } ensuring (res => res._1 >= 0 && res._1 < input2 && input1 == input2 * res._2 + res._1)

    // input1.length = 2n, 0 <= input1 <=  // c.io.out.bits.expect("b1001".U)input2 * 2^{n} - 1
    // input2.length = n, 0 <= input2 <= 2^{n} - 1
    // input1 = input2 * Q + R 
    // Pow2 = Pow(len)
    def NutshellFixedClockSplit(len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt) = {
      require(len >= 1 && input1 >= 0 && input1 < Pow2(len) && input2 > 0 && input2 < Pow2(len))
      
      // val stateArray = Array("s_idle", "s_log2", "s_shift", "s_compute", "s_finish")
      val a = input1
      val b = input2
      val divBy0 = (b == 0)
      val bReg = b
      val aValx2Reg = a * 2 

      // hi = shiftReg(len * 2, len), hi_hi = hi(len), hi_lo = hi(len - 1, 0)
      // lo = shiftReg(len - 1, 0), lo_hi = lo(len - 1), lo_lo = lo(len - 2, 0)
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

      var state = "s_log2"
      var stateNext = "s_log2"

      var cnt = BigInt(0)

      (while (state != "s_finish") {
        state = stateNext
        hi_hi = hi_hi_next
        hi_lo = hi_lo_next
        lo_hi = lo_hi_next
        lo_lo = lo_lo_next
        hi = hi_next
        lo = lo_next
        if (state == "s_log2") {
          stateNext = "s_shift"
        }
        else if (state == "s_shift") {
          val a_hi_0 = Mux(a >= Pow2(len - 1), 1, 0)
  
          hi_next = a_hi_0
          lo_next = (a - a_hi_0 * Pow2(len - 1)) * 2

          hi_hi_next = Mux(hi_next >= Pow2(len), 1, 0)
          hi_lo_next = hi_next - hi_hi_next * Pow2(len)
          lo_hi_next = Mux(lo_next >= Pow2(len - 1), 1, 0)
          lo_lo_next = lo_next - lo_hi_next * Pow2(len - 1)

          stateNext = "s_compute"
        }
        else if (state == "s_compute") {
          val enough = hi >= bReg

          // shiftReg := Cat(Mux(enough, hi - bReg, hi)(len - 1, 0), lo, enough)
          hi = Mux(enough, hi - bReg, hi)
          val enoughBigInt = Mux(enough, 1, 0)

          hi_hi = Mux(hi >= Pow2(len), 1, 0)
          hi_lo = hi - hi_hi * Pow2(len)

          hi_next = hi_lo * 2 + lo_hi
          lo_next = lo_lo * 2 + enoughBigInt

          hi_hi_next = Mux(hi_next >= Pow2(len), 1, 0)
          hi_lo_next = hi_next - hi_hi_next * Pow2(len)
          lo_hi_next = Mux(lo_next >= Pow2(len - 1), 1, 0)
          lo_lo_next = lo_next - lo_hi_next * Pow2(len - 1)

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
