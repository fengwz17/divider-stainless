package divider

object StainVerifyDividerFixedClockCompute1 {
  // case class RegVar(var state: String, var shiftReg: BigInt, var cnt: BigInt, var valid: Boolean)

  def main(args: Array[String]): Unit = {
    println(VerifyDividerFixedClock(5, 20, 6))
  }

  def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
    case true => y
    case _ => z
  } // ensuring(res => (x && (res == y)) || (!x && (res == z)))

  def Pow2(exp: BigInt): BigInt = {
      require(exp >= 0) 
      exp match {
        case zero if (zero == 0) => 1
        case one if (one == 1) => 2
        case _ => 2 * Pow2(exp - 1)
      }
  }

  /* (h, l) = Extract(a, i)
   * a = an-1an-2...a1a0
   * h = an-1...ai
   * l = ai-1...a0
  */ 
  def Extract(a: BigInt, index: BigInt): (BigInt, BigInt) = {
    require(index >= 0) // && Pow2(index) > 0)
    val low = a % Pow2(index)
    val high = a / Pow2(index)
    return (high, low)
  } // ensuring(res => a == res._1 * Pow2(index) + res._2 && 0 <= res._2 && res._2 < Pow2(index))

  // res = (a, b)
  def Cat(a: BigInt, b: BigInt, len: BigInt): BigInt = {
    require(len >= 0)
    len match {
      case zero if (len == 0) => a
      case _ => a * Pow2(len) + b
    }
  }

  def VerifyDividerFixedClock(len: BigInt, in1: BigInt, in2: BigInt): (BigInt, BigInt) = {
    require(len >= 1 && in1 >= 0 && in1 < Pow2(len) && in2 > 0 && in2 < Pow2(len))

    var state = "s_compute"

    val a = in1
    val b = in2 

    var shiftReg = Cat(a, BigInt(0), 1)

    var cnt = BigInt(0)
    
    var out = (BigInt(0), BigInt(0))

    while (cnt <= len) {
      var hi = Extract(shiftReg, len)._1
      var lo = Extract(shiftReg, len)._2

      val enough = hi >= b

      val shiftReg_tmp = Cat(lo, Mux(enough, BigInt(1), BigInt(0)), 1)
      // val hi_tmp = Extract(Mux(enough, hi - b, hi), len)._2
      val hi_tmp = Mux(enough, hi - b, hi)
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
      println(out, cnt, state)

      state = state_next
      shiftReg = shiftReg_next
      cnt = cnt_next
    }
    out
  } // ensuring (res => (input1 == input2 * res._2 + res._1) && (res._1 >= 0) && (res._1 < input2)) 
}