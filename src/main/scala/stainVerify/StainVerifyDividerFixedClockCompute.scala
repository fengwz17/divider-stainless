package divider

object StainVerifyDividerFixedClockCompute {
  case class RegVar(var state: String, var shiftReg: BigInt, var cnt: BigInt, var valid: Boolean)

  def main(args: Array[String]): Unit = {
    for (i <- 0 to 10) {
      VerifyDividerFixedClock(4, 5, i, 10)
    }
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

  def VerifyDividerFixedClock(len: BigInt, input1: BigInt, input2: BigInt, steps: BigInt): Unit = {
    val RegVar = new RegVar("s_compute", 2 * input1, 0, false)
    // var step = 0
    // var exit = false
    var step = steps
    while (step >= 0) {
      val (resR, resQ, valid) = DividerFixedClock(RegVar, len, input1, input2)
      step = step - 1
    }
  }

  def DividerFixedClock(RegVar: RegVar, len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt, Boolean) = {
    // require(len >= 1 && input1 >= 0 && input1 < Pow2(len) && input2 > 0 && input2 < Pow2(len))

    val a = input1
    val b = input2

    println(RegVar.shiftReg)

    val shiftReg = RegVar.shiftReg
    val hi = Extract(shiftReg, len)._1
    val lo = Extract(shiftReg, len)._2

    val bReg = b
    // val aValx2Reg = Cat(a, BigInt(0), 1)
    
    val cnt = RegVar.cnt
    val state = RegVar.state

    val enough = hi >= bReg

    val shiftReg_next_tmp = Cat(lo, Mux(enough, BigInt(1), BigInt(0)), 1)
    val hi_tmp = Extract(Mux(enough, hi - bReg, hi), len)._2
    val shiftReg_next = Cat(hi_tmp, shiftReg_next_tmp, len + 1)
    val cnt_next = cnt + 1
    val state_next = cnt match {
      case finish if finish == (len - 1) => "s_finish"
      case _ => "s_compute"
    }

    val r = Extract(hi, 1)._1
    val resQ = lo
    val resR = r
    val valid_next = state match {
      case "s_finish" => true
      case _ => false
    }

    RegVar.state = state_next
    RegVar.shiftReg = shiftReg_next
    RegVar.cnt = cnt_next
    RegVar.valid = valid_next

    if (RegVar.valid == true) {
      println(s"Q: ${resQ}, R: ${resR}, valid: ${RegVar.valid}")
    }
    (resR, resQ, RegVar.valid)
  } // ensuring (res => (input1 == input2 * res._2 + res._1) && (res._1 >= 0) && (res._1 < input2)) 
}