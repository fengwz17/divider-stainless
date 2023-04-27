package divider

object StainNutshellFixedClockTest0 {
  case class RegVar(var state: String, var shiftReg: BigInt, var cnt: BigInt, var valid: Boolean)

  def main(args: Array[String]): Unit = {
    NutshellFixedClock(4, 10, 3, 10)
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

  def Extract(a: BigInt, index: BigInt): (BigInt, BigInt) = {
    require(index >= 0 && Pow2(index) > 0)
    // high = a(n - 1, index)
    // low = a(index - 1, 0)
    val low = a % Pow2(index)
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

  def NutshellFixedClock(len: BigInt, input1: BigInt, input2: BigInt, istep: BigInt): Unit = {
    val RegVar = new RegVar("s_idle", 0, 0, false)
    var step = 0
    var exit = false
    while (exit != true) {
      val (resR, resQ, valid) = OneClock(RegVar, len, input1, input2)
      exit = valid
      step = step + 1
    }
  }

  def OneClock(RegVar: RegVar, len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt, Boolean) = {
    require(len >= 1 && input1 >= 0 && input1 < Pow2(len) && input2 > 0 && input2 < Pow2(len))

    val a = input1
    val b = input2
    val bReg = b
    val aValx2Reg = a * 2 

    val hi = Extract(RegVar.shiftReg, len)._1
    val lo = Extract(RegVar.shiftReg, len)._2

    val enough = hi >= bReg
    val hi_next_0 = Mux(enough, hi - bReg, hi)
    val hi_next = Extract(hi_next_0, len)._2
    val enough2BigInt = Mux(enough, 1, 0)
    val shiftReg_next_0 = Cat(lo, enough2BigInt, 1)
    val shiftReg_next_1 = Cat(hi, shiftReg_next_0, len + 1)


    val (state_next, cnt_next, shiftReg_next, valid_next) = RegVar.state match { 
      case "s_idle" => ("s_log2", RegVar.cnt, RegVar.shiftReg, false) 
      case "s_log2" => ("s_shift", RegVar.cnt, RegVar.shiftReg, false) 
      case "s_shift" => ("s_compute", RegVar.cnt, aValx2Reg, false)
      case "s_compute" if RegVar.cnt == len - 1 => ("s_finish", RegVar.cnt, RegVar.shiftReg, false)
      case "s_compute" if RegVar.cnt != len - 1 => ("s_compute", RegVar.cnt + 1, shiftReg_next_1, false) 
      case "s_finish" => ("s_idle", RegVar.cnt, RegVar.shiftReg, true)
      case _ => ("s_idle", RegVar.cnt, RegVar.shiftReg, false)
    }
    
    RegVar.state = state_next
    RegVar.shiftReg = shiftReg_next
    RegVar.cnt = cnt_next
    RegVar.valid = valid_next

    val resQ = lo
    val resR = Extract(hi, 1)._1

    println(s"Q: ${resQ}, R: ${resR}, valid: ${RegVar.valid}")
    (resR, resQ, RegVar.valid)
  } // ensuring (res => (input1 == input2 * res._2 + res._1) && (res._1 >= 0) && (res._1 < input2)) 
}