package divider

import stainless.collection._
import stainless.lang._
import stainless.math.BitVectors._

object NutshellFixedClock {

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
  } ensuring(res => res > 0)

  def Extract(a: BigInt, index: BigInt): (BigInt, BigInt) = {
    require(index >= 0 && Pow2(index) > 0)
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

  // def stateMachine(len: BigInt, state: String, cnt: BigInt, shiftReg: BigInt, hi: BigInt, lo: BigInt, a: BigInt): (BigInt, BigInt) = {
  //   require((state == "s_log2" || state == "s_shift" || state == "s_compute" || state == "s_finish") && cnt >= 0 && cnt <= len && a >= 0 && a < Pow2(len) && len >= 1)
  //   var res = (hi / 2, lo)
  //   if (state == "s_log2") {
  //     res = stateMachine(len, "s_shift", 0, shiftReg, hi, lo, a)
  //   }
  //   else if (state == "s_shift") {
  //     res = stateMachine(len, "s_compute", cnt, 2 * a, hi, lo, a) 
  //   }
  //   else if (state == "s_compute") {
  //     var cntVar = cnt + 1
  //     if (cntVar == len) {
  //       res = stateMachine(len, "s_finish", cntVar, shiftReg, hi, lo, a)
  //     }
  //     res = stateMachine(len, "s_compute", cntVar, shiftReg, hi, lo, a)
  //   }
  //   res
  // } ensuring(0 <= cnt && cnt <= len && (state == "s_log2" || state == "s_shift" || state == "s_compute" || state == "s_finish"))

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
    var hi = BigInt(0)
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

    // R = Extract(shiftReg_next, len - cnt + 1)._1
    // Q = Extract(shiftReg_next, len - cnt + 1)._2

    // (state == s_log2, cnt == len + 3), (state == s_shift, cnt = len + 2), (cnt = len + 1, state == s_compute), ..., 


  
    // var cnt = len + 3
    // (while (state != "s_finish") {
    //   cnt = cnt - 1
    //   if (state == "s_log2") {
    //     state = "s_shift"
    //   }
    //   else if (state == "s_shift") {
    //     shiftReg = a * 2
    //     state = "s_compute"
    //   }
    //   else if (state == "s_compute") {
    //     // 
    //     if (cnt == 1) {
    //       state = "s_finish"
    //     }
    //   }
    //   // R = Extract(shiftReg, len - cnt + 1)._1
    //   // Q = Extract(shiftReg, len - cnt + 1)._2
    // }) invariant((state == "s_log2" || state == "s_shift" || state == "s_compute" || state == "s_finish") && 1 <= cnt && cnt <= len + 3) // && R + Q * Pow2(cnt - 1) * b == a && R >= 0 && R < input2 * Pow2(cnt - 1))
    // // invariant(cnt >= 0 && cnt <= len && R + Q * Pow2(cnt) * b == a && R >= 0 && R < input2 * Pow2(cnt))
    // // (R == Extract(shiftReg, len - cnt + 1)._1) && (Q == Extract(shiftReg, len - cnt + 1)._2))
  
    // var cnt = len
    // (while (cnt > 0) {
    //   val enough = R >= bReg * Pow2(cnt - 1)
    //   R = Mux(enough, R - bReg * Pow2(cnt - 1), R)
    //   val enough2BigInt = Mux(enough, 1, 0)
    //   Q = Q * 2 + enough2BigInt
     
    // /*
    //   hi = Extract(R, cnt - 1)._1
    //   val enough = hi >= bReg
    //   val enough2BigInt = Mux(enough, 1, 0)
    //   hi = Mux(enough, hi - bReg, hi)
    //   hi = Extract(hi, len)._2
    //   R = Cat(hi, Extract(R, cnt - 1)._2, cnt - 1)
    //   Q = Q * 2 + enough2BigInt
    // */
    //   cnt = cnt - 1
    // })invariant(cnt >= 0 && cnt <= len && R + Q * Pow2(cnt) * b == a && R >= 0 && R < input2 * Pow2(cnt))
  
 
    /*
      // val tmp_R_0 = Extract(hi, len - cnt + 1)._2
      // val tmp_R_1 = Extract(lo, len - cnt + 1)._1
      // R = Cat(tmp_R_0, tmp_R_1, cnt - 1) 
      // Q = Extract(lo, len - cnt + 1)._2
    */

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

    }) invariant(cnt >= 0 && cnt <= len && R + Q * Pow2(cnt) * b == a && R >= 0 && R < input2 * Pow2(cnt) && R == Extract(shiftReg, len - cnt + 1)._1) 
    // && hi == Extract(shiftReg, len)._1 && hi == Extract(R, cnt)._1
      // shiftReg = shiftReg_next
      // hi = Extract(shiftReg, len)._1
      // lo = Extract(shiftReg, len)._2

    // hi = R * 2
    // lo = Q 
    val resQ = lo
    val resR = Extract(hi, 1)._1

    (resR, resQ)
  } // ensuring (res => (input1 == input2 * res._2 + res._1) && (res._1 >= 0) && (res._1 < input2)) 

    // && R == shiftReg / Pow2(len - cnt))
    // && shiftReg == Cat(R, Q, len - cnt + 1))
    // R == Extract(shiftReg, len - cnt + 1)._1 && Q == Extract(shiftReg, len - cnt + 1)._2

    // assert(shiftReg == Cat(R, Q, len + 1))

    // lo = Q
    // hi = R * 2

     // // shiftReg := Cat(Mux(enough, hi - bReg, hi)(len - 1, 0), lo, enough)
      // hi = Mux(enough, hi - bReg, hi)
      // hi = Extract(hi, len)._2
  
      // hi = Extract(shiftReg, len)._1
      // lo = Extract(shiftReg, len)._2
      // hi = Extract(R, cnt - 1)._1
      // val loR = Extract(R, cnt - 1)._2
      // lo = Cat(loR, Q, len - cnt + 1)

      // val enough = hi >= bReg
      // hi = Mux(enough, hi - bReg, hi)
      // hi = Extract(hi, len)._2
    
      // // R = Cat(hi, loR, cnt - 1)
      // R = Mux(enough, R - bReg * Pow2(cnt - 1), R)
      // val enough2BigInt = Mux(enough, 1, 0)
      // Q = Q * 2 + enough2BigInt 

      // shiftReg = Cat(lo, enough2BigInt, 1)hi
      // shiftReg = Cat(hi, shiftReg, len + 1)
      // shiftReg = lo * 2 + enough2BigInt
      // shiftReg = hi * Pow2(len + 1) + shiftReg

/*
  def NutshellFixedClockSimple(len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt) = {
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
    var shiftReg_next = a * 2

    var state = "s_log2"
    var stateNext = "s_log2"

    var cnt = len

    // hi_next = Extract(shiftReg_next, len)._1
    // lo_next = Extract(shiftReg_next, len)._2

    var R = input1
    var Q = BigInt(0)

    // R = Extract(shiftReg_next, len - cnt + 1)._1
    // Q = Extract(shiftReg_next, len - cnt + 1)._2

    (while (cnt > 0) {
      // state = stateNext
      // shiftReg = shiftReg_next
      // hi = hi_next
      // lo = lo_next
      
      // val enough = hi >= bReg

      // // shiftReg := Cat(Mux(enough, hi - bReg, hi)(len - 1, 0), lo, enough)
      // hi = Mux(enough, hi - bReg, hi)
      // hi = Extract(hi, len)._2
      // val enough2BigInt = Mux(enough, 1, 0)
      // shiftReg_next = Cat(lo, enough2BigInt, 1)
      // shiftReg_next = Cat(hi, shiftReg_next, len + 1)
      // hi_next = Extract(shiftReg_next, len)._1
      // lo_next = Extract(shiftReg_next, len)._2

      val enough = R >= input2 * Pow2(cnt - 1)
      R = Mux(enough, R - input2 * Pow2(cnt - 1), R)
      val enough2BigInt = Mux(enough, 1, 0)
      Q = Q * 2 + enough2BigInt 

      cnt = cnt - 1

    }) invariant(cnt >= 0 && cnt <= len && R + Q * Pow2(cnt) * b == a && R >= 0 && R < input2 * Pow2(cnt))
    
    // val r    = hi(len, 1)
    // val resQ = Mux(qSignReg, -lo, lo)
    // val resR = Mux(aSignReg, -r, r)
    // val r = Extract(hi_next, 1)._1
    // val resQ = Extract(shiftReg_next, len + 1)._2
    // val resR = r
    val resQ = Q
    val resR = R
    (resR, resQ)
  } ensuring (res => (input1 == input2 * res._2 + res._1) && (res._1 >= 0) && (res._1 < input2)) 
*/

  // def NutshellFixedClock(len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt) = {
  //   require(len >= 1 && input1 >= 0 && input1 < Pow2(len) && input2 > 0 && input2 < Pow2(len))

  //   val a = input1
  //   val b = input2
  //   val divBy0 = (b == 0)
  //   val bReg = b
  //   val aValx2Reg = a * 2 

  //   var hi = BigInt(0)
  //   var lo = BigInt(0)
  //   var shiftReg = BigInt(0)

  //   var hi_next = BigInt(0)
  //   var lo_next = BigInt(0)
  //   var shiftReg_next = BigInt(0)

  //   var state = "s_log2"
  //   var stateNext = "s_log2"

  //   var cnt = BigInt(0)

  //   (while (state != "s_finish") {
  //     state = stateNext
  //     shiftReg = shiftReg_next
  //     hi = hi_next
  //     lo = lo_next
  //     if (state == "s_log2") {
  //       stateNext = "s_shift"
  //     }
  //     else if (state == "s_shift") {
  //       shiftReg_next = a * 2

  //       // val hi = shiftReg(len * 2, len)
  //       // val lo = shiftReg(len - 1, 0)
  //       hi_next = Extract(shiftReg_next, len - 1)._1
  //       lo_next = Extract(shiftReg_next, len - 1)._2

  //       stateNext = "s_compute"
  //     }
  //     else if (state == "s_compute") {
  //       val enough = hi >= bReg

  //       // shiftReg := Cat(Mux(enough, hi - bReg, hi)(len - 1, 0), lo, enough)
  //       hi = Mux(enough, hi - bReg, hi)
  //       hi = Extract(hi, len - 1)._2
  //       val enough2BigInt = Mux(enough, 1, 0)
  //       shiftReg_next = Cat(lo, enough2BigInt, 1)
  //       shiftReg_next = Cat(hi, shiftReg_next, len + 1)
  //       hi_next = Extract(shiftReg_next, len - 1)._1
  //       lo_next = Extract(shiftReg_next, len - 1)._2

  //       cnt = cnt + 1

  //       if (cnt == len) {
  //         stateNext = "s_finish"
  //       }
  //     }
  //   }) invariant(cnt >= 0 && cnt <= len)

  //   // val r    = hi(len, 1)
  //   // val resQ = Mux(qSignReg, -lo, lo)
  //   // val resR = Mux(aSignReg, -r, r)
  //   val r = Extract(hi, 0)._1
  //   val resQ = lo
  //   val resR = r
  //   (resR, resQ)
  // } // ensuring (res => res._1 >= 0 && res._1 < input2 && input1 == input2 * res._2 + res._1)
}
