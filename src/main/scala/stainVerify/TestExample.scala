package stainVerify
// import stainless.lang._
// import stainless.collection._

// import scala.collection.immutable.BitSet

object TestExample {
 def main(args: Array[String]): Unit = {
    foo(4, 10, 3)
  }

  def Pow2(exp: BigInt): BigInt = {
      require(exp >= 0) 
      val result = exp match {
        // case neg if (neg < 0) => 1
        // case 0 => 1
        // case 1 => result
        case zero if (zero == 0) => BigInt(1)
        case _ => 2 * Pow2(exp - 1)
      }
      result
  } // ensuring(res => res > 0)


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
  } // ensuring(res => res >= 0)

  def Extract(a: BigInt, index: BigInt): (BigInt, BigInt) = {
      require(a >= 0 && index >= 0) // && Pow2(index) > 0)
      // high = a(n - 1, index)
      // low = a(index - 1, 0)
      val low = a % Pow2(index)
      // val high = (a - low) / Pow2(index)
      val high = a / Pow2(index)
      (high, low)
  } // ensuring(res => a == res._1 * Pow2(index) + res._2 && 0 <= res._2 && res._2 < Pow2(index))

  def foo(len: BigInt, a: BigInt, b: BigInt): (BigInt, BigInt) = {
    require(len >= 1)
    require(a < Pow2(len) && a >= 0)
    require(b < Pow2(len) && b > 0)
    var cnt = BigInt(0)
    var R = a
    var shiftReg = a * 2
    
    (while (cnt < len) {
      // decreases(len - cnt)
      val e = Mux(R >= b * Pow2(len - cnt - 1), BigInt(1), BigInt(0))
      R = R - b * Pow2(len - cnt - 1) * e

      val hi = shiftReg / Pow2(len)
      val lo = shiftReg - hi * Pow2(len)

      shiftReg = ((hi - b * e) * Pow2(len + 1) + lo * 2 + e)

      val compare_shiftReg = shiftReg / Pow2(cnt + 2)

      println(R, hi, lo, shiftReg, compare_shiftReg)

      cnt = cnt + 1
    }) // invariant (0 <= cnt && cnt <= len)
    
    val hi = shiftReg / Pow2(len)
    val resR = hi / 2
    val resQ = shiftReg - hi * Pow2(len)
    println(resQ, resR)
    (resQ, resR)
  } // ensuring(res => res > 0)
}