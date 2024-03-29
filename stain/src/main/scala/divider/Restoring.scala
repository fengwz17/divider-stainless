package divider

import stainless.collection._
import stainless.lang._
import stainless.math.BitVectors._

object Restoring {
  def main(args: Array[String]): Unit = {
    // val res = RestoringDividerUnsign(2, 1, 2)
    // println(res)
  }

  def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
    case true => y
    case _ => z
  } // ensuring(res => (x && (res == y)) || (!x && (res == z)))

  def Pow2while(n: BigInt): BigInt = {
      var res = BigInt(1)
      var x = n
      while (x > 0) {
          res = res * BigInt(2)
          x = x - 1
      }
      res
  } // ensuring(res => res == 2^n)

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

  // input1.length = 2n, 0 <= input1 <= input2 * Pow22^{n} - 1
  // input2.length = n, 0 <= input2 <= 2^{n} - 1
  // input1 = input2 * Q + R 
  // Pow2 = Pow2(2, len)
  def RestoringDividerUnsign(len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt) = {
    require(len >= 1 && input1 >= 0 && input1 < input2 * Pow2(len) && input2 > 0 && input2 < Pow2(len))

    val n = len
    val D = input2

    var R = input1

    var q = BigInt(0)

    // pre-condition => invariant
    // invariant hold in loop
    // invariant \wedge \neg loop-condition => res
    // invariant include j, Q, R, when exit loop (j = 0)
    var j = n
    // var Qbit = BigInt(0)
    // var lshift = Pow2(j)
    (while (j >= BigInt(1)) {
      j = j - 1
      val Qbit = Mux(R < D * Pow2(j), BigInt(0), BigInt(1))   
      q = q + Qbit * Pow2(j)
      R = R - Mux(Qbit, D * Pow2(j), BigInt(0))
    }) invariant(j >= 0 && R < input2 * Pow2(j) && R >= 0 && R == input1 - input2 * q) 
    
    // val diff = input1 - input2 * Q - R
    // diff验证
    val outQ = q
    val outR = R
    (outQ, outR)
  } ensuring (res => res._2 >= 0 && res._2 < input2 && input1 == input2 * res._1 + res._2)
}
