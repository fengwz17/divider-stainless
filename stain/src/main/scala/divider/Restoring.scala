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

    def verify(len: BigInt, a: BigInt, b: BigInt): BigInt = {
      // require(a < b * pow2(len))
      // require(b > 0)
      var n = len
      val result = b * pow2(2, 0)
      result
    } // ensuring(res => a < res)

    // input1.length = 2n, 0 <= input1 <= input2 * 2^{n} - 1
    // input2.length = n, 0 <= input2 <= 2^{n} - 1
    // input1 = input2 * Q + R 
    // pow2 = pow2(2, len)
    def RestoringDividerUnsign(len: BigInt, input1: BigInt, input2: BigInt): (BigInt, BigInt) = {
      require(len >= 1 && input1 >= 0 && input1 < input2 * pow2(2, len) && input2 > 0 && input2 < pow2(2, len))

      // val n = len
      // val n = 4
      var R = input1
      // var lshift = pow2(2, n)
      // var lshift = pow2

      // val k = pow2(2, n - 1)
      // assert(lshift == 2 * k)
      // assert(lshift > 0)
     
      // var D = lshift * input2

      var Q = BigInt(0)

      // pre-condition => invariant
      // invariant hold in loop
      // invariant \wedge \neg loop-condition => res
      // invariant include j, Q, R, when exit loop (j = 0)
      var j = len
      var Qbit = BigInt(0)
      var lshift = pow2(2, j)
      (while (j >= BigInt(1)) {
        j = j - 1
        // lshift = lshift / 2 
        // lshift = pow2(2, j - 1)
        // var D = input2 * lshift
        Qbit = Mux(R >= input2 * pow2(2, j), BigInt(1), BigInt(0))   
        R = R - Qbit * input2 * pow2(2, j)
        // if (R >= input2 * pow2(2, j)) 
        //   R = R - input2 * pow2(2, j)
        Q = Q + Qbit * pow2(2, j)
      }) invariant(j >= 0 && R < input2 * pow2(2, j) && R >= 0 && R == input1 - input2 * Q) // && && (((tmpR < tmpD) && (Qbit == 0)) || ((tmpR >= tmpD) && (Qbit == 1))) && (((Qbit == 1) && (R == tmpR - tmpD)) || ((Qbit == 0) && (R == tmpR)))) // && Q >= 0 && Q <= pow2(n) - pow2(j - 1)) 
      
      // val diff = input1 - input2 * Q - R
      // diff验证
      (Q, R)
    } ensuring (res => res._2 >= 0 && res._2 < input2 && input1 == input2 * res._1 + res._2)
}
