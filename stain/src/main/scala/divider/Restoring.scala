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
      case false => z
    }

    def pow2(n: Int): BigInt = {
        var res = BigInt(1)
        var x = n
        while (x > 0) {
            res = res * BigInt(2)
            x = x - 1
        }
        res
    }

    // input1.length = 2n - 1, 0 <= input1 <= 2^{2n} - 1
    // input2.length = n, 0 <= input2 <= 2^{n} - 1
    // input1 = input2 * Q + R 
    def RestoringDividerUnsign(len: Int, input1: BigInt, input2: BigInt): BigInt = {
      // require(0 <= input1 && input1 <= 2.pow(2*len) - 1 && 0 <= input2 && input2 <= 2.pow(len) - 1)
      // require(input1.length <= (2*len - 1) && input2.length <= len)
      require(len <= 128 && len > 0 && input1 >= 0 && input1 <= pow2(2 * len) - 1 && input2 > 0 && input2 <= pow2(len) - 1)

      val n = len
      // val n = 8
      var R = input1
      val D = input2

      var Q = BigInt(0)

      // for (j <- 1 to n) {
      //   q(n - j) = Mux( R(j - 1) < (D << (n - j)), 0, 1)        
      //   R(j) = R(j - 1) - Mux(q(n - j) > 0, D << (n - j), 0)
      // }

      // predicate 
      // hold: enter, each loop
      // invariant /\ \neg condition => res
      // make j = n + 1
      // invariant include j, Q, R, when j = n + 1
      var j = 1
      (while (j <= n) {
        val lshift = pow2(n - j)
        val tmpD = D * lshift
        val tmpQbit = Mux( R < tmpD, 0, 1)
        val tmpR = R - Mux(tmpQbit > 0, tmpD, 0)
        val Qpow = pow2(n - j)
        Q = Q + tmpQbit * Qpow
        R = tmpR
        j = j + 1
      }) invariant(1 <= j && j <= n )
      
      val diff = input1 - input2 * Q - R
      diff
    } ensuring (res => res == 0)
}
