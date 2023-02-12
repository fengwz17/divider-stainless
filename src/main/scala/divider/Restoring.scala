package divider

object Restoring {
    def main(args: Array[String]): Unit = {
      val res = RestoringDividerUnsign(4, 5, 2)
      println("diff = " + res)
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
      // val n = 4
      var R = input1
      val D = input2
      // val q = new Array[Int](n)
      // val R = new Array[Int](n + 1)val in1 = input1.
      // val q = new Array[Int](n)
      // val R = new Array[Int](n + 1)

      // R(0) = input1
      // val zero = Int(0)
      var Q = BigInt(0)

      // println("R0 = " + input1)
      // println("D = " + input2)

      // for (j <- 1 to n) {
      //   q(n - j) = Mux( R(j - 1) < (D << (n - j)), 0, 1)        
      //   R(j) = R(j - 1) - Mux(q(n - j) > 0, D << (n - j), 0)
      // }
      var j = 1
      while (j <= n) {
        val lshift = pow2(n - j)
        val tmpD = D * lshift
        val tmpQbit = Mux( R < tmpD, 0, 1)
        val tmpR = R - Mux(tmpQbit > 0, tmpD, 0)
        val Qpow = pow2(n - j)
        Q = Q + tmpQbit * Qpow
        R = tmpR
        j = j + 1

        println("Q = " + Q)
        println("R = " + R)
        println("j = " + j)
        println("")
      }
      
      // val qStringArray = Q.map {_.toString}
      // val qString = qStringArray.reverse.mkString("")
      // println(qStringArray)
      // val qStringRe = qStringArray.reverse.tail
      // println(qStringRe)
      // val qString = qStringRe.mkString("")
      // println(qString)
      // val outQ = Integer.parseInt(qString, 2)
      // val outQInt = Int(outQ)
      // val outR = R(n)
      // val outR = R.head
      // val resArray = Array[Int](outQInt, outR)
      // println(outQInt)
      // println(outR)
      println("Q = " + Q)
      println("R = " + R)
      val diff = input1 - input2 * Q - R
      diff
      // resArray(0) = outQInt
      // resArray(1) = outR
      // println("Q = " + outQInt)
      // println("R = " + outR)
    } // ensuring (res => res == 0)
}
