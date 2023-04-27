import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import stainless.lang.Real

def Pow2(exp: BigInt): BigInt = {
    require(exp >= 0) 
    val result = exp match {
    case BigInt(0) => BigInt(1)
    case _ => 2 * Pow2(exp - 1)
    }
    result
} ensuring(res => res > 0)

@opaque @inlineOnce
def Pow2Mul(x: BigInt, y: BigInt): Unit = {
    require(x >= 0)
    require(y >= 0)
    decreases(x)
    x match {
        case BigInt(0) => ()
        case _ => {
        Pow2(x + y)                       ==:| trivial  |:
        BigInt(2) * Pow2(x - 1 + y)       ==:| Pow2Mul(x - 1, y)  |:
        BigInt(2) * Pow2(x - 1) * Pow2(y) ==:| trivial  |:
        Pow2(x) * Pow2(y) 
        }.qed
    }
}.ensuring(_ => Pow2(x + y) == Pow2(x) * Pow2(y))

def Pow2MulTest(a: BigInt, b: BigInt): (BigInt, BigInt) = {
    require(a >= 0 && b >= 0)
    // Pow2Mul(a, b)
    val p1 = Pow2(a + b)
    val p2 = Pow2(a)
    val p3 = Pow2(b)
    val mul = p2 * p3
    
    (p1, mul)
} ensuring(res => res._1 == res._2)