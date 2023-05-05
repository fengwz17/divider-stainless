package verify

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check
import Chisel.Bool
import chisel3.util.MuxLookup

object TestUint {
  // val MAXINT = 2147483647

  def Pow2(exp: BigInt): BigInt = {
    require(exp >= 0) 
    val result = exp match {
      case 0 => BigInt(1)
      case _ => 2 * Pow2(exp - 1)
    }
    result
  } ensuring(res => res > 0)

  def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
    case true => y
    case _ => z
  }

  def getWidth(x: BigInt): BigInt = {
    require(x >= 0)
    val result = x match {
      case 0 => 1
      case 1 => 1
      case _ => 1 + getWidth(x / 2)
    }
    result
  } ensuring(res => res > 0)

  @library
  def Log2(x: UInt): UInt = {
    require(x.value >= 0)
    // val result = x.value match {
    //   case 1 => 0
    //   case _ => 1 + Log2(x / 2)
    // }
    // result
    val width = x.width
    val result = UInt(width - 1, getWidth(width))
  } ensuring(res => res.value == x.width - 1)

  case class UInt(val value: BigInt, val width: BigInt) {
    require(width >= 0)
    require(value >= 0)
    require(value < Pow2(width))
    
    def apply(i: BigInt): BigInt = {
      require(i >= 0)
      require(i < width)
      (this.value / Pow2(i)) % 2
    }
    def apply(hi: BigInt, lo: BigInt) = {
      require(hi >= lo)
      require(hi < width)
      require(lo >= 0)
      UInt((this.value / Pow2(lo)) % Pow2(hi - lo + 1), hi - lo + 1)
    }
    def apply(x: BigInt): BigInt = {
      require(x >= 0)
      UInt(x, getWidth(x))
    }

    // assuming no overflow
    def +(that: UInt): UInt = {
      UInt((this.value + that.value),
      (if (this.width > that.width) this.width else that.width)
      )
    }
    def -(that: UInt): UInt = {
      UInt((this.value - that.value),
      (if (this.width > that.width) this.width else that.width)
      )
    }
    def >=(that: UInt): Boolean = {
      if (this.value >= that.value) true else false
    }
    def <<(that: Int): UInt = {
      UInt((this.value * Pow2(that.value)),
      this.width + that
      )
    }
    def neg: UInt = {
      UInt(-this.value,
      this.width
      )
    }
    def Cat(that: UInt): UInt = {
      UInt((this.value * Pow2(that.width)) + that.value,
      this.width + that.width
      )
    }
  }

  def NutShellDivider(len: BigInt, in1: UInt, in2: UInt, sign: Boolean): (UInt, UInt) = {
    require(len >= 1)
    require(in1.width == len)
    require(in2.width == len)
    
    def abs(a: UInt, sign: Boolean): (Boolean, UInt) = {
      val sign_value = if (sign == true) BigInt(1) else BigInt(0)
      val s = a(len - 1) * sign_value
      val s_bool = if (s == 1) true else false
      (s_bool, Mux(s_bool, neg(a), a)) 
    }

    val stateList = "s_idle" :: "s_log2" :: "s_shift" :: "s_compute" :: "s_finish" :: Nil
    val state = stateList(5)
    assert(state == "s_idle")
    val newReq = (state == "s_idle")

    val (a, b) = (in1, in2)
    val divBy0 = b.value === BigInt(0)

    val shiftReg = UInt(BigInt(0), 1 + len * 2)
    val hi = shiftReg(len * 2, len)
    val lo = shiftReg(len - 1, 0)

    val (aSign, aVal) = abs(a, sign)
    val (bSign, bVal) = abs(b, sign)
    val aSignReg = aSign
    val qSignReg = aSign ^ bSign && !divBy0
    val bReg = bVal
    val aValx2Reg = Cat(aVal, UInt(BigInt(0), 1))
    
    val cnt = UInt(BigInt(0), len)
    if (newReq) {
      state_next = "s_log2"
    } else if (state == "s_log2") {
      val canSkipShift = (UInt(len) + Log2(bReg)) - Log2(aValx2Reg)
      cnt_next = Mux(divBy0, UInt(BigInt(0), 1), Mux(canSkipShift >= UInt(len - 1), UInt(len - 1), canSkipShift))
      state_next = "s_compute"
    }

    var shiftReg = aValx2Reg

    var cnt: UInt = (BigInt(0), len)

    var R: UInt = shiftReg
    var Q: UInt = (BigInt(0), len)
    
    val t: (BigInt, BigInt, BigInt, BigInt) = if (cnt.value <= len - 1) {
      fooWhile(len, a, b, cnt, R, Q, shiftReg)
    } else {
      (cnt, R, Q, shiftReg)
    }

    val hi = t._4(len * 2, len)
    // val lo = t._4 - hi * Pow2(len)
    val lo = t._4(len - 1, 0)

    val r = hi(len, 1)
    val resQ = lo
    val resR = r 
    (resQ, resR)
  } ensuring(res => in1 == in2 * res._1 + res._2)
}