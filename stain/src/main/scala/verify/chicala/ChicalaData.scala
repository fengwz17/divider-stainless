package chicala

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

@dropVCs
sealed abstract class Bits {
  def asUInt: UInt
}

@dropVCs
case class UInt(val value: BigInt, val width: BigInt) extends Bits {
  require(0 < width)
  require(0 <= value && value < Pow2(width))

  def apply(idx: BigInt): Bool = {
    require(0 <= idx && idx < width)
    Bool((value / Pow2(idx)) % 2 == 1)
  }
  def apply(left: BigInt, right: BigInt): UInt = {
    require(left >= right)
    UInt((value / Pow2(right)) % Pow2(left), left - right + 1)
  }

  def getWidth: BigInt = width
  def asUInt: UInt     = this
  def asBool: Bool = {
    require(width == 1)
    Bool(if (value == 1) true else false)
  }

  // Unary

  def unary_- : UInt = {
    UInt(Pow2(width) - value, width)
  }
  def unary_~ : UInt = {
    def reverseUInt(u: UInt): UInt = {
      def f(result: BigInt, width: BigInt, bits: BigInt): BigInt = {
        if (width > 0) {
          f(result * 2 + bits % 2, width - 1, bits / 2)
        } else {
          result
        }
      }
      UInt(f(0, u.value, u.width), u.width)
    }
    def reverseFlipUInt(u: UInt): UInt = {
      def f(result: BigInt, width: BigInt, bits: BigInt): BigInt = {
        if (width > 0) {
          f(result * 2 + (bits + 1) % 2, width - 1, bits / 2)
        } else {
          result
        }
      }
      UInt(f(0, u.value, u.width), u.width)
    }
    reverseUInt(reverseFlipUInt(this))
  }

  // Binary

  def +(that: UInt): UInt = {
    val carryed  = this.value + that.value
    val newWidth = if (this.width > that.width) this.width else that.width
    val limt     = Pow2(newWidth)

    UInt(
      if (carryed > limt) carryed - limt else carryed,
      newWidth
    )
  }
  def -(that: UInt): UInt = {
    UInt(
      this.value - that.value,
      (if (this.width > that.width) this.width else that.width) + 1
    )
  }
  def <<(that: UInt): UInt = {
    UInt(this.value * Pow2(that.value), this.width + Pow2(that.width) - 1)
  }
  def <<(that: BigInt): UInt = {
    UInt(this.value * Pow2(that), this.width + that)
  }

  // Binary compire
  def ===(that: UInt): Bool = {
    Bool(this.value == that.value)
  }
  def >=(that: UInt): Bool = {
    Bool(this.value >= that.value)
  }
}

@dropVCs
object UInt {
  def empty(width: BigInt): UInt = {
    UInt(BigInt(0), width)
  }
}

@dropVCs
case class Bool(val value: Boolean) extends Bits {
  def asUInt: UInt = {
    if (value) {
      UInt(1, 1)
    } else {
      UInt(0, 1)
    }
  }

  def unary_! : Bool = {
    Bool(!value)
  }
  def unary_~ : Bool = {
    Bool(!value)
  }

  def &(that: Bool): Bool = {
    Bool(this.value & that.value)
  }
  def |(that: Bool): Bool = {
    Bool(this.value | that.value)
  }
  def ^(that: Bool): Bool = {
    Bool(this.value ^ that.value)
  }
  def &&(that: Bool): Bool = {
    Bool(this.value && that.value)
  }
}

object Bool {
  def empty(): Bool = {
    Bool(false)
  }
}

@dropVCs
case class Lit(value: BigInt, width: BigInt) {
  def U: UInt = UInt(value, width)
}

@dropVCs
object Lit {
  def apply(value: BigInt): Lit = {
    require(0 <= value)
    if (value == 0) {
      Lit(0, 1)
    } else {
      Lit(value, log2Ceil(value + 1))
    }
  }
}
