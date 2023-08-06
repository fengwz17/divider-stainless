package rocketchip

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

object Div {

  def Pow2(exp: BigInt): BigInt = {
      require(exp >= 0) 
      val result = exp match {
        case BigInt(0) => BigInt(1)
        case _ => 2 * Pow2(exp - 1)
      }
      result
  } ensuring(res => res > 0)

  @opaque  @library
  def Pow2Mul(s: BigInt, x: BigInt, y: BigInt): Unit = {
    require(x >= 0)
    require(y >= 0)
    require(s == x + y)
    decreases(x)
    x match {
      case BigInt(0) => ()
      case _ => {
        Pow2(s)                           ==:| trivial |:
        Pow2(x + y)                       ==:| trivial |:
        BigInt(2) * Pow2(x - 1 + y)       ==:| Pow2Mul(x + y - 1, x - 1, y) |:
        BigInt(2) * Pow2(x - 1) * Pow2(y) ==:| trivial |:
        Pow2(x) * Pow2(y) 
      }.qed
    }
  }.ensuring(_ => Pow2(s) == Pow2(x) * Pow2(y))

  @opaque  @library
  def lemmaPow2ModMod(a: BigInt, x: BigInt, y: BigInt): Unit = {
    require(a >= 0)
    require(x >= 0 && y >= 0)
    require(x >= y)
    val h = a / Pow2(x) 
    val l = a % Pow2(x)
    val hl = l / Pow2(y)
    val ll = l % Pow2(y)
    assert(ll < Pow2(y))
    assert(ll == l - hl * Pow2(y))
    assert(l == a - h * Pow2(x))
    assert(ll == a - h * Pow2(x) - hl * Pow2(y))
    assert((Pow2(y) * (h * Pow2(x - y) + hl) + ll) / Pow2(y) == h * Pow2(x - y) + hl) 
    Pow2Mul(x, x - y, y)
    assert(h * Pow2(x) == h * Pow2(x - y) * Pow2(y))
    {
      a % Pow2(y)                                                             ==:| trivial |:
      a - a / Pow2(y) * Pow2(y)                                               ==:| trivial |:
      a - (h * Pow2(x) + hl * Pow2(y) + ll) / Pow2(y) * Pow2(y)               ==:| Pow2Mul(x, x - y, y) |:
      a - (h * Pow2(x - y) * Pow2(y) + hl * Pow2(y) + ll) / Pow2(y) * Pow2(y) ==:| trivial |:
      a - (Pow2(y) * (h * Pow2(x - y) + hl) + ll) / Pow2(y) * Pow2(y)         ==:| trivial |:
      a - (h * Pow2(x - y) + hl) * Pow2(y)                                    ==:| trivial |:
      a - (h * Pow2(x - y) * Pow2(y) + hl * Pow2(y))                          ==:| Pow2Mul(x, x - y, y) |:
      a - h * Pow2(x) - hl * Pow2(y)                                          ==:| trivial |:
      ll                                                                      ==:| trivial |:
      l % Pow2(y)                                                             ==:| trivial |:
      a % Pow2(x) % Pow2(y)                               
    }.qed 
  }.ensuring(a % Pow2(y) == a % Pow2(x) % Pow2(y))

  @opaque @library
  def lemmaPow2Mod(t: BigInt, a: BigInt, pow2b: BigInt, c: BigInt): Unit = {
    require(c >= BigInt(0))
    require(a >= c)
    require(pow2b >= 0)
    // lemmaPow2lt(c, b)
    // require(pow2b < Pow2(c))
    require(t >= 0)
    assert(Pow2(a - c) >= 0)
    {
      ((Pow2(a - c) * Pow2(c) + pow2b)) / Pow2(c) ==:| trivial |:
      Pow2(a - c) + pow2b / Pow2(c)
    }.qed
    {
      (t * Pow2(a) + pow2b) % Pow2(c)                                                 ==:| trivial |:
      (t * Pow2(a) + pow2b) - (t * Pow2(a) + pow2b) / Pow2(c) * Pow2(c)                 ==:| Pow2Mul(a, a - c, c) |:
      (t * Pow2(a) + pow2b) - ((t * Pow2(a - c) * Pow2(c) + pow2b)) / Pow2(c) * Pow2(c) ==:| trivial |:
      (t * Pow2(a) + pow2b) - (t * Pow2(a - c) + pow2b / Pow2(c)) * Pow2(c)       ==:| trivial |:
      (t * Pow2(a) + pow2b) - t * Pow2(a - c) * Pow2(c) - pow2b / Pow2(c) * Pow2(c) ==:| Pow2Mul(a, a - c, c) |:
      (t * Pow2(a) + pow2b) - t * Pow2(a) - pow2b / Pow2(c) * Pow2(c)               ==:| trivial |:
      pow2b - pow2b / Pow2(c) * Pow2(c)                                             ==:| trivial |:
      pow2b % Pow2(c)
    }.qed
  }.ensuring((t * Pow2(a) + pow2b) % Pow2(c) == pow2b % Pow2(c))

  def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
    case true => y
    case _ => z
  }

  @library
  def Cat(a: BigInt, b: BigInt, len: BigInt): BigInt = {
    require(len >= 0 && a >= 0 && b >= 0)
    val result = len match {
      case zero if (len == 0) => a
      case _ => a * Pow2(len) + b 
    }
    result
  } ensuring(res => res >= 0)
  
  @opaque @inlineOnce @library
  def fooWhilePropShiftRegRange(shiftReg: BigInt, cnt: BigInt, len: BigInt): Unit = {
      require(len >= BigInt(1))
      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(shiftReg >= 0)

      val hl = shiftReg / Pow2(len)
      val ll = shiftReg - hl * Pow2(len)
      {
        shiftReg / Pow2(cnt)                                        ==:| trivial |:
        (ll + Pow2(len) * hl) / Pow2(cnt)                           ==:| Pow2Mul(len, cnt, len - cnt) |:
        (ll + Pow2(cnt) * Pow2(len - cnt) * hl) / Pow2(cnt)         ==:| trivial |:
        Pow2(len - cnt) * hl + ll / Pow2(cnt)                       ==:| trivial |:
        shiftReg / Pow2(len) * Pow2(len - cnt) + ll / Pow2(cnt)        
      }.qed
  }.ensuring(_ => shiftReg / Pow2(cnt) >= shiftReg / Pow2(len) * Pow2(len - cnt))

  @opaque @inlineOnce @library
  def fooWhilePropRshiftReg(a: BigInt, b: BigInt, len: BigInt, e:BigInt, cnt: BigInt, R: BigInt, shiftReg: BigInt): Unit = {
      require(len >= BigInt(1))
      require(a < Pow2(len) && a >= BigInt(0))
      require(b < Pow2(len) && b > BigInt(0))

      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(0 <= e && e <= 1)
      require(shiftReg >= 0)
      require(shiftReg / Pow2(len) >= b * e)
      require(R >= 0)
      require(R == shiftReg / Pow2(cnt))

      // val e = Mux(hi >= b, BigInt(1), BigInt(0))

      val R1 = R - b * Pow2(len - cnt) * e
      assert(R1 == shiftReg / Pow2(cnt) - b * Pow2(len - cnt) * e)

      val shiftReg1 = 2 * shiftReg - b * e * Pow2(len + 1) + e

      val cnt1 = cnt + BigInt(1)

      val h = shiftReg / Pow2(cnt)
      val l = shiftReg - h * Pow2(cnt)
      assert(shiftReg == h * Pow2(cnt) + l)
      assert(l <= Pow2(cnt) - 1)
      assert(2 * l + e < Pow2(cnt + 1))
      
      // shiftReg / Pow2(cnt) >= shiftReg / Pow2(len) * Pow2(len - cnt)
      // h >= shiftReg / Pow2(len) * Pow2(len - cnt), shifteg / Pow2(len) >= b * e
      // h >= b * e * Pow2(len - cnt)
      fooWhilePropShiftRegRange(shiftReg, cnt, len)
      assert(h - b * e * Pow2(len - cnt) >= 0)

      cnt match {
        case cnt if cnt <= len => {
          shiftReg1 / Pow2(cnt + 1)                                                                             ==:| trivial |:
          (2 * shiftReg - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)                                            ==:| trivial |:
          (2 * (h * Pow2(cnt) + l) - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)                                 ==:| trivial |:
          (h * Pow2(cnt + 1) + 2 * l + e - b * e * Pow2(len + 1)) / Pow2(cnt + 1)                               ==:| Pow2Mul(len + 1, len - cnt, cnt + 1) |:
          (h * Pow2(cnt + 1) + 2 * l + e - b * e * Pow2(len - cnt) * Pow2(cnt + 1)) / Pow2(cnt + 1)             ==:| trivial |:
          (Pow2(cnt + 1) * (h - b * e * Pow2(len - cnt)) + 2 * l + e) / Pow2(cnt + 1)                           ==:| {2 * l + e < Pow2(cnt + 1)} |:
          h - b * e * Pow2(len - cnt)                                                                           ==:| trivial |:
          (shiftReg / Pow2(cnt)) - b * e * Pow2(len - cnt)                                                      ==:| trivial |:
          R1 
        }.qed
      }      
  }.ensuring(_ => R - b * Pow2(len - cnt) * e == (2 * shiftReg - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)) 

  sealed abstract class Bits {
    def asUInt: UInt
  }

  case class UInt(val value: BigInt, val width: BigInt) extends Bits {
    require(0 < width)
    require(0 <= value && value < Pow2(width))

    def apply(idx: BigInt): Bool = {
      require(0 <= idx && idx < width)
      Bool((value / Pow2(idx)) % 2 == 1)
    }
    def apply(left: BigInt, right: BigInt): UInt = {
      require(left >= right)
      UInt((value / Pow2(right)) % Pow2(left - right + 1), left - right + 1)
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
      val carryed = this.value - that.value
      val newWidth = if (this.width > that.width) this.width else that.width
      val limt     = Pow2(newWidth)

      UInt(
        if (carryed < 0) carryed + limt else carryed,
        newWidth
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

  object UInt {
    def empty(width: BigInt): UInt = {
      UInt(BigInt(0), width)
    }
  }

  @opaque @library
  object bitLength {
    def apply(x: BigInt): BigInt = {
      def f(base: BigInt, res: BigInt): BigInt = {
        if (res > 0) {
          f(base + 1, res / 2)
        } else {
          base
        }
      }
      f(0, x)
    }
  }

  // @example
  // log2Ceil(1)  // returns 0
  // log2Ceil(2)  // returns 1
  // log2Ceil(3)  // returns 2
  // log2Ceil(4)  // returns 2
  // (in - 1).bitLength
  @opaque @library
  object log2Ceil {
    def apply(x: BigInt): BigInt = {
      require(x > 0)
      bitLength(x - 1)
    }
  }// ensuring(res => Pow2(res) >= x && Pow2(res - 1) < x)

  case class MultiplierIO(
    // in1 = UInt(dataBits.W)
    // in2 = UInt(dataBits.W)
    in1: UInt,
    in2: UInt
  )
  
  case class  MulRegs(
    divisor: UInt,
    remainder: UInt,
    count: UInt,
    R: UInt, 
    Q: UInt
  )

  case class MulDivParams(
    mulUnroll: BigInt = 1,
    divUnroll: BigInt = 1,
    mulEarlyOut: Boolean = false,
    divEarlyOut: Boolean = false,
    divEarlyOutGranularity: BigInt = 1
  )

  def inputsRequire(width: BigInt, inputs: MultiplierIO): Boolean = inputs match {
    case MultiplierIO(in1, in2) =>
      width >= 0 &&
      in1.width == width &&
      in2.width == width
  }

  def regsRequire(width: BigInt, regs: MulRegs): Boolean = regs match {
    case DividerRegs(divisor, remainder, count, R, Q) =>
      divisor.width == width &&
      shiftReg.width == 1 + width * 2 &&
      count.width == width &&
      R.width == width &&
      Q.width == width
  }

  def Div(cfg: MulDivParams, width: BigInt, nXpr: BigInt = 32, inputs: MultiplierIO, regs: MulRegs, step: BigInt): (BigInt, MulRegs) = {  
    require(width == 32 || width == 64)
    require(inputs.in1.value < Pow2(width - 1) && inputs.in1.value >= 0)
    require(inputs.in2.value < Pow2(width - 1) && inputs.in2.value > 0)
    require(cfg.divUnroll == 1)
    // require(regs.remainder >= 0) // && regs.remainder < Pow2(2 * width + 1))
    // require(regs.divisor >= 0 && regs.divisor < Pow2(width - 1))
    require(regs.count.value >= 0 && regs.count.value < width / cfg.divUnroll)
    require(regs.divisor.value == inputs.in2.value)
    require(step == BigInt(0) && regs.R.value == inputs.in1.value
      || step >= BigInt(1) && regs.R.value >= BigInt(0))
    decreases(width / cfg.divUnroll - regs.count.value)
    require(step == regs.count.value)

    require(regs.R.value + inputs.in2.value * regs.Q.value * Pow2(width - regs.count.value + 1) == 2 * inputs.in1.value)

    val w = width

    val count = regs.count

    val subtractor = 

    val R_next = regs.R - inputs.in2 * Pow2(w - count) * (1 - less)
  
    val Q_next = regs.Q << BigInt(1) + (1 - less)

    {
      R_next + inputs.in2 * Q_next * Pow2(w - (regs.count + 1) + 1) ==:| trivial |:
      (regs.R - inputs.in2 * Pow2(w - regs.count) * (1 - less)) 
        + inputs.in2 * (regs.Q * 2 + (1 - less)) * Pow2(w - regs.count) ==:| trivial |:
      regs.R - inputs.in2 * Pow2(w - regs.count) * (1 - less) + inputs.in2 * regs.Q * 2 * Pow2(w - regs.count) 
        + inputs.in2 * (1 - less) * Pow2(w - regs.count) ==:| trivial |:
      regs.R + inputs.in2 * regs.Q * Pow2(w - regs.count + 1) ==:| trivial |:
      2 * inputs.in1
    }.qed
    // count := count + 1.U
    val count_next = count + 1
    // if(eOut || count === (mulw / cfg.mulUnroll - 1).U) {
    //   state := s_done_mul
    //   resHi := isHi
    // }

    // if (io.req.fire) {
    //   state     = s_mul
    //   isHi      = cmdHi
    //   resHi     = false
    //   count     = 0
    //   divisor   = Cat(rhs_sign, rhs_in)
    //   remainder = lhs_in
    //   req       = io.req.bits
    // }
    
    // assert(nextMulReg % Pow2(w) == remainder_next % Pow2(w))

    // val loOut = result(w / 2 - 1, 0)
    // val hiOut = result(w - 1, w / 2)
    val out = result
    val regs_next = MulRegs(divisor, remainder_next, count_next, R_next, Q_next)
    val step_next = step + 1

    if (count_next < w / cfg.divUnroll) {
      Div(cfg, width, nXpr, inputs, regs_next, step_next)
    }
    else {
      (out, regs_next)
    }
  } 

/*
  def MulRun(cfg: MulDivParams, width: BigInt, nXpr: BigInt, inputs: MultiplierIO, regs: MulRegs, step: BigInt, timeout: BigInt): (BigInt, MulRegs) = {
    require(width == 32 || width == 64)
    require(inputs.in1 < Pow2(width) && inputs.in1 >= 0)
    require(inputs.in2 < Pow2(width) && inputs.in2 >= 0)
    require(cfg.mulUnroll == 1)
    require(regs.remainder >= 0 && regs.remainder < Pow2(2 * width + 1))
    require(regs.divisor >= 0 && regs.divisor < Pow2(width))
    require(regs.count >= 0)

    require(step >= 0 && step < timeout)
    require(timeout >= 1)

    val (out, regs_next) = Mul(cfg, width, nXpr, inputs, regs, step)

    // // loop-invariant tells the relation of the outputs and inputs
    // if (step < timeout) {
    //   MulRun(cfg, width, nXpr, inputs, regs_next, step + 1, timeout)
    // }
    // else {
    //   // loop-inv => post-condition
    //   (out, regs_next)
    // }
    (out, regs_next)
  } // ensuring(res => true)
*/

  // // for testing
  // // give initial values for the registers, and set timeout steps
  // def Run(): Unit = {
  //   initial
  //   MulRun()
  // }
}