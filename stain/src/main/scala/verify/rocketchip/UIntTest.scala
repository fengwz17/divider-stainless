package rocketchip

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

object UIntTest {

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
  
  // sealed abstract class Bits {
  //   def asUInt: UInt
  // }

/*
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
*/

  case class MultiplierIO(
    // in1 = UInt(dataBits.W)
    // in2 = UInt(dataBits.W)
    in1: BigInt,
    in2: BigInt
  )
  
  case class  MulRegs(
    divisor: BigInt,
    remainder: BigInt,
    count: BigInt,
    mulRegReg: BigInt
  )

  case class MulDivParams(
    mulUnroll: BigInt = 1,
    divUnroll: BigInt = 1,
    mulEarlyOut: Boolean = false,
    divEarlyOut: Boolean = false,
    divEarlyOutGranularity: BigInt = 1
  )

  @library
  def nextMulRegUpdate(mulReg: BigInt, nextMulReg: BigInt, 
    prod: BigInt, mulw: BigInt, width: BigInt, cfg: MulDivParams, mplier: BigInt, remainder: BigInt, inputs: MultiplierIO, w: BigInt): Unit = {
    {
      nextMulReg ==:| trivial |:
      prod * Pow2(mulw - cfg.mulUnroll) + mplier / Pow2(cfg.mulUnroll) ==:| trivial |:
      (remainder % Pow2(cfg.mulUnroll) * inputs.in2 + remainder / Pow2(w + 1)) * Pow2(mulw - cfg.mulUnroll)
        + (remainder % Pow2(width)) / Pow2(cfg.mulUnroll) ==:| trivial |:
      (mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)) * Pow2(mulw- cfg.mulUnroll) 
        + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll)
    }.qed
  }.ensuring(nextMulReg == (mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)) * Pow2(mulw- cfg.mulUnroll) 
        + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll))

  @library
  def MulRegRemainder(mulReg: BigInt, remainder: BigInt, w: BigInt): Unit = {
    {
      remainder / Pow2(w + 1) ==:| trivial |:
      ((mulReg / Pow2(w)) * Pow2(w + 1) + mulReg % Pow2(w)) / Pow2(w + 1) ==:| trivial |:
      mulReg / Pow2(w)
    }.qed

    {
      remainder / Pow2(w) ==:| trivial |:
      ((mulReg / Pow2(w)) * Pow2(w + 1) + mulReg % Pow2(w)) / Pow2(w) ==:| trivial |:
      ((mulReg / Pow2(w)) * Pow2(w) * BigInt(2) + mulReg % Pow2(w)) / Pow2(w) ==:| trivial |:
      (mulReg / Pow2(w)) * 2
    }.qed
    
    {
      remainder % Pow2(w) ==:| trivial |:
      remainder - remainder / Pow2(w) * Pow2(w) ==:| trivial |:
      remainder - mulReg / Pow2(w) * 2 * Pow2(w) ==:| trivial |:
      remainder - mulReg / Pow2(w) * Pow2(w + 1) ==:| trivial |:
      mulReg % Pow2(w) 
    }.qed

    {
      mulReg / Pow2(w) ==:| trivial |:
      ((remainder / Pow2(w + 1)) * Pow2(w) + remainder % Pow2(w)) / Pow2(w) ==:| trivial |:
      remainder / Pow2(w + 1)
    }.qed
  }.ensuring(remainder / Pow2(w + 1) == mulReg / Pow2(w) && remainder / Pow2(w) == mulReg / Pow2(w) * 2
    && remainder % Pow2(w) == mulReg % Pow2(w) && remainder / Pow2(w) == mulReg / Pow2(w + 1))

  @library
  // mulReg % Pow2(w - step * cfg.mulUnroll) == inputs.in1 / Pow2(step * cfg.mulUnroll) 
  def mulReg_lower_bits(nextMulReg: BigInt, mulReg: BigInt, w: BigInt, cfg: MulDivParams, step: BigInt, inputs: MultiplierIO): Unit = { 
    require(w == 32 || w == 64)
    require(cfg.mulUnroll == 1)
    require(step >= 0 && step < w / cfg.mulUnroll)
    require(mulReg >= 0)
    require(nextMulReg >= 0)
    require(nextMulReg == (mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)) * Pow2(w - cfg.mulUnroll) 
        + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll))
    require(inputs.in1 >= 0 && inputs.in1 < Pow2(w))
    require(mulReg % Pow2(w - step * cfg.mulUnroll) == inputs.in1 / Pow2(step * cfg.mulUnroll))

    val h = mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)
    val l = (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll)
    {
      h ==:| trivial |:
      mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)
    }.qed

    {
      nextMulReg % Pow2(w - (step + 1) * cfg.mulUnroll) ==:| trivial |:
      ((mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)) * Pow2(w - cfg.mulUnroll) + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll)) 
        % Pow2(w - (step + 1) * cfg.mulUnroll) // ==:| {h == mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)} |:
      // (h * Pow2(w - cfg.mulUnroll) + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll)) % Pow2(w - (step + 1) * cfg.mulUnroll)
    }.qed
    {
      (mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)) * Pow2(w - cfg.mulUnroll) + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll) ==:| trivial |:
      h * Pow2(w - cfg.mulUnroll) + l
    }.qed
    {
      ((mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)) * Pow2(w - cfg.mulUnroll) + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll)) 
        % Pow2(w - (step + 1) * cfg.mulUnroll) ==:| trivial |:
      (h * Pow2(w - cfg.mulUnroll) + l) % Pow2(w - (step + 1) * cfg.mulUnroll)
    }.qed
    {
      nextMulReg % Pow2(w - (step + 1) * cfg.mulUnroll) ==:| trivial |:
      ((mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)) * Pow2(w - cfg.mulUnroll) + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll)) 
        % Pow2(w - (step + 1) * cfg.mulUnroll)          ==:| trivial |:
      (h * Pow2(w - cfg.mulUnroll) + l) % Pow2(w - (step + 1) * cfg.mulUnroll) ==:| lemmaPow2Mod(h, w - cfg.mulUnroll, l, w - (step + 1) * cfg.mulUnroll) |:
      l % Pow2(w - (step + 1) * cfg.mulUnroll)
    }.qed

    // check
    {
      (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll) ==:| trivial |:
      mulReg % Pow2(w - step * cfg.mulUnroll) / Pow2(cfg.mulUnroll) ==:| trivial |:
      inputs.in1 / Pow2(step * cfg.mulUnroll) / Pow2(cfg.mulUnroll) ==:| trivial |:
      inputs.in1 / Pow2(step * cfg.mulUnroll + cfg.mulUnroll)       ==:| trivial |:
      inputs.in1 / Pow2((step + 1) * cfg.mulUnroll)
    }.qed
  }.ensuring(nextMulReg % Pow2(w - (step + 1) * cfg.mulUnroll) == inputs.in1 / Pow2((step + 1) * cfg.mulUnroll))

  @library
  // mulReg / Pow2(w - step * cfg.mulUnroll) == inputs.in1 % Pow2(step * cfg.mulUnroll) * inputs.in2 
  def mulReg_higher_bits(nextMulReg: BigInt, mulReg: BigInt, w: BigInt, cfg: MulDivParams, step: BigInt, inputs: MultiplierIO): Unit = { 
    require(w == 32 || w == 64)
    require(cfg.mulUnroll == 1)
    require(step >= 0 && step < w / cfg.mulUnroll)
    require(mulReg >= 0)
    require(nextMulReg >= 0)
    require(nextMulReg == (mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)) * Pow2(w - cfg.mulUnroll) 
        + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll))
    require(inputs.in1 >= 0 && inputs.in1 < Pow2(w))
    require(mulReg / Pow2(w - step * cfg.mulUnroll) == inputs.in1 % Pow2(step * cfg.mulUnroll) * inputs.in2)
    require(mulReg % Pow2(w - step * cfg.mulUnroll) == inputs.in1 / Pow2(step * cfg.mulUnroll))

    // check
    {
      nextMulReg % Pow2(cfg.mulUnroll) * inputs.in2 ==:| trivial |:
      nextMulReg % Pow2(w - step * cfg.mulUnroll) % Pow2(cfg.mulUnroll) * inputs.in2 ==:| trivial |:
      inputs.in1 / Pow2(step * cfg.mulUnroll) % Pow2(cfg.mulUnroll) * inputs.in2
    }.qed

    val h = mulReg / Pow2(w - step * cfg.mulUnroll)
    val l = mulReg - h * Pow2(w - step * cfg.mulUnroll)

    {
      mulReg / Pow2(w) ==:| trivial |:
      mulReg / Pow2(w - step * cfg.mulUnroll) / Pow2(step * cfg.mulUnroll) ==:| trivial |:
      h / Pow2(step * cfg.mulUnroll)
    }

    val hh = h / Pow2(step * cfg.mulUnroll)
    val hl = h - hh * Pow2(step * cfg.mulUnroll)

    {
      mulReg % Pow2(w) / Pow2(cfg.mulUnroll) ==:| trivial |:
      hl * Pow2(w - (step + 1) * cfg.mulUnroll) + l / Pow2(cfg.mulUnroll)
    }.qed
    
    {
      nextMulReg / Pow2(w - (step + 1) * cfg.mulUnroll) ==:| trivial |:
      (inputs.in1 / Pow2(step * cfg.mulUnroll) % Pow2(cfg.mulUnroll) * inputs.in2 + h / Pow2(step * cfg.mulUnroll)) * Pow2(step * cfg.mulUnroll)
        + h % Pow2(step * cfg.mulUnroll) ==:| trivial |:
      inputs.in1 / Pow2(step * cfg.mulUnroll) % Pow2(cfg.mulUnroll) * inputs.in2 * Pow2(step * cfg.mulUnroll)
        + h ==:| trivial |:
      inputs.in1 / Pow2(step * cfg.mulUnroll) % Pow2(cfg.mulUnroll) * inputs.in2 * Pow2(step * cfg.mulUnroll)
        + inputs.in1 % Pow2(step * cfg.mulUnroll) * inputs.in2 ==:| trivial |:
      (inputs.in1 / Pow2(step * cfg.mulUnroll) % Pow2(cfg.mulUnroll) + inputs.in1 % Pow2(step * cfg.mulUnroll)) * inputs.in2 ==:| trivial |:
      inputs.in1 % Pow2((step + 1) * cfg.mulUnroll) * inputs.in2
    }.qed

  }.ensuring(nextMulReg / Pow2(w - (step + 1) * cfg.mulUnroll) == inputs.in1 % Pow2((step + 1) * cfg.mulUnroll) * inputs.in2)


  def Mul(cfg: MulDivParams, width: BigInt, nXpr: BigInt = 32, inputs: MultiplierIO, regs: MulRegs, step: BigInt): (BigInt, MulRegs) = {  
    require(width == 32 || width == 64)
    require(inputs.in1 < Pow2(width - 1) && inputs.in1 >= 0)
    require(inputs.in2 < Pow2(width - 1) && inputs.in2 >= 0)
    require(cfg.mulUnroll == 1)
    // require(regs.remainder >= 0) // && regs.remainder < Pow2(2 * width + 1))
    // require(regs.divisor >= 0 && regs.divisor < Pow2(width - 1))
    require(regs.count >= 0 && regs.count < width / cfg.mulUnroll)

    require(step == BigInt(0) && regs.remainder == inputs.in1 && regs.divisor == inputs.in2 
      || step >= BigInt(1) && regs.remainder >= BigInt(0) && regs.divisor == inputs.in2)
    decreases(width / cfg.mulUnroll - regs.count)
    require(step == regs.count)
    require(regs.mulRegReg == regs.remainder % Pow2(width) + regs.remainder / Pow2(width + 1) * Pow2(width))
    require(regs.mulRegReg % Pow2(width - step * cfg.mulUnroll) == inputs.in1 / Pow2(step * cfg.mulUnroll))
   
    // require(cfg.divUnroll == 0)
    // require(mulEarlyOut == false)
    // require(divEarlyOut == false)
    // require(isHi == false)

    // def minDivLatency = (cfg.divUnroll > 0).option(if (cfg.divEarlyOut) 3 else 1 + w / cfg.divUnroll)
    // def minMulLatency = (cfg.mulUnroll > 0).option(if (cfg.mulEarlyOut) 2 else w / cfg.mulUnroll)
    // def minLatency: Int       = (minDivLatency ++ minMulLatency).min

    // val io = IO(new MultiplierIO(width, log2Up(nXpr)))

    // val w        = io.req.bits.in1.getWidth
    val w = width
    val mulw     = w

    // val count = log2Ceil(mulw / cfg.mulUnroll)
    val count = regs.count
    val divisor = regs.divisor
    val remainder = regs.remainder

    val (lhs_in, lhs_sign) = (inputs.in1, false)
    val (rhs_in, rhs_sign) = (inputs.in2, false)

    // val result = Mux(resHi, remainder(2 * w, w + 1), remainder(w - 1, 0))
    val result = remainder % Pow2(w)

    // val mulReg     = Cat(remainder(2 * mulw + 1, w + 1), remainder(w - 1, 0))
    val mulReg = Cat(remainder / Pow2(w + 1), remainder % Pow2(w), w)
    assert(mulReg == regs.mulRegReg)

    // val mplierSign = remainder(w)
    // val mplierSign = (remainder / Pow2(w)) % 2
    val mplierSign = BigInt(0)

    // val mplier     = mulReg(mulw - 1, 0)
    val mplier = mulReg % Pow2(mulw)

    // val accum      = mulReg(2 * mulw, mulw)
    val accum = mulReg / Pow2(mulw)
    {
      accum ==:| trivial |:
      mulReg / Pow2(mulw) ==:| trivial |:
      mulReg / Pow2(w) ==:| trivial |:
      (remainder / Pow2(w + 1) * Pow2(w) + remainder % Pow2(w)) / Pow2(w) ==:| trivial |:
      remainder / Pow2(w + 1)
    }.qed

    {
      mplier ==:| trivial |:
      mulReg % Pow2(mulw) ==:| trivial |:
      mulReg % Pow2(w) ==:| trivial |:
      mulReg - mulReg / Pow2(w) * Pow2(w) ==:| trivial |:
      mulReg - remainder / Pow2(w + 1) * Pow2(w) ==:| trivial |:
      remainder / Pow2(w + 1) * Pow2(w) + remainder % Pow2(w) - remainder / Pow2(w + 1) * Pow2(w) ==:| trivial |:
      remainder % Pow2(w)
    }.qed

    // assert(mplier == remainder % Pow2(w))
    // assert(accum == remainder / Pow2(w + 1))

    val mpcand     = divisor
    
    // val prod       = Cat(mplierSign, mplier(cfg.mulUnroll - 1, 0)) * mpcand + accum
    val prod = Cat(mplierSign, mplier % Pow2(cfg.mulUnroll), cfg.mulUnroll) * mpcand + accum

    {
      remainder % Pow2(width) % Pow2(cfg.mulUnroll)
        ==:| lemmaPow2ModMod(remainder, width, cfg.mulUnroll) |:
      remainder % Pow2(cfg.mulUnroll)
    }.qed

    {
      prod ==:| trivial |:
      mplier % Pow2(cfg.mulUnroll) * mpcand + accum ==:| trivial |:
      mplier % Pow2(cfg.mulUnroll) * inputs.in2 + remainder / Pow2(w + 1) ==:| trivial |:
      remainder % Pow2(width) % Pow2(cfg.mulUnroll) * inputs.in2 + remainder / Pow2(w + 1) 
        ==:| trivial |:
      remainder % Pow2(cfg.mulUnroll) * inputs.in2 + remainder / Pow2(w + 1)
    }.qed

    // val nextMulReg = Cat(prod, mplier(mulw - 1, cfg.mulUnroll))
    val nextMulReg = Cat(prod, mplier / Pow2(cfg.mulUnroll), mulw - cfg.mulUnroll)

    // val nextMplierSign = count === (mulw / cfg.mulUnroll - 2) && neg_out
    val nextMplierSign = false

    // val eOutMask = ((BigInt(-1) << mulw) >> (count * cfg.mulUnroll)(log2Up(mulw) - 1, 0))(mulw - 1, 0)
    // val eOut = (cfg.mulEarlyOut) && count =/= (mulw / cfg.mulUnroll - 1).U && count =/= 0.U &&
    // !isHi && (mplier & remainder~eOutMask) === 0.U
    // val eOutRes     = (mulReg >> (mulw.U - count * cfg.mulUnroll.U)(log2Up(mulw) - 1, 0))
    val eOut = false
    val eOutRes = false

    // val nextMulReg1 = Cat(nextMulReg(2 * mulw, mulw), Mux(eOut, eOutRes, nextMulReg)(mulw - 1, 0))
    val nextMulReg1 = Cat(nextMulReg / Pow2(mulw), nextMulReg % Pow2(mulw), mulw)
    // assert(nextMulReg1 == (nextMulReg / mulw) * Pow2(mulw) + nextMulReg % Pow2(mulw))

    assert(nextMulReg1 == nextMulReg)

    // remainder := Cat(nextMulReg1 >> w, nextMplierSign, nextMulReg1(w - 1, 0))
    // val remainder_next = Cat(nextMulReg1 / Pow2(w), nextMplierSign, nextMulReg1 % Pow2(w))
    val remainder_next = (nextMulReg1 / Pow2(w)) * Pow2(w + 1) + nextMulReg1 % Pow2(w)

    // {
    //   remainder_next / Pow2(w + 1) ==:| trivial |:
    //   ((nextMulReg1 / Pow2(w)) * Pow2(w + 1) + nextMulReg1 % Pow2(w)) / Pow2(w + 1) ==:| trivial |:
    //   nextMulReg1 / Pow2(w)
    // }.qed
    {
      remainder_next / Pow2(w + 1) ==:| MulRegRemainder(nextMulReg1, remainder_next, w) |:
      nextMulReg1 / Pow2(w)
    }.qed

    {
      remainder_next / Pow2(w) ==:| MulRegRemainder(nextMulReg1, remainder_next, w) |:
      (nextMulReg1 / Pow2(w)) * 2
    }.qed
    
    {
      remainder_next % Pow2(w) ==:| MulRegRemainder(nextMulReg1, remainder_next, w) |:
      nextMulReg1 % Pow2(w) 
    }.qed

    {
      mulReg / Pow2(w) ==:| MulRegRemainder(mulReg, remainder, w) |:
      remainder / Pow2(w + 1)
    }.qed

    {
      mulReg % Pow2(w) ==:| MulRegRemainder(mulReg, remainder, w) |:
      remainder % Pow2(w)
    }.qed

    {
      nextMulReg ==:| nextMulRegUpdate(mulReg, nextMulReg, prod, mulw, width, cfg, mplier, remainder, inputs, w) |:
      (mulReg % Pow2(cfg.mulUnroll) * inputs.in2 + mulReg / Pow2(w)) * Pow2(mulw - cfg.mulUnroll) 
        + (mulReg % Pow2(w)) / Pow2(cfg.mulUnroll)
    }.qed
    
    {
      remainder_next % Pow2(w) + remainder_next / Pow2(w + 1) * Pow2(w)  ==:| trivial |:
      nextMulReg1 % Pow2(w) + nextMulReg1 / Pow2(w) * Pow2(w)            ==:| trivial |:
      nextMulReg % Pow2(w) + nextMulReg / Pow2(w) * Pow2(w)              ==:| trivial |:
      nextMulReg
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
    val regs_next = MulRegs(divisor, remainder_next, count_next, nextMulReg)
    val step_next = step + 1

    // mulReg % Pow2(w - step * cfg.mulUnroll) == inputs.in1 / Pow2(step * cfg.mulUnroll) 
    {
      regs_next.mulRegReg % Pow2(width - step_next * cfg.mulUnroll) ==:| trivial |:
      nextMulReg % Pow2(w - (step + 1) * cfg.mulUnroll) ==:| mulReg_lower_bits(nextMulReg, mulReg, w, cfg, step, inputs) |:
      inputs.in1 / Pow2((step + 1) * cfg.mulUnroll)     ==:| trivial |:
      inputs.in1 / Pow2(step_next * cfg.mulUnroll)
    }.qed

    // nextMulReg / Pow2(w - (step + 1) * cfg.mulUnroll) == inputs.in1 % Pow2((step + 1) * cfg.mulUnroll) * inputs.in2)
    {
      regs_next.mulRegReg / Pow2(width - step_next * cfg.mulUnroll) ==:| trivial |:
      nextMulReg % Pow2(w - (step + 1) * cfg.mulUnroll) ==:| mulReg_higher_bits(nextMulReg, mulReg, w, cfg, step, inputs) |:
      inputs.in1 / Pow2((step + 1) * cfg.mulUnroll)     ==:| trivial |:
      inputs.in1 % Pow2(step_next * cfg.mulUnroll) * inputs.in2
    }.qed

    {
      regs_next.mulRegReg ==:| trivial |:
      inputs.in1 % Pow2(step_next * cfg.mulUnroll) * inputs.in2 + inputs.in1 / Pow2(step_next * cfg.mulUnroll)
    }.qed 

    if (count_next < mulw / cfg.mulUnroll) {
      Mul(cfg, width, nXpr, inputs, regs_next, step_next)
    }
    else {
      assert(width == step_next * cfg.mulUnroll)

      {
        regs_next.mulRegReg ==:| trivial |:
        inputs.in1 % Pow2(width) * inputs.in2 + inputs.in1 / Pow2(width) ==:| trivial |:
        inputs.in1 * inputs.in2
      }.qed
      
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