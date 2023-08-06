package rocketchip

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check
import chisel3.util.log2Ceil
import chisel3.chiselTypeOf

object Mul {

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
  
  @library
  def bitLength(x: BigInt): BigInt = {
    def f(base: BigInt, res: BigInt): BigInt = {
      if (res > 0) {
        f(base + 1, res / 2)
      } else {
        base
      }
    }
    f(0, x)
  }

  // @example
  // log2Ceil(1)  // returns 0
  // log2Ceil(2)  // returns 1
  // log2Ceil(3)  // returns 2
  // log2Ceil(4)  // returns 2
  // (in - 1).bitLength
  @library
  def log2Ceil(x: BigInt): BigInt = {
    require(x > 0)
    result = bitLength(x - 1)
  } // ensuring(res => Pow2(res) >= x && Pow2(res - 1) < x)

  class MultiplierReq(dataBits: Int, tagBits: Int) extends Bundle {
    val fn  = UInt(4.W) // aluFn.SZ_ALU_FN
    val dw  = UInt(1.W)
    val in1 = UInt(dataBits.W)
    val in2 = UInt(dataBits.W)
    val tag = UInt(tagBits.W)
  }

  class MultiplierResp(dataBits: Int, tagBits: Int) extends Bundle {
    val data = UInt(dataBits.W)
    val tag  = UInt(tagBits.W)
  } 

  class MultiplierIO(val dataBits: Int, val tagBits: Int) extends Bundle {
    val req  = Flipped(Decoupled(new MultiplierReq(dataBits, tagBits)))
    val resp = Decoupled(new MultiplierResp(dataBits, tagBits))
  }

  case class MulDivParams(
    mulUnroll: Int = 1,
    divUnroll: Int = 1,
    mulEarlyOut: Boolean = false,
    divEarlyOut: Boolean = false,
    divEarlyOutGranularity: Int = 1
  )
  
  def option[T](z: => T): Option[T] = if (x) Some(z) else None

  def Mul(cfg: MulDivParams, width: BigInt, nXpr: BigInt = 32): (BigInt, BigInt) = {  
    // require(width == 32 || width == 64)
    // require(in1 < Pow2(width) && in1 >= 0)
    // require(in2 < Pow2(width) && in2 >= 0)
    require(cfg.mulUnroll == 1)
    require(cfg.divUnroll == 0)
    require(mulEarlyOut == false)
    require(divEarlyOut == false)

    // def minDivLatency = (cfg.divUnroll > 0).option(if (cfg.divEarlyOut) 3 else 1 + w / cfg.divUnroll)
    // def minMulLatency = (cfg.mulUnroll > 0).option(if (cfg.mulEarlyOut) 2 else w / cfg.mulUnroll)
    // def minLatency: Int       = (minDivLatency ++ minMulLatency).min

    val io = IO(new MultiplierIO(width, log2Up(nXpr)))
    require(io.req.bits.dw == true)

    val w        = io.req.bits.in1.getWidth

    /*
    *  make mulw the smallest integer multiple of mulUnroll greater than w
    *  e.g. w = 32, mulUnroll = 2, 4, 8, 16, 32 => mulw = 32; mulUnroll = 9 => mulw = 36
    */
    val mulw     = if (cfg.mulUnroll == 0) w else (w + cfg.mulUnroll - 1) / cfg.mulUnroll * cfg.mulUnroll
    val fastMulW = if (cfg.mulUnroll == 0) false else w / 2 > cfg.mulUnroll && w % (2 * cfg.mulUnroll) == 0

    val s_list = s_ready :: s_mul :: s_done_mul :: Nil
    val state = RegInit(s_ready)

    val req = Reg(chiselTypeOf(io.req.bits))
    val count = Reg(
      UInt(
        log2Ceil(
          ((cfg.divUnroll != 0).option(w / cfg.divUnroll + 1).toSeq ++
            (cfg.mulUnroll != 0).option(mulw / cfg.mulUnroll)).reduce(_ max _)
        ).W
      )
    )

    val neg_out   = Reg(Bool())
    val isHi      = Reg(Bool())
    val resHi     = Reg(Bool())
    val divisor   = Reg(Bits((w + 1).W))        // div only needs w bits
    val remainder = Reg(Bits((2 * mulw + 2).W)) // div only needs 2*w+1 bits

    val cmdMul, cmdHi, lhsSigned, rhsSigned = WireInit(false.B)
    if (cfg.mulUnroll != 0) {
      switch(io.req.bits.fn) {
        is(0.U) { // aluFn.FN_MUL
          cmdMul    := true.B
          cmdHi     := false.B
          lhsSigned := false.B
          rhsSigned := false.B
        }
      }
    }

    require(w == 32 || w == 64)

    // w == 32 return false
    // w == 64 if dw == false return true; else return false
    def halfWidth(req: MultiplierReq) = (w > 32).B && req.dw === false.B

    def sext(x: Bits, halfW: Bool, signed: Bool) = {
      val sign = signed && Mux(halfW, x(w / 2 - 1), x(w - 1))
      val hi   = Mux(halfW, Fill(w / 2, sign), x(w - 1, w / 2))
      (Cat(hi, x(w / 2 - 1, 0)), sign)
    }
    val (lhs_in, lhs_sign) = sext(io.req.bits.in1, halfWidth(io.req.bits), lhsSigned)
    val (rhs_in, rhs_sign) = sext(io.req.bits.in2, halfWidth(io.req.bits), rhsSigned)

    assert(lhs_in == io.req.bits.in1 && lhs_sign == false)
    assert(rhs_in == io.req.bits.in2 && rhs_sign == false)

    val subtractor        = remainder(2 * w, w) - divisor
    val result            = Mux(resHi, remainder(2 * w, w + 1), remainder(w - 1, 0))
    val negated_remainder = -result

    if (cfg.mulUnroll != 0) when(state === s_mul) {
      val mulReg         = Cat(remainder(2 * mulw + 1, w + 1), remainder(w - 1, 0))
      val mplierSign     = remainder(w)
      val mplier         = mulReg(mulw - 1, 0)
      val accum          = mulReg(2 * mulw, mulw).asSInt
      val mpcand         = divisor.asSInt
      val prod           = Cat(mplierSign, mplier(cfg.mulUnroll - 1, 0)).asSInt * mpcand + accum
      val nextMulReg     = Cat(prod, mplier(mulw - 1, cfg.mulUnroll))
      val nextMplierSign = count === (mulw / cfg.mulUnroll - 2).U && neg_out

      val eOutMask = ((BigInt(-1) << mulw).S >> (count * cfg.mulUnroll.U)(log2Up(mulw) - 1, 0))(mulw - 1, 0)
      val eOut = (cfg.mulEarlyOut).B && count =/= (mulw / cfg.mulUnroll - 1).U && count =/= 0.U &&
        !isHi && (mplier & ~eOutMask) === 0.U
      val eOutRes     = (mulReg >> (mulw.U - count * cfg.mulUnroll.U)(log2Up(mulw) - 1, 0))
      val nextMulReg1 = Cat(nextMulReg(2 * mulw, mulw), Mux(eOut, eOutRes, nextMulReg)(mulw - 1, 0))
      remainder := Cat(nextMulReg1 >> w, nextMplierSign, nextMulReg1(w - 1, 0))

      count := count + 1.U
      when(eOut || count === (mulw / cfg.mulUnroll - 1).U) {
        state := s_done_mul
        resHi := isHi
      }
    }

    when(io.resp.fire) {
      state := s_ready
    }
    when(io.req.fire) {
      state     := Mux(cmdMul, s_mul, Mux(lhs_sign || rhs_sign, s_neg_inputs, s_div))
      isHi      := cmdHi
      resHi     := false.B
      count     := (if (fastMulW) Mux[UInt](cmdMul && halfWidth(io.req.bits), (w / cfg.mulUnroll / 2).U, 0.U) else 0.U)
      neg_out   := Mux(cmdHi, lhs_sign, lhs_sign =/= rhs_sign)
      divisor   := Cat(rhs_sign, rhs_in)
      remainder := lhs_in
      req       := io.req.bits
    }

    val outMul = (state & (s_done_mul ^ s_done_div)) === (s_done_mul & ~s_done_div)
    val loOut  = Mux(fastMulW.B && halfWidth(req) && outMul, result(w - 1, w / 2), result(w / 2 - 1, 0))
    val hiOut  = Mux(halfWidth(req), Fill(w / 2, loOut(w / 2 - 1)), result(w - 1, w / 2))
    io.resp.bits.tag := req.tag

    io.resp.bits.data := Cat(hiOut, loOut)
    io.resp.valid     := (state === s_done_mul || state === s_done_div)
    io.req.ready      := state === s_ready
  }

  def MulRun(): BigInt = {
    val (out, reg_next) = Mul(inputs, regInit, step)

    // loop-invariant tells the relation of the outputs and inputs
    val t = if (step < timeout) {
      MulRun(inputs, reg_next, step + 1)
    }
    else {
      // loop-inv => post-condition
      (out)
    }
  } ensuring(res => true)

  // for testing
  // give initial values for the registers, and set timeout steps
  def Run(): Unit = {
    initial
    MulRun()
  }
}