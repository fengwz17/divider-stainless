package example.rocketchip

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class MulInputs(
    io_req_valid: Bool,
    io_req_bits_fn: UInt,
    io_req_bits_dw: UInt,
    io_req_bits_tag: UInt,
    io_req_bits_in1: UInt,
    io_req_bits_in2: UInt,
    io_resp_ready: Bool
)
case class MulOutputs(
    io_req_ready: Bool,
    io_resp_valid: Bool,
    io_resp_bits_data: UInt,
    io_resp_bits_tag: UInt
)
case class MulRegs(
    state: UInt,
    req_fn: UInt,
    req_dw: UInt,
    req_tag: UInt,
    req_in1: UInt,
    req_in2: UInt,
    count: UInt,
    neg_out: Bool,
    isHi: Bool,
    resHi: Bool,
    divisor: UInt,
    remainder: UInt
)

case class Mul(
    mulUnroll: BigInt,
    divUnroll: BigInt,
    mulEarlyOut: Boolean,
    divEarlyOut: Boolean,
    divEarlyOutGranularity: BigInt,
    width: BigInt,
    nXpr: BigInt
) {
  def inputsRequire(inputs: MulInputs): Boolean = inputs match {
    case MulInputs(
          io_req_valid,
          io_req_bits_fn,
          io_req_bits_dw,
          io_req_bits_tag,
          io_req_bits_in1,
          io_req_bits_in2,
          io_resp_ready
        ) =>
      io_req_bits_fn.width == 4 &&
      io_req_bits_dw.width == 1 &&
      io_req_bits_tag.width == tagBits &&
      io_req_bits_in1.width == dataBits &&
      io_req_bits_in2.width == dataBits
  }
  def outputsRequire(outputs: MulOutputs): Boolean = outputs match {
    case MulOutputs(io_req_ready, io_resp_valid, io_resp_bits_data, io_resp_bits_tag) =>
      io_resp_bits_data.width == dataBits &&
      io_resp_bits_tag.width == tagBits
  }
  def regsRequire(regs: MulRegs): Boolean = regs match {
    case MulRegs(state, req_fn, req_dw, req_tag, req_in1, req_in2, count, neg_out, isHi, resHi, divisor, remainder) =>
      state.width == 2 &&
      req_fn.width == 4 &&
      req_dw.width == 1 &&
      req_tag.width == tagBits &&
      req_in1.width == dataBits &&
      req_in2.width == dataBits &&
      count.width == log2Ceil((mulw / mulUnroll)) &&
      divisor.width == (w + 1) &&
      remainder.width == ((2 * mulw) + 2)
  }

  def trans(inputs: MulInputs, regs: MulRegs): (MulOutputs, MulRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_req_ready      = Bool.empty()
    var io_resp_valid     = Bool.empty()
    var io_resp_bits_data = UInt.empty(dataBits)
    var io_resp_bits_tag  = UInt.empty(tagBits)
    // reg next
    var state_next     = regs.state
    var req_fn_next    = regs.req_fn
    var req_dw_next    = regs.req_dw
    var req_tag_next   = regs.req_tag
    var req_in1_next   = regs.req_in1
    var req_in2_next   = regs.req_in2
    var count_next     = regs.count
    var neg_out_next   = regs.neg_out
    var isHi_next      = regs.isHi
    var resHi_next     = regs.resHi
    var divisor_next   = regs.divisor
    var remainder_next = regs.remainder

    // body
    def minMulLatency: BigInt = {
      if (mulEarlyOut) 2 else (w / mulUnroll)
    }
    def minLatency: BigInt = {
      minMulLatency
    }
    val w        = io_req_bits_in1.width
    val mulw     = if ((mulUnroll == 0)) w else ((((w + mulUnroll) - 1) / mulUnroll) * mulUnroll)
    val fastMulW = if ((mulUnroll == 0)) false else (((w / 2) > mulUnroll) && ((w % (2 * mulUnroll)) == 0))
    val (s_ready, s_mul, s_done_mul) = (Lit(0, 2).U, Lit(1, 2).U, Lit(2, 2).U)
    var cmdMul                       = Lit(false).B
    var cmdHi                        = Lit(false).B
    var lhsSigned                    = Lit(false).B
    var rhsSigned                    = Lit(false).B
    if ((mulUnroll != 0)) if (io_req_bits_fn == Lit(0).U) {
      cmdMul = cmdMul       := Lit(true).B
      cmdHi = cmdHi         := Lit(false).B
      lhsSigned = lhsSigned := Lit(false).B
      rhsSigned = rhsSigned := Lit(false).B
    }
    def halfWidth(reqDw: UInt): Bool = {
      (Lit((w > 32)).B && (reqDw === Lit(false).B))
    }
    def sext(x: UInt, halfW: Bool, signed: Bool): (UInt, Bool) = {
      val sign = (signed && Mux(halfW, x(((w / 2) - 1)), x((w - 1))))
      val hi   = Mux(halfW, Fill((w / 2), sign), x((w - 1), (w / 2)))
      (Cat(hi, x(((w / 2) - 1), 0)), sign)
    }
    val (lhs_in, lhs_sign) = sext(io_req_bits_in1, halfWidth(io_req_bits_dw), lhsSigned)
    val (rhs_in, rhs_sign) = sext(io_req_bits_in2, halfWidth(io_req_bits_dw), rhsSigned)
    val subtractor         = (regs.remainder((2 * w), w) - regs.divisor)
    val result             = Mux(regs.resHi, regs.remainder((2 * w), (w + 1)), regs.remainder((w - 1), 0))
    val negated_remainder  = -result
    val mulReg             = Cat(regs.remainder(((2 * mulw) + 1), (w + 1)), regs.remainder((w - 1), 0))
    val mplierSign         = regs.remainder(w)
    val mplier             = mulReg((mulw - 1), 0)
    val accum              = mulReg((2 * mulw), mulw).asSInt
    val mpcand             = regs.divisor.asSInt
    val prod               = ((Cat(mplierSign, mplier((mulUnroll - 1), 0)).asSInt * mpcand) + accum)
    val nextMulReg         = Cat(prod, mplier((mulw - 1), mulUnroll))
    val nextMplierSign     = ((regs.count === Lit(((mulw / mulUnroll) - 2)).U) && regs.neg_out)
    val eOutMask = (Lit((-1 << mulw)).S >> (regs.count * Lit(mulUnroll).U)((log2Up(mulw) - 1), 0))((mulw - 1), 0)
    val eOut = ((((Lit(mulEarlyOut).B && (regs.count =/= Lit(((mulw / mulUnroll) - 1)).U)) && (regs.count =/= Lit(
      0
    ).U)) && !regs.isHi) && ((mplier & ~eOutMask) === Lit(0).U))
    val eOutRes     = (mulReg >> (Lit(mulw).U - (regs.count * Lit(mulUnroll).U))((log2Up(mulw) - 1), 0))
    val nextMulReg1 = Cat(nextMulReg((2 * mulw), mulw), Mux(eOut, eOutRes, nextMulReg)((mulw - 1), 0))
    if ((mulUnroll != 0)) if (when((regs.state === s_mul))) {
      remainder_next = remainder_next := Cat(List((nextMulReg1 >> w), nextMplierSign, nextMulReg1((w - 1), 0)))
      count_next = count_next         := (regs.count + Lit(1).U)
      if (when((eOut || (regs.count === Lit(((mulw / mulUnroll) - 1)).U)))) {
        state_next = state_next := s_done_mul
        resHi_next = resHi_next := regs.isHi
      }
    }
    val outMul = ((regs.state & s_done_mul) === s_done_mul)
    io_resp_valid = io_resp_valid := (regs.state === s_done_mul)
    if (when((io_resp_ready && io_resp_valid))) {
      state_next = state_next := s_ready
    }
    io_req_ready = io_req_ready := (regs.state === s_ready)
    if (when((io_req_ready && io_req_valid))) {
      state_next = state_next := Mux(cmdMul, s_mul, s_ready)
      isHi_next = isHi_next   := cmdHi
      resHi_next = resHi_next := Lit(false).B
      count_next =
        count_next := (if (fastMulW) Mux((cmdMul && halfWidth(io_req_bits_dw)), Lit(((w / mulUnroll) / 2)).U, Lit(0).U)
                       else Lit(0).U)
      neg_out_next = neg_out_next     := Mux(cmdHi, lhs_sign, (lhs_sign =/= rhs_sign))
      divisor_next = divisor_next     := Cat(rhs_sign, rhs_in)
      remainder_next = remainder_next := lhs_in
      req_next = req_next             := io_req_bits
    }
    val loOut =
      Mux(((Lit(fastMulW).B && halfWidth(regs.req_dw)) && outMul), result((w - 1), (w / 2)), result(((w / 2) - 1), 0))
    val hiOut = Mux(halfWidth(regs.req_dw), Fill((w / 2), loOut(((w / 2) - 1))), result((w - 1), (w / 2)))
    io_resp_bits_tag = io_resp_bits_tag   := regs.req_tag
    io_resp_bits_data = io_resp_bits_data := Cat(hiOut, loOut)

    (
      MulOutputs(
        io_req_ready,
        io_resp_valid,
        io_resp_bits_data,
        io_resp_bits_tag
      ),
      MulRegs(
        state_next,
        req_fn_next,
        req_dw_next,
        req_tag_next,
        req_in1_next,
        req_in2_next,
        count_next,
        neg_out_next,
        isHi_next,
        resHi_next,
        divisor_next,
        remainder_next
      )
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }

  def mulRun(timeout: Int, inputs: MulInputs, regInit: MulRegs): (MulOutputs, MulRegs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      mulRun(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
  def run(inputs: MulInputs, randomInitValue: MulRegs): (MulOutputs, MulRegs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = MulRegs(
      Lit(0, 2).U,
      randomInitValue.req_fn,
      randomInitValue.req_dw,
      randomInitValue.req_tag,
      randomInitValue.req_in1,
      randomInitValue.req_in2,
      randomInitValue.count,
      randomInitValue.neg_out,
      randomInitValue.isHi,
      randomInitValue.resHi,
      randomInitValue.divisor,
      randomInitValue.remainder
    )
    mulRun(100, inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}
