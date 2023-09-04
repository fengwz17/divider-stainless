package example.rocketchip

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class DivInputs(
    io_req_valid: Bool,
    io_req_bits_dw: UInt,
    io_req_bits_in1: UInt,
    io_req_bits_in2: UInt,
    io_req_bits_tag: UInt,
    io_req_bits_fn: UInt,
    io_resp_ready: Bool
)
case class DivOutputs(
    io_req_ready: Bool,
    io_resp_valid: Bool,
    io_resp_bits_data: UInt,
    io_resp_bits_tag: UInt
)
case class DivRegs(
    state: UInt,
    req_dw: UInt,
    req_in1: UInt,
    req_in2: UInt,
    req_tag: UInt,
    req_fn: UInt,
    count: UInt,
    neg_out: Bool,
    isHi: Bool,
    resHi: Bool,
    divisor: UInt,
    remainder: UInt
)

case class Div(
    mulUnroll: BigInt = 1,
    divUnroll: BigInt = 1,
    mulEarlyOut: Boolean = false,
    divEarlyOut: Boolean = false,
    divEarlyOutGranularity: BigInt = 1,
    w: BigInt,
    nXpr: BigInt = 32
) {
  def inputsRequire(inputs: DivInputs): Boolean = inputs match {
    case DivInputs(io_req_valid, io_req_bits_dw, io_req_bits_in1, io_req_bits_in2, io_req_bits_tag, io_req_bits_fn, io_resp_ready) =>
      io_req_bits_dw.width == 1 &&
      io_req_bits_in1.width == w &&
      io_req_bits_in2.width == w &&
      io_req_bits_tag.width == log2Up(nXpr) &&
      io_req_bits_fn.width == 4
  }
  def outputsRequire(outputs: DivOutputs): Boolean = outputs match {
    case DivOutputs(io_req_ready, io_resp_valid, io_resp_bits_data, io_resp_bits_tag) =>
      io_resp_bits_data.width == w &&
      io_resp_bits_tag.width == log2Up(nXpr)
  }
  def regsRequire(regs: DivRegs): Boolean = regs match {
    case DivRegs(state, req_dw, req_in1, req_in2, req_tag, req_fn, count, neg_out, isHi, resHi, divisor, remainder) =>
      state.width == 3 &&
      req_dw.width == 1 &&
      req_in1.width == w &&
      req_in2.width == w &&
      req_tag.width == log2Up(nXpr) &&
      req_fn.width == 4 &&
      count.width == log2Ceil(((w / divUnroll) + 1)) &&
      divisor.width == (w + 1) &&
      remainder.width == ((2 * (if ((mulUnroll == 0)) w else ((((w + mulUnroll) - 1) / mulUnroll) * mulUnroll))) + 2)
  }

  def trans(inputs: DivInputs, regs: DivRegs): (DivOutputs, DivRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_req_ready = Bool.empty()
    var io_resp_valid = Bool.empty()
    var io_resp_bits_data = UInt.empty(w)
    var io_resp_bits_tag = UInt.empty(log2Up(nXpr))
    // reg next
    var state_next = regs.state
    var req_dw_next = regs.req_dw
    var req_in1_next = regs.req_in1
    var req_in2_next = regs.req_in2
    var req_tag_next = regs.req_tag
    var req_fn_next = regs.req_fn
    var count_next = regs.count
    var neg_out_next = regs.neg_out
    var isHi_next = regs.isHi
    var resHi_next = regs.resHi
    var divisor_next = regs.divisor
    var remainder_next = regs.remainder

    // body
    def minDivLatency: BigInt = {
      if (divEarlyOut) 3 else (1 + (w / divUnroll))
    }
    def minLatency: BigInt = {
      minDivLatency
    }
    val mulw = if ((mulUnroll == 0)) w else ((((w + mulUnroll) - 1) / mulUnroll) * mulUnroll)
    val fastMulW = if ((mulUnroll == 0)) false else (((w / 2) > mulUnroll) && ((w % (2 * mulUnroll)) == 0))
    val (s_ready, s_neg_inputs, s_div, s_dummy, s_neg_output, s_done_div) = (Lit(0, 3).U, Lit(1, 3).U, Lit(2, 3).U, Lit(3, 3).U, Lit(4, 3).U, Lit(5, 3).U)
    var cmdMul = Lit(false).B
    var cmdHi = Lit(false).B
    var lhsSigned = Lit(false).B
    var rhsSigned = Lit(false).B
    if ((divUnroll != 0)) if (inputs.io_req_bits_fn == Lit(4).U) {
      cmdMul = cmdMul := Lit(false).B
      cmdHi = cmdHi := Lit(false).B
      lhsSigned = lhsSigned := Lit(true).B
      rhsSigned = rhsSigned := Lit(true).B
    }
    def halfWidth(reqDw: UInt): Bool = {
      (Lit((w > 32)).B && (reqDw === Lit(false).B))
    }
    def sext(x: UInt, halfW: Bool, signed: Bool): (UInt, Bool) = {
      val sign = (signed && Mux(halfW, x(((w / 2) - 1)), x((w - 1))))
      val hi = Mux(halfW, Fill((w / 2), sign), x((w - 1), (w / 2)))
      (Cat(hi, x(((w / 2) - 1), 0)), sign)
    }
    val (lhs_in, lhs_sign) = sext(inputs.io_req_bits_in1, halfWidth(inputs.io_req_bits_dw), lhsSigned)
    val (rhs_in, rhs_sign) = sext(inputs.io_req_bits_in2, halfWidth(inputs.io_req_bits_dw), rhsSigned)
    val subtractor = (regs.remainder((2 * w), w) - regs.divisor)
    val result = Mux(regs.resHi, regs.remainder((2 * w), (w + 1)), regs.remainder((w - 1), 0))
    val negated_remainder = -result
    if ((divUnroll != 0)) if (when((regs.state === s_neg_inputs))) {
      if (when(regs.remainder((w - 1)))) {
        remainder_next = remainder_next := negated_remainder
      }
      if (when(regs.divisor((w - 1)))) {
        divisor_next = divisor_next := subtractor
      }
      state_next = state_next := s_div
    }
    if ((divUnroll != 0)) if (when((regs.state === s_neg_output))) {
      remainder_next = remainder_next := negated_remainder
      state_next = state_next := s_done_div
      resHi_next = resHi_next := Lit(false).B
    }
    val divby0 = ((regs.count === Lit(0).U) && !subtractor(w))
    val align = (1 << log2Floor(max(divUnroll, divEarlyOutGranularity)))
    val alignMask = ~Lit((align - 1), log2Ceil(w)).U
    val divisorMSB = (Log2(regs.divisor((w - 1), 0), w) & alignMask)
    val dividendMSB = (Log2(regs.remainder((w - 1), 0), w) | ~alignMask)
    val eOutPos = ~(dividendMSB - divisorMSB)
    val eOut = (((regs.count === Lit(0).U) && !divby0) && (eOutPos >= Lit(align).U))
    if ((divUnroll != 0)) if (when((regs.state === s_div))) {
      val unrolls = (0 until divUnroll).scanLeft(regs.remainder)({ case (rem, i) => {
          val difference = if ((i == 0)) subtractor else (rem((2 * w), w) - regs.divisor((w - 1), 0))
          val less = difference(w)
          Cat(List(Mux(less, rem(((2 * w) - 1), w), difference((w - 1), 0)), rem((w - 1), 0), !less))
      }}).tail
      remainder_next = remainder_next := unrolls.last
      if (when((regs.count === Lit((w / divUnroll)).U))) {
        state_next = state_next := Mux(regs.neg_out, s_neg_output, s_done_div)
        resHi_next = resHi_next := regs.isHi
        if (((w % divUnroll) < (divUnroll - 1))) remainder_next = remainder_next := unrolls((w % divUnroll))
      }
      count_next = count_next := (regs.count + Lit(1).U)
      if (divEarlyOut) if (when(eOut)) {
        remainder_next = remainder_next := (regs.remainder((w - 1), 0) << eOutPos)
        count_next = count_next := (eOutPos >> log2Floor(divUnroll))
      }
      if (when((divby0 && !regs.isHi))) {
        neg_out_next = neg_out_next := Lit(false).B
      }
    }
    val outMul = ((regs.state & s_done_div) === (Lit(false).B & ~s_done_div))
    io_resp_valid = io_resp_valid := (regs.state === s_done_div)
    if (when((inputs.io_resp_ready && io_resp_valid))) {
      state_next = state_next := s_ready
    }
    io_req_ready = io_req_ready := (regs.state === s_ready)
    if (when((io_req_ready && inputs.io_req_valid))) {
      state_next = state_next := Mux((lhs_sign || rhs_sign), s_neg_inputs, s_div)
      isHi_next = isHi_next := cmdHi
      resHi_next = resHi_next := Lit(false).B
      count_next = count_next := (if (fastMulW) Mux((cmdMul && halfWidth(inputs.io_req_bits_dw)), Lit(((w / mulUnroll) / 2)).U, Lit(0).U) else Lit(0).U)
      neg_out_next = neg_out_next := Mux(cmdHi, lhs_sign, (lhs_sign =/= rhs_sign))
      divisor_next = divisor_next := Cat(rhs_sign, rhs_in)
      remainder_next = remainder_next := lhs_in
      req_next = req_next := io_req_bits
    }
    val loOut = Mux(((Lit(fastMulW).B && halfWidth(regs.req_dw)) && outMul), result((w - 1), (w / 2)), result(((w / 2) - 1), 0))
    val hiOut = Mux(halfWidth(regs.req_dw), Fill((w / 2), loOut(((w / 2) - 1))), result((w - 1), (w / 2)))
    io_resp_bits_tag = io_resp_bits_tag := regs.req_tag
    io_resp_bits_data = io_resp_bits_data := Cat(hiOut, loOut)

    (
      DivOutputs(
        io_req_ready,
        io_resp_valid,
        io_resp_bits_data,
        io_resp_bits_tag
      ),
      DivRegs(
        state_next,
        req_dw_next,
        req_in1_next,
        req_in2_next,
        req_tag_next,
        req_fn_next,
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

  def divRun(timeout: Int, inputs: DivInputs, regInit: DivRegs): (DivOutputs, DivRegs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      divRun(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
  def run(inputs: DivInputs, randomInitValue: DivRegs): (DivOutputs, DivRegs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = DivRegs(
      Lit(0, 3).U,
      randomInitValue.req_dw,
      randomInitValue.req_in1,
      randomInitValue.req_in2,
      randomInitValue.req_tag,
      randomInitValue.req_fn,
      randomInitValue.count,
      randomInitValue.neg_out,
      randomInitValue.isHi,
      randomInitValue.resHi,
      randomInitValue.divisor,
      randomInitValue.remainder
    )
    divRun(100, inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}