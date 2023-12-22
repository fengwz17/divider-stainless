package exampleVerify.rocketchip

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class MulInputs(
    io_req_valid: Bool,
    io_req_bits_tag: UInt,
    io_req_bits_dw: UInt,
    io_req_bits_fn: UInt,
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
    req_tag: UInt,
    req_dw: UInt,
    req_fn: UInt,
    req_in1: UInt,
    req_in2: UInt,
    count: UInt,
    neg_out: Bool,
    isHi: Bool,
    resHi: Bool,
    divisor: UInt,
    remainder: UInt,
    mulRegReg: UInt
)

case class Mul(
    mulUnroll: BigInt = 1,
    divUnroll: BigInt = 1,
    mulEarlyOut: Boolean = false,
    divEarlyOut: Boolean = false,
    divEarlyOutGranularity: BigInt = 1,
    w: BigInt,
    nXpr: BigInt = 32
) {
  def inputsRequire(inputs: MulInputs): Boolean = inputs match {
    case MulInputs(io_req_valid, io_req_bits_tag, io_req_bits_dw, io_req_bits_fn, io_req_bits_in1, io_req_bits_in2, io_resp_ready) =>
      io_req_bits_tag.width == log2Up(nXpr) &&
      io_req_bits_dw.width == 1 &&
      io_req_bits_fn.width == 4 &&
      io_req_bits_in1.width == w &&
      io_req_bits_in2.width == w
  }
  def outputsRequire(outputs: MulOutputs): Boolean = outputs match {
    case MulOutputs(io_req_ready, io_resp_valid, io_resp_bits_data, io_resp_bits_tag) =>
      io_resp_bits_data.width == w &&
      io_resp_bits_tag.width == log2Up(nXpr)
  }
  def regsRequire(regs: MulRegs): Boolean = regs match {
    case MulRegs(state, req_tag, req_dw, req_fn, req_in1, req_in2, count, neg_out, isHi, resHi, divisor, remainder, mulRegReg) =>
      state.width == 3 &&
      req_tag.width == log2Up(nXpr) &&
      req_dw.width == 1 &&
      req_fn.width == 4 &&
      req_in1.width == w &&
      req_in2.width == w &&
      count.width == log2Ceil(((if ((mulUnroll == 0)) w else ((((w + mulUnroll) - 1) / mulUnroll) * mulUnroll)) / mulUnroll)) &&
      divisor.width == (w + 1) &&
      remainder.width == ((2 * (if ((mulUnroll == 0)) w else ((((w + mulUnroll) - 1) / mulUnroll) * mulUnroll))) + 2)
  }

  def preCond(inputs: MulInputs, regs: MulRegs): Boolean = {
    // require(regs.count >= 0 && regs.count < width / mulUnroll)
    val in1 = inputs.io_req_bits_in1.value
    val in2 = inputs.io_req_bits_in2.value
    (regs.count.value == BigInt(0) && regs.remainder.value == inputs.io_req_bits_in1.value && regs.divisor.value == inputs.io_req_bits_in2.value 
      || regs.count.value >= BigInt(1) && regs.remainder.value >= BigInt(0) && regs.divisor.value == in2) &&
    // decreases(width / mulUnroll - regs.count.value)
    (regs.mulRegReg.value == regs.remainder.value % Pow2(w) + regs.remainder.value / Pow2(w + 1) * Pow2(w)) &&
    (regs.mulRegReg.value % Pow2(w - regs.count.value * mulUnroll) == in1 / Pow2(regs.count.value * mulUnroll)) &&
    regs.state.value == BigInt(0)
  }

  def postCond(inputs: MulInputs, outputs: MulOutputs, regs: MulRegs): Boolean = {
    val in1 = inputs.io_req_bits_in1.value
    val in2 = inputs.io_req_bits_in2.value
    (regs.count.value == BigInt(0) && regs.remainder.value == in1 && regs.divisor.value == in2 
      || regs.count.value >= BigInt(1) && regs.remainder.value >= BigInt(0) && regs.divisor.value == in2) &&
    // decreases(width / mulUnroll - regs.count.value)
    (regs.mulRegReg.value == regs.remainder.value % Pow2(w) + regs.remainder.value / Pow2(w + 1) * Pow2(w)) &&
    (regs.mulRegReg.value % Pow2(w - regs.count.value * mulUnroll) == in1 / Pow2(regs.count.value * mulUnroll))
  }

  // lemmas
  @library
  def nextMulRegUpdate(mulReg: BigInt, nextMulReg: BigInt, 
    prod: BigInt, mulw: BigInt, width: BigInt, mplier: BigInt, remainder: BigInt, inputs: MulInputs, w: BigInt): Unit = {
    val in1 = inputs.io_req_bits_in1.value
    val in2 = inputs.io_req_bits_in2.value
    {
      nextMulReg ==:| trivial |:
      prod * Pow2(mulw - mulUnroll) + mplier / Pow2(mulUnroll) ==:| trivial |:
      (remainder % Pow2(mulUnroll) * in2 + remainder / Pow2(w + 1)) * Pow2(mulw - mulUnroll)
        + (remainder % Pow2(width)) / Pow2(mulUnroll) ==:| trivial |:
      (mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)) * Pow2(mulw- mulUnroll) 
        + (mulReg % Pow2(w)) / Pow2(mulUnroll)
    }.qed
  }.ensuring(nextMulReg == (mulReg % Pow2(mulUnroll) * inputs.io_req_bits_in2 + mulReg / Pow2(w)) * Pow2(mulw- mulUnroll) 
        + (mulReg % Pow2(w)) / Pow2(mulUnroll))

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
  // mulReg % Pow2(w - step * mulUnroll) == in1 / Pow2(step * mulUnroll) 
  def mulReg_lower_bits(nextMulReg: BigInt, mulReg: BigInt, w: BigInt, step: BigInt, inputs: MulInputs): Unit = { 
    val in1 = inputs.io_req_bits_in1.value
    val in2 = inputs.io_req_bits_in2.value
    require(w == 32 || w == 64)
    require(mulUnroll == 1)
    require(step >= 0 && step < w / mulUnroll)
    require(mulReg >= 0)
    require(nextMulReg >= 0)
    require(nextMulReg == (mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)) * Pow2(w - mulUnroll) 
        + (mulReg % Pow2(w)) / Pow2(mulUnroll))
    require(in1 >= 0 && in1 < Pow2(w))
    require(mulReg % Pow2(w - step * mulUnroll) == in1 / Pow2(step * mulUnroll))

    val h = mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)
    val l = (mulReg % Pow2(w)) / Pow2(mulUnroll)
    {
      h ==:| trivial |:
      mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)
    }.qed

    {
      nextMulReg % Pow2(w - (step + 1) * mulUnroll) ==:| trivial |:
      ((mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)) * Pow2(w - mulUnroll) + (mulReg % Pow2(w)) / Pow2(mulUnroll)) 
        % Pow2(w - (step + 1) * mulUnroll) // ==:| {h == mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)} |:
      // (h * Pow2(w - mulUnroll) + (mulReg % Pow2(w)) / Pow2(mulUnroll)) % Pow2(w - (step + 1) * mulUnroll)
    }.qed
    {
      (mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)) * Pow2(w - mulUnroll) + (mulReg % Pow2(w)) / Pow2(mulUnroll) ==:| trivial |:
      h * Pow2(w - mulUnroll) + l
    }.qed
    {
      ((mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)) * Pow2(w - mulUnroll) + (mulReg % Pow2(w)) / Pow2(mulUnroll)) 
        % Pow2(w - (step + 1) * mulUnroll) ==:| trivial |:
      (h * Pow2(w - mulUnroll) + l) % Pow2(w - (step + 1) * mulUnroll)
    }.qed
    {
      nextMulReg % Pow2(w - (step + 1) * mulUnroll) ==:| trivial |:
      ((mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)) * Pow2(w - mulUnroll) + (mulReg % Pow2(w)) / Pow2(mulUnroll)) 
        % Pow2(w - (step + 1) * mulUnroll)          ==:| trivial |:
      (h * Pow2(w - mulUnroll) + l) % Pow2(w - (step + 1) * mulUnroll) ==:| lemmaPow2Mod(h, w - mulUnroll, l, w - (step + 1) * mulUnroll) |:
      l % Pow2(w - (step + 1) * mulUnroll)
    }.qed

    // check
    {
      (mulReg % Pow2(w)) / Pow2(mulUnroll) ==:| trivial |:
      mulReg % Pow2(w - step * mulUnroll) / Pow2(mulUnroll) ==:| trivial |:
      in1 / Pow2(step * mulUnroll) / Pow2(mulUnroll) ==:| trivial |:
      in1 / Pow2(step * mulUnroll + mulUnroll)       ==:| trivial |:
      in1 / Pow2((step + 1) * mulUnroll)
    }.qed
  }.ensuring(nextMulReg % Pow2(w - (step + 1) * mulUnroll) == inputs.io_req_bits_in1 / Pow2((step + 1) * mulUnroll))

  @library
  // mulReg / Pow2(w - step * mulUnroll) == in1 % Pow2(step * mulUnroll) * in2 
  def mulReg_higher_bits(nextMulReg: BigInt, mulReg: BigInt, w: BigInt, step: BigInt, inputs: MulInputs): Unit = { 
    val in1 = inputs.io_req_bits_in1.value
    val in2 = inputs.io_req_bits_in2.value
    require(w == 32 || w == 64)
    require(mulUnroll == 1)
    require(step >= 0 && step < w / mulUnroll)
    require(mulReg >= 0)
    require(nextMulReg >= 0)
    require(nextMulReg == (mulReg % Pow2(mulUnroll) * in2 + mulReg / Pow2(w)) * Pow2(w - mulUnroll) 
        + (mulReg % Pow2(w)) / Pow2(mulUnroll))
    require(in1 >= 0 && in1 < Pow2(w))
    require(mulReg / Pow2(w - step * mulUnroll) == in1 % Pow2(step * mulUnroll) * in2)
    require(mulReg % Pow2(w - step * mulUnroll) == in1 / Pow2(step * mulUnroll))

    // check
    {
      nextMulReg % Pow2(mulUnroll) * in2 ==:| trivial |:
      nextMulReg % Pow2(w - step * mulUnroll) % Pow2(mulUnroll) * in2 ==:| trivial |:
      in1 / Pow2(step * mulUnroll) % Pow2(mulUnroll) * in2
    }.qed

    val h = mulReg / Pow2(w - step * mulUnroll)
    val l = mulReg - h * Pow2(w - step * mulUnroll)

    {
      mulReg / Pow2(w) ==:| trivial |:
      mulReg / Pow2(w - step * mulUnroll) / Pow2(step * mulUnroll) ==:| trivial |:
      h / Pow2(step * mulUnroll)
    }

    val hh = h / Pow2(step * mulUnroll)
    val hl = h - hh * Pow2(step * mulUnroll)

    {
      mulReg % Pow2(w) / Pow2(mulUnroll) ==:| trivial |:
      hl * Pow2(w - (step + 1) * mulUnroll) + l / Pow2(mulUnroll)
    }.qed
    
    {
      nextMulReg / Pow2(w - (step + 1) * mulUnroll) ==:| trivial |:
      (in1 / Pow2(step * mulUnroll) % Pow2(mulUnroll) * in2 + h / Pow2(step * mulUnroll)) * Pow2(step * mulUnroll)
        + h % Pow2(step * mulUnroll) ==:| trivial |:
      in1 / Pow2(step * mulUnroll) % Pow2(mulUnroll) * in2 * Pow2(step * mulUnroll)
        + h ==:| trivial |:
      in1 / Pow2(step * mulUnroll) % Pow2(mulUnroll) * in2 * Pow2(step * mulUnroll)
        + in1 % Pow2(step * mulUnroll) * in2 ==:| trivial |:
      (in1 / Pow2(step * mulUnroll) % Pow2(mulUnroll) + in1 % Pow2(step * mulUnroll)) * in2 ==:| trivial |:
      in1 % Pow2((step + 1) * mulUnroll) * in2
    }.qed

  }.ensuring(nextMulReg / Pow2(w - (step + 1) * mulUnroll) == inputs.io_req_bits_in1.value % Pow2((step + 1) * mulUnroll) * inputs.io_req_bits_in2.value)

  
  def trans(inputs: MulInputs, regs: MulRegs): (MulOutputs, MulRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_req_ready = Bool.empty()
    var io_resp_valid = Bool.empty()
    var io_resp_bits_data = UInt.empty(w)
    var io_resp_bits_tag = UInt.empty(log2Up(nXpr))
    // reg next
    var state_next = regs.state
    var req_tag_next = regs.req_tag
    var req_dw_next = regs.req_dw
    var req_fn_next = regs.req_fn
    var req_in1_next = regs.req_in1
    var req_in2_next = regs.req_in2
    var count_next = regs.count
    var neg_out_next = regs.neg_out
    var isHi_next = regs.isHi
    var resHi_next = regs.resHi
    var divisor_next = regs.divisor
    var remainder_next = regs.remainder

    // ghost-variable
    var mulRegReg_next = regs.mulRegReg

    // body
    def minMulLatency: BigInt = if (mulEarlyOut) 2 else (w / mulUnroll)
    def minLatency: BigInt = minMulLatency
    val mulw = if ((mulUnroll == 0)) w else ((((w + mulUnroll) - 1) / mulUnroll) * mulUnroll)
    val fastMulW = if ((mulUnroll == 0)) false else (((w / 2) > mulUnroll) && ((w % (2 * mulUnroll)) == 0))
    val (s_ready, s_neg_inputs, s_mul, s_div, s_dummy, s_neg_output, s_done_mul, s_done_div) = (Lit(0, 3).U, Lit(1, 3).U, Lit(2, 3).U, Lit(3, 3).U, Lit(4, 3).U, Lit(5, 3).U, Lit(6, 3).U, Lit(7, 3).U)
    var cmdMul = Lit(false).B
    var cmdHi = Lit(false).B
    var lhsSigned = Lit(false).B
    var rhsSigned = Lit(false).B
    if ((mulUnroll != 0)) if ((inputs.io_req_bits_fn === Lit(0).U).value) {
      cmdMul = cmdMul := Lit(true).B
      cmdHi = cmdHi := Lit(false).B
      lhsSigned = lhsSigned := Lit(false).B
      rhsSigned = rhsSigned := Lit(false).B
    }
    def halfWidth(reqDw: UInt): Bool = (Lit((w > 32)).B && (reqDw === Lit(false).B))
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
    val mulReg = Cat(regs.remainder(((2 * mulw) + 1), (w + 1)), regs.remainder((w - 1), 0))
    val mplierSign = regs.remainder(w)
    val mplier = mulReg((mulw - 1), 0)
    val accum = mulReg((2 * mulw), mulw).asSInt
    val mpcand = regs.divisor.asSInt
    val prod = ((Cat(mplierSign, mplier((mulUnroll - 1), 0)).asSInt * mpcand) + accum)
    val nextMulReg = Cat(prod, mplier((mulw - 1), mulUnroll))
    val nextMplierSign = ((regs.count === Lit(((mulw / mulUnroll) - 2)).U) && regs.neg_out)
    val eOutMask = (Lit((-1 << mulw)).S >> (regs.count * Lit(mulUmpliernroll).U)((log2Up(mulw) - 1), 0))((mulw - 1), 0)
    val eOut = ((((Lit(mulEarlyOut).B && (regs.count =/= Lit(((mulw / mulUnroll) - 1)).U)) && (regs.count =/= Lit(0).U)) && !regs.isHi) && ((mplier & ~eOutMask) === Lit(0).U))
    val eOutRes = (mulReg >> (Lit(mulw).U - (regs.count * Lit(mulUnroll).U))((log2Up(mulw) - 1), 0))
    val nextMulReg1 = Cat(nextMulReg((2 * mulw), mulw), Mux(eOut, eOutRes, nextMulReg)((mulw - 1), 0))

    assert(regs.mulRegReg.value == mulReg.value)

    {
      accum.value ==:| trivial |:
      mulReg.value / Pow2(mulw) ==:| trivial |:
      mulReg.value / Pow2(w) ==:| trivial |:
      (remainder.value / Pow2(w + 1) * Pow2(w) + remainder.value % Pow2(w)) / Pow2(w) ==:| trivial |:
      remainder.value / Pow2(w + 1)
      }.qed

    {
      mplier.value ==:| trivial |:
      mulReg.value % Pow2(mulw) ==:| trivial |:
      mulReg.value % Pow2(w) ==:| trivial |:
      mulReg.value -  mulReg.value / Pow2(w) * Pow2(w) ==:| trivial |:
      mulReg.value - remainder.value / Pow2(w + 1) * Pow2(w) ==:| trivial |:
      remainder.value / Pow2(w + 1) * Pow2(w) + remainder.value % Pow2(w) - remainder.value / Pow2(w + 1) * Pow2(w) ==:| trivial |:
      remainder.value % Pow2(w)
    }.qed


    
    {
      remainder.value % Pow2(width) % Pow2(mulUnroll)
        ==:| lemmaPow2ModMod(remainder.value, width, mulUnroll) |:
      remainder.value % Pow2(mulUnroll)
    }.qed

    {
      prod.value ==:| trivial |:
      mplier.value % Pow2(mulUnroll) * mpcand.value + accum.value ==:| trivial |:
      mplier.value % Pow2(mulUnroll) * in2 + remainder.value / Pow2(w + 1) ==:| trivial |:
      remainder.value % Pow2(width) % Pow2(mulUnroll) * in2 + remainder.value / Pow2(w + 1) 
        ==:| trivial |:
      remainder.value % Pow2(mulUnroll) * in2 + remainder.value / Pow2(w + 1)
    }.qed
    
    if ((mulUnroll != 0)) if (when((regs.state === s_mul))) {
      remainder_next = remainder_next := Cat(List((nextMulReg1 >> w), nextMplierSign, nextMulReg1((w - 1), 0)))
      count_next = count_next := (regs.count + Lit(1).U)

      if (when((eOut || (regs.count === Lit(((mulw / mulUnroll) - 1)).U)))) {
        state_next = state_next := s_done_mul
        resHi_next = resHi_next := regs.isHi
      }

      assert(count_next.value == regs.count.value + 1) 
      assert(nextMplierSign.value == false)
      assert(eOut.value == false)
  
      {
        remainder_next.value / Pow2(w + 1) ==:| MulRegRemainder(nextMulReg1.value, remainder_next.value, w) |:
        nextMulReg1.value / Pow2(w)
      }.qed

      {
        remainder_next.value / Pow2(w) ==:| MulRegRemainder(nextMulReg1.value, remainder_next.value, w) |:
        (nextMulReg1.value / Pow2(w)) * 2
      }.qed
      
      {
        remainder_next.value % Pow2(w) ==:| MulRegRemainder(nextMulReg1.value, remainder_next.value, w) |:
        nextMulReg1.value % Pow2(w) 
      }.qed

      {
        mulReg.value / Pow2(w) ==:| MulRegRemainder(mulReg.value, remainder.value, w) |:
        remainder.value / Pow2(w + 1)
      }.qed

      {
        mulReg.value % Pow2(w) ==:| MulRegRemainder(mulReg.value, remainder.value, w) |:
        remainder.value % Pow2(w)
      }.qed

      {
        nextMulReg.value ==:| nextMulRegUpdate(mulReg.value, nextMulReg.value, prod.value, mulw.value, width, cfg, mplier, remainder, inputs, w) |:
        (mulReg.value % Pow2(mulUnroll) * in2.value + mulReg.value / Pow2(w)) * Pow2(mulw.value - mulUnroll) 
          + (mulReg.value % Pow2(w)) / Pow2(mulUnroll)
      }.qed
    
      {
        remainder_next.value % Pow2(w) + remainder_next.value / Pow2(w + 1) * Pow2(w)  ==:| trivial |:
        nextMulReg1.value % Pow2(w) + nextMulReg1.value / Pow2(w) * Pow2(w)            ==:| trivial |:
        nextMulReg.value % Pow2(w) + nextMulReg.value / Pow2(w) * Pow2(w)              ==:| trivial |:
        nextMulReg.value
      }.qed
        
      

      // mulReg % Pow2(w - step * mulUnroll) == in1 / Pow2(step * mulUnroll) 
      {
        regs_next.mulRegReg.value % Pow2(width - count_next * mulUnroll) ==:| trivial |:
        nextMulReg.value % Pow2(w - (regs.count + 1) * mulUnroll) ==:| mulReg_lower_bits(nextMulReg.value, mulReg.value, w, cfg, regs.count, inputs) |:
        in1.value / Pow2((regs.count + 1) * mulUnroll)     ==:| trivial |:
        in1.value / Pow2(count_next * mulUnroll)
      }.qed

      // nextMulReg / Pow2(w - (step + 1) * mulUnroll) == in1 % Pow2((step + 1) * mulUnroll) * in2)
      {
        regs_next.mulRegReg.value / Pow2(width - count_next * mulUnroll) ==:| trivial |:
        nextMulReg.value % Pow2(w - (regs.count + 1) * mulUnroll) ==:| mulReg_higher_bits(nextMulReg, mulReg, w, cfg, regs.count, inputs) |:
        in1.value / Pow2((regs.count + 1) * mulUnroll)     ==:| trivial |:
        in1.value % Pow2(count_next * mulUnroll) * in2.value
      }.qed

      {
        regs_next.mulRegReg.value ==:| trivial |:
        in1.value % Pow2(count_next * mulUnroll) * in2.value + in1.value / Pow2(count_next * mulUnroll)
      }.qed 

     
    }
    val outMul = ((regs.state & (s_done_mul ^ s_done_div)) === (s_done_mul & ~s_done_div))
    io_resp_valid = io_resp_valid := (regs.state === s_done_mul)
    if (when((inputs.io_resp_ready && io_resp_valid))) state_next = state_next := s_ready
    io_req_ready = io_req_ready := (regs.state === s_ready)
    if (when((io_req_ready && inputs.io_req_valid))) {
      state_next = state_next := Mux(cmdMul, s_mul, s_ready)
      isHi_next = isHi_next := cmdHi
      resHi_next = resHi_next := Lit(false).B
      count_next = count_next := (if (fastMulW) Mux((cmdMul && halfWidth(inputs.io_req_bits_dw)), Lit(((w / mulUnroll) / 2)).U, Lit(0).U) else Lit(0).U)
      neg_out_next = neg_out_next := Mux(cmdHi, lhs_sign, (lhs_sign =/= rhs_sign))
      divisor_next = divisor_next := Cat(rhs_sign, rhs_in)
      remainder_next = remainder_next := lhs_in
      req_tag_next = req_tag_next := inputs.io_req_bits_tag
      req_dw_next = req_dw_next := inputs.io_req_bits_dw
      req_fn_next = req_fn_next := inputs.io_req_bits_fn
      req_in1_next = req_in1_next := inputs.io_req_bits_in1
      req_in2_next = req_in2_next := inputs.io_req_bits_in2
    }
    val loOut = Mux(((Lit(fastMulW).B && halfWidth(regs.req_dw)) && outMul), result((w - 1), (w / 2)), result(((w / 2) - 1), 0))
    val hiOut = Mux(halfWidth(regs.req_dw), Fill((w / 2), loOut(((w / 2) - 1))), result((w - 1), (w / 2)))
    io_resp_bits_tag = io_resp_bits_tag := regs.req_tag
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
        req_tag_next,
        req_dw_next,
        req_fn_next,
        req_in1_next,
        req_in2_next,
        count_next,
        neg_out_next,
        isHi_next,
        resHi_next,
        divisor_next,
        remainder_next,
        mulRegReg_next
      )
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts) && postCond(outputs, regNexts)
  }

  @library
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
  @library
  def run(inputs: MulInputs, randomInitValue: MulRegs): (MulOutputs, MulRegs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = MulRegs(
      Lit(0, 3).U,
      randomInitValue.req_tag,
      randomInitValue.req_dw,
      randomInitValue.req_fn,
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