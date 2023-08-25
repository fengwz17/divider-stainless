package UIntExample

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

case class Inputs(
    io_in1: UInt,
    io_in2: UInt
)

case class Outputs(
    io_outQ: UInt,
    io_outR: UInt
)

case class Regs(
    state: UInt,
    R: UInt,
    Q: UInt,
    cnt: UInt
)

case class TestRocketChipUIntRQ(len: BigInt = 64) {

  // variables width
  @library
  def inputsRequire(inputs: Inputs): Boolean = inputs match {
    case Inputs(io_in1, io_in2) =>
      len >= 1 &&
      io_in1.width == len &&
      io_in2.width == len
  }
  @library
  def outputsRequire(outputs: Outputs): Boolean = outputs match {
    case Outputs(io_outQ, io_outR) =>
      io_outQ.width == len &&
      io_outR.width == len
  }
  @library
  def regsRequire(regs: Regs): Boolean = {
      regs.state.width == 2 &&
      regs.R.width == 2 * len &&
      regs.Q.width == len &&
      regs.cnt.width == len
  }

  // pre-condition for proof
  def preCond(inputs: Inputs, regs: Regs): Boolean = {
    regs.cnt.value >= BigInt(0) && regs.cnt.value <= len - 1
    && (regs.R.value + inputs.io_in2.value * regs.Q.value * Pow2(len - regs.cnt.value + 1) == inputs.io_in1.value)
  } 

  // post-condition for proof
  def postCond(inputs: Inputs, regs: Regs, outputs: Outputs): Boolean = {
    regs.cnt.value >= BigInt(0) && regs.cnt.value <= len
    && (regs.R.value + inputs.io_in2.value * regs.Q.value * Pow2(len - regs.cnt.value + 1) == inputs.io_in1.value)
    // && (outputs.io_outQ.value == regs.Q.value) && (outputs.io_outR.value == regs.R.value)
  }

  // One clock cycle
  def trans(inputs: Inputs, regs: Regs): (Outputs, Regs) = {
    require(inputsRequire(inputs) && regsRequire(regs) && preCond(inputs, regs))

    // output
    var io_outR = UInt.empty(len)
    var io_outQ = UInt.empty(len)

    // reg next
    var state_next     = regs.state
    var R_next         = regs.R
    var Q_next         = regs.Q
    var cnt_next       = regs.cnt

    val cnt = regs.cnt
    val R = regs.R
    val Q = regs.Q
    val state = regs.state

    // Enum(3)
    val (s_init, s_compute, s_finish) = (Lit(0, 2).U, Lit(1, 2).U, Lit(2, 2).U)
    
    if (when(state === s_init)) {
      R_next = R_next := inputs.io_in1
      Q_next = Q_next := Lit(0, len).U
      cnt_next = cnt_next := Lit(0, len).U
      state_next = state_next := s_compute
    } 
    else if (when(state === s_compute)) {
      val sub = Lit(len).U - cnt
      val shift = (inputs.io_in2 << sub)(2 * len - 1, 0)
      val subtractor = R - shift
      val less = subtractor(2 * len - 1)

      R_next = R_next := Mux(less, R, subtractor)
      Q_next = Q_next := Mux(less, Q << Lit(1).U, (Q << Lit(1).U) + Lit(1).U)
      cnt_next = cnt_next := cnt + Lit(1).U

      assert(inputs.io_in2.width == len)
      assert(sub.value <= len)
      val p_tmp = inputs.io_in2 << sub
      assert(p_tmp.value < Pow2(len + len - cnt.value))
      Pow2.Pow2Monotone(2 * len, 2 * len - cnt.value)
      assert(Pow2(2 * len - cnt.value) <= Pow2(2 * len))
      assert(p_tmp.value < Pow2(2 * len))
      assert((inputs.io_in2 << sub).value % Pow2(2 * len) == (inputs.io_in2 << sub).value)

      {
        R_next.value ==:| trivial |:
        R.value - subtractor.value * (1 - less.asBigInt)        ==:| trivial |:
        R.value - (R.value - shift.value) * (1 - less.asBigInt) ==:| trivial |:
        R.value - (R.value - (inputs.io_in2 << sub).value % Pow2(2 * len) * (1 - less.asBigInt)) ==:| trivial |:
        R.value - (R.value - (inputs.io_in2 << sub).value  * (1 - less.asBigInt))                ==:| trivial |:
        R.value - (R.value - inputs.io_in2.value * Pow2(sub.value) * (1 - less.asBigInt))        ==:| trivial |:
        R.value - (R.value - inputs.io_in2.value * Pow2(len - cnt.value) * (1 - less.asBigInt))
      }

      if (when(cnt_next === Lit(len).U)) { state_next := s_finish }
    } 
    else if (when(state === s_finish)) {
        state_next = state_next := s_finish
    }

    io_outQ = io_outQ := Q_next
    io_outR = io_outR := R_next

    assert(io_outQ.width == len)
    assert(io_outR.width == len)

    assert(state_next.width == 2)
    assert(R_next.width == 2 * len)
    assert(Q_next.width == len)
    assert(cnt_next.width == len)

    (
      Outputs(io_outQ, io_outR),
      Regs(state_next, R_next, Q_next, cnt_next)
    )
    // }

  } ensuring { case (outputs, regNexts) => 
    outputsRequire(outputs) && regsRequire(regNexts) && postCond(inputs, regNexts, outputs)
  }

  @ignore
  def Run(timeout: BigInt, inputs: Inputs, regInit: Regs): (Outputs, Regs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))

    val (newOutputs, newRegs) = trans(inputs, regInit)

    if (timeout > 1) {
      Run(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}
