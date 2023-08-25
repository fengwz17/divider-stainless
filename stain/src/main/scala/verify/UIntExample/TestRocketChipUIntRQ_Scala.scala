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
  def inputsRequire(inputs: Inputs): Boolean = inputs match {
    case Inputs(io_in1, io_in2) =>
      len >= 1 &&
      io_in1.width == len &&
      io_in2.width == len
  }
  def outputsRequire(outputs: Outputs): Boolean = outputs match {
    case Outputs(io_outQ, io_outR) =>
      io_outQ.width == len &&
      io_outR.width == len
  }
  def regsRequire(regs: Regs): Boolean = {
      regs.state.width == 2 &&
      regs.R.width == 2 * len &&
      regs.Q.width == len &&
      regs.cnt.width == len
  }

  // One clock cycle
  def trans(inputs: Inputs, regs: Regs): (Outputs, Regs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // (inputs, regs) match {
    //   case (
    //         DividerInputs(io_in_ready, io_in_valid, io_in_bits, io_sign, io_out_ready, io_out_valid),
    //         DividerRegs(state, shiftReg, aSignReg, qSignReg, bReg, aValx2Reg, cnt)
    //       ) =>

    // output
    var io_outR  = UInt.empty(len)
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
      R_next := inputs.io_in1
      Q_next := Lit(0, len).U
      cnt_next := Lit(0, len).U
      state_next := s_compute
    } 
    else if (when(state === s_compute)) {
      val sub = Lit(len).U - cnt
      val shift = (inputs.io_in1 << sub)(2 * len - 1, 0)
      val subtractor = R - shift
      val less = subtractor(2 * len - 1)

      R_next := Mux(less, R, subtractor)
      Q_next := Mux(less, Q << Lit(1).U, (Q << Lit(1).U) + Lit(1).U)
      cnt_next := cnt + Lit(1).U

      if (when(cnt_next === Lit(len - 1).U)) { state_next := s_finish }
    } 
    else if (when(state === s_finish)) {
        state_next := s_init
    }

    io_outQ := Q_next
    io_outR := R_next

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
    outputsRequire(outputs) && regsRequire(regNexts)
  }

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

  // def run(inputs: DividerInputs, randomInitValue: DividerRegs): (DividerOutputs, DividerRegs) = {
  //   require(inputsRequire(inputs) && regsRequire(randomInitValue))

  //   val regInit = DividerRegs(
  //     Lit(0, 3).U,
  //     randomInitValue.shiftReg,
  //     randomInitValue.aSignReg,
  //     randomInitValue.qSignReg,
  //     randomInitValue.bReg,
  //     randomInitValue.aValx2Reg,
  //     Lit(0, bitLength(len)).U
  //   )
  //   dividerRun(100, inputs, regInit)
  // } ensuring { case (outputs, regNexts) =>
  //   outputsRequire(outputs) && regsRequire(regNexts)
  // }
}
