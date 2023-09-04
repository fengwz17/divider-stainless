package example.xiangshan

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class DividerInputs(
    io_in_valid: Bool,
    io_in_bits: List[UInt],
    io_sign: Bool,
    io_out_ready: Bool
)
case class DividerOutputs(
    io_in_ready: Bool,
    io_out_valid: Bool,
    io_out_bits: UInt
)
case class DividerRegs(
    state: UInt,
    shiftReg: UInt,
    aSignReg: Bool,
    qSignReg: Bool,
    bReg: UInt,
    aValx2Reg: UInt,
    cnt: UInt
)

case class Divider(len: BigInt = 64) {
  def inputsRequire(inputs: DividerInputs): Boolean = inputs match {
    case DividerInputs(io_in_valid, io_in_bits, io_sign, io_out_ready) =>
      io_in_bits.length == 2 &&
      io_in_bits.forall(_.width == len)
  }
  def outputsRequire(outputs: DividerOutputs): Boolean = outputs match {
    case DividerOutputs(io_in_ready, io_out_valid, io_out_bits) =>
      io_out_bits.width == (len * 2)
  }
  def regsRequire(regs: DividerRegs): Boolean = regs match {
    case DividerRegs(state, shiftReg, aSignReg, qSignReg, bReg, aValx2Reg, cnt) =>
      state.width == 3 &&
      shiftReg.width == (1 + (len * 2)) &&
      // Unknown size bReg &&
      // Unknown size aValx2Reg &&
      cnt.width == bitLength(len)
  }

  def trans(inputs: DividerInputs, regs: DividerRegs): (DividerOutputs, DividerRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_in_ready = Bool.empty()
    var io_out_valid = Bool.empty()
    var io_out_bits = UInt.empty((len * 2))
    // reg next
    var state_next = regs.state
    var shiftReg_next = regs.shiftReg
    var aSignReg_next = regs.aSignReg
    var qSignReg_next = regs.qSignReg
    var bReg_next = regs.bReg
    var aValx2Reg_next = regs.aValx2Reg
    var cnt_next = regs.cnt

    // body
    def abs(a: UInt, sign: Bool): (Bool, UInt) = {
      val s = (a((len - 1)) && sign)
      (s, Mux(s, -a, a))
    }
    val (s_idle, s_log2, s_shift, s_compute, s_finish) = (Lit(0, 3).U, Lit(1, 3).U, Lit(2, 3).U, Lit(3, 3).U, Lit(4, 3).U)
    val (a, b) = (inputs.io_in_bits(0), inputs.io_in_bits(1))
    val divBy0 = (b === Lit(0, len).U)
    val hi = regs.shiftReg((len * 2), len)
    val lo = regs.shiftReg((len - 1), 0)
    val (aSign, aVal) = abs(a, inputs.io_sign)
    val (bSign, bVal) = abs(b, inputs.io_sign)
    val canSkipShift = ((Lit(len).U + Log2(regs.bReg)) - Log2(regs.aValx2Reg))
    val enough = (hi.asUInt >= regs.bReg.asUInt)
    val r = hi(len, 1)
    val resQ = Mux(regs.qSignReg, -lo, lo)
    val resR = Mux(regs.aSignReg, -r, r)
    io_out_bits = io_out_bits := Cat(resR, resQ)
    io_out_valid = io_out_valid := (regs.state === s_finish)
    io_in_ready = io_in_ready := (regs.state === s_idle)
    val newReq = ((regs.state === s_idle) && (io_in_ready && inputs.io_in_valid))
    if (when(newReq)) {
      aSignReg_next = aSignReg_next := aSign
    }
    if (when(newReq)) {
      qSignReg_next = qSignReg_next := ((aSign ^ bSign) && !divBy0)
    }
    if (when(newReq)) {
      bReg_next = bReg_next := bVal
    }
    if (when(newReq)) {
      aValx2Reg_next = aValx2Reg_next := Cat(aVal, Lit(b0).U)
    }
    if (when(newReq)) {
      state_next = state_next := s_log2
    } else if (when((regs.state === s_log2))) {
      cnt_next = cnt_next := Mux(divBy0, Lit(0).U, Mux((canSkipShift >= Lit((len - 1)).U), Lit((len - 1)).U, canSkipShift))
      state_next = state_next := s_shift
    } else if (when((regs.state === s_shift))) {
      shiftReg_next = shiftReg_next := (regs.aValx2Reg << regs.cnt)
      state_next = state_next := s_compute
    } else if (when((regs.state === s_compute))) {
      shiftReg_next = shiftReg_next := Cat(List(Mux(enough, (hi - regs.bReg), hi)((len - 1), 0), lo, enough))
      cnt_next = cnt_next := (regs.cnt + Lit(1).U)
      if (when((regs.cnt === Lit((len - 1)).U))) {
        state_next = state_next := s_finish
      }
    } else if (when((regs.state === s_finish))) {
      if (when(inputs.io_out_ready)) {
        state_next = state_next := s_idle
      }
    }

    (
      DividerOutputs(
        io_in_ready,
        io_out_valid,
        io_out_bits
      ),
      DividerRegs(
        state_next,
        shiftReg_next,
        aSignReg_next,
        qSignReg_next,
        bReg_next,
        aValx2Reg_next,
        cnt_next
      )
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }

  def dividerRun(timeout: Int, inputs: DividerInputs, regInit: DividerRegs): (DividerOutputs, DividerRegs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      dividerRun(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
  def run(inputs: DividerInputs, randomInitValue: DividerRegs): (DividerOutputs, DividerRegs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = DividerRegs(
      Lit(0, 3).U,
      randomInitValue.shiftReg,
      randomInitValue.aSignReg,
      randomInitValue.qSignReg,
      randomInitValue.bReg,
      randomInitValue.aValx2Reg,
      Lit(0, bitLength(len)).U
    )
    dividerRun(100, inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}