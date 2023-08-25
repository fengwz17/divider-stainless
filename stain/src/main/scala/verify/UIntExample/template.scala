package UIntExample

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class DividerInputs(
    io_in_ready: Bool,
    io_in_valid: Bool,
    io_in_bits: Array[UInt],
    io_sign: Bool,
    io_out_ready: Bool,
    io_out_valid: Bool
)

case class DividerOutputs(
    io_out_bits: UInt,
    io_out_valid: Bool,
    io_in_ready: Bool
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
    case DividerInputs(io_in_ready, io_in_valid, io_in_bits, io_sign, io_out_ready, io_out_valid) =>
      len >= 0 &&
      io_in_bits.length == 2 &&
      io_in_bits(0).width == len &&
      io_in_bits(1).width == len
  }
  def outputsRequire(outputs: DividerOutputs): Boolean = outputs match {
    case DividerOutputs(io_out_bits, io_out_valid, io_in_ready) =>
      io_out_bits.width == len * 2
  }
  def regsRequire(regs: DividerRegs): Boolean = regs match {
    case DividerRegs(state, shiftReg, aSignReg, qSignReg, bReg, aValx2Reg, cnt) =>
      state.width == 3 &&
      shiftReg.width == 1 + len * 2 &&
      bReg.width == len &&
      aValx2Reg.width == len + 1 &&
      cnt.width == bitLength(len)
  }

  // pre- post- conditions of trans
  def preCond(inputs: DividerInputs, regs: DividerRegs): Boolean = {

  }

  def postCond(inputs: DividerInputs, outputs: DividerOutputs, regs: DividerRegs): Boolean = {

  }

  // lemmas

  // user defined function
  def abs(a: UInt, sign: Bool): (Bool, UInt) = {
    val s = a(len - 1) && sign
    (s, Mux(s, -a, a))
  }

  def trans(inputs: DividerInputs, regs: DividerRegs): (DividerOutputs, DividerRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))
    require(preCond(inputs, regs))

    // output
    var io_out_bits  = UInt.empty(len * 2)
    var io_out_valid = Bool.empty()
    var io_in_ready  = Bool.empty()
    // reg next
    var state_next     = regs.state
    var shiftReg_next  = regs.shiftReg
    var aSignReg_next  = regs.aSignReg
    var qSignReg_next  = regs.qSignReg
    var bReg_next      = regs.bReg
    var aValx2Reg_next = regs.aValx2Reg
    var cnt_next       = regs.cnt

    // Enum(5)
    val s_idle    = Lit(0, 3).U
    val s_log2    = Lit(1, 3).U
    val s_shift   = Lit(2, 3).U
    val s_compute = Lit(3, 3).U
    val s_finish  = Lit(4, 3).U

    val newReq = (regs.state === s_idle) && (inputs.io_in_ready && inputs.io_in_valid)

    val (a, b) = (inputs.io_in_bits(0), inputs.io_in_bits(1))
    val divBy0 = b === Lit(0, len).U

    val hi = regs.shiftReg(len * 2, len)
    val lo = regs.shiftReg(len - 1, 0)

    val (aSign, aVal) = abs(a, inputs.io_sign)
    val (bSign, bVal) = abs(b, inputs.io_sign)

    if (when(newReq)) {
      aSignReg_next = aSign
    } // val aSignReg = RegEnable(aSign, newReq)
    if (when(newReq)) {
      qSignReg_next = (aSign ^ bSign) && !divBy0
    } // val qSignReg = RegEnable((aSign ^ bSign) && !divBy0, newReq)
    if (when(newReq)) {
      bReg_next = bVal
    } // val aSignReg = RegEnable(aSign, newReq)
    if (when(newReq)) {
      aValx2Reg_next = Cat(aVal, Lit(0).U)
    } // val aValx2Reg = RegEnable(Cat(aVal, "b0".U), newReq)

    if (when(newReq)) {
      state_next = s_log2
    } else if (when(regs.state === s_log2)) {
      val canSkipShift = (Lit(len).U + Log2(bReg)) - Log2(regs.aValx2Reg)
      cnt_next = Mux(
        divBy0,
        Lit(0).U,
        Mux(
          canSkipShift >= Lit(len - 1).U,
          Lit(len - 1).U,
          canSkipShift
        )
      )
      state_next = s_shift

    } else if (when(regs.state === s_shift)) {
      shiftReg_next = aValx2Reg << regs.cnt
      state_next = s_compute
    } else if (when(regs.state === s_compute)) {
      val enough = hi >= bReg
      shiftReg_next = Cat(
        Mux(enough, hi - bReg, hi)(len - 1, 0),
        Cat(lo, enough)
      )
      cnt_next = regs.cnt + Lit(1).U
      if (when(cnt === Lit(len - 1).U)) { state_next = s_finish }
    } else if (when(regs.state === s_finish)) {
      if (when(io_out_ready)) {
        state_next = s_idle
      }
    }

    val r    = hi(len, 1)
    val resQ = Mux(qSignReg, -lo, lo)
    val resR = Mux(aSignReg, -r, r)
    io_out_bits = Cat(resR, resQ)

    io_out_valid = (regs.state === s_finish)
    io_in_ready = (regs.state === s_idle)

    (
      DividerOutputs(io_out_bits, io_out_valid, io_in_ready),
      DividerRegs(state_next, 
                  shiftReg_next, 
                  aSignReg_next, 
                  qSignReg_next, 
                  bReg_next, 
                  aValx2Reg_next, 
                  cnt_next)
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
      && postCond(inputs, outputs, regNexts)
    }

  def dividerRun(timeout: Int, inputs: DividerInputs, regInit: DividerRegs): (DividerOutputs, DividerRegs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    // require(state == s_compute)? 
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
    // require(state == s_compute)？
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
