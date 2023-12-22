package verify.exampleVerify

package running

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class ExampleInputs(
    io_valid: Bool,
    io_in: UInt
)
case class ExampleOutputs(
    io_out: UInt,
    io_ready: Bool
)
case class ExampleRegs(
    state: Bool,
    cnt: UInt,
    r: UInt
)

case class Example(len: BigInt) {
  def inputsRequire(inputs: ExampleInputs): Boolean = inputs match {
    case ExampleInputs(io_valid, io_in) =>
      io_in.width == len
  }
  def outputsRequire(outputs: ExampleOutputs): Boolean = outputs match {
    case ExampleOutputs(io_out, io_ready) =>
      io_out.width == len
  }
  def regsRequire(regs: ExampleRegs): Boolean = regs match {
    case ExampleRegs(state, cnt, r) =>
      cnt.width == len &&
      r.width == (2 * len)
  }

  def preCond(inputs: ExampleInputs, regs: ExampleRegs): Boolean = {
    regs.state.value == false &&
    len >= 2 &&
    0 <= regs.cnt.value && regs.cnt.value <= len 
  }

  def postCond(inputs: ExampleInputs, regs: ExampleRegs, outputs: ExampleOutputs): Boolean = {
    len >= 2 &&
    0 <= regs.cnt.value && regs.cnt.value <= len + 1

  }

  def trans(inputs: ExampleInputs, regs: ExampleRegs): (ExampleOutputs, ExampleRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs) && preCond(inputs, regs))

    // output
    var io_out = UInt.empty(len)
    var io_ready = Bool.empty()
    // reg next
    var state_next = regs.state
    var cnt_next = regs.cnt
    var r_next = regs.r

    // body
    val accum = regs.r(((2 * len) - 1), len)
    val prod = (regs.r(0) + accum)
    io_ready = io_ready := regs.state
    // assert(io_ready.value == true)

    if (when((io_ready))) {
      r_next = r_next := inputs.io_in
      state_next = state_next := Bool(false)
    } else {
      val tmp = Cat(prod, regs.r((len - 1), 1))
      r_next = r_next := Cat(Lit(0).U, tmp)
      assert(r_next.value == Cat(prod, regs.r(len - 1, 1)).value)

      cnt_next = cnt_next := (regs.cnt + Lit(1).U)
   
      io_out = io_out := regs.r
    // assert(r_next.value == prod.value * Pow2(len - 1) + regs.r.value / 2)

      if (when((regs.cnt === Lit((len)).U))) {
        state_next = state_next := Bool(true)
      }
    }

    (
      ExampleOutputs(
        io_out,
        io_ready
      ),
      ExampleRegs(
        state_next,
        cnt_next,
        r_next
      )
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts) && postCond(inputs, regNexts, outputs)
  }

  def preCondRun(inputs: ExampleInputs, regs: ExampleRegs) = {
    len > 0 &&
    0 <= regs.cnt.value && regs.cnt.value <= len &&
    regs.state.value == false
  }

  def prop(inputs: ExampleInputs, outputs: ExampleOutputs) = {
    outputs.io_out.value == inputs.io_in.value
  }

  @ignore   
  def exampleRun(inputs: ExampleInputs, regInit: ExampleRegs): (ExampleOutputs, ExampleRegs) = {
    require(inputsRequire(inputs) && regsRequire(regInit) && preCondRun(inputs, regInit))
    decreases(len - regInit.cnt.value) 
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (newRegs.cnt.value < len) {
      exampleRun(inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts) && prop(inputs, outputs)
  }
//   def run(inputs: ExampleInputs, randomInitValue: ExampleRegs): (ExampleOutputs, ExampleRegs) = {
//     require(inputsRequire(inputs) && regsRequire(randomInitValue))
//     val regInit = ExampleRegs(
//       Lit(true).B,
//       Lit(0, len).U,
//       randomInitValue.R
//     )
//     exampleRun(100, inputs, regInit)
//   } ensuring { case (outputs, regNexts) =>
//     outputsRequire(outputs) && regsRequire(regNexts)
//   }
}