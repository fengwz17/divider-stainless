package example.xiangshan

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class C53Inputs(io_in: List[UInt])
case class C53Outputs(io_out: List[UInt])
case class C53Regs()

case class C53() {
  def inputsRequire(inputs: C53Inputs): Boolean = inputs match {
    case C53Inputs(io_in) =>
      io_in.length == 5 &&
      io_in.forall(_.width == 1)
  }
  def outputsRequire(outputs: C53Outputs): Boolean = outputs match {
    case C53Outputs(io_out) =>
      io_out.length == 3 &&
      io_out.forall(_.width == 1)
  }
  def regsRequire(regs: C53Regs): Boolean = regs match {
    case C53Regs() =>
      true
  }

  def trans(inputs: C53Inputs, regs: C53Regs): (C53Outputs, C53Regs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_out = List.fill(3)(UInt.empty(1))

    // body
    val FAs0 = example.xiangshan.C32()
    var FAs0_io_in = List.fill(3)(UInt.empty(1))
    val FAs1 = example.xiangshan.C32()
    var FAs1_io_in = List.fill(3)(UInt.empty(1))
    FAs0_io_in = FAs0_io_in := inputs.io_in.take(3)
    val (FAs0TransOutputs, _) = C53.this.FAs0.trans(
      example.xiangshan.C32Inputs(FAs0_io_in),
      example.xiangshan.C32Regs()
    )
    val FAs0_io_out = FAs0TransOutputs.io_out
    var tmp1 = List(FAs0_io_out(0), inputs.io_in(3), inputs.io_in(4))
    FAs1_io_in = FAs1_io_in := tmp1
    val (FAs1TransOutputs, _) = C53.this.FAs1.trans(
      example.xiangshan.C32Inputs(FAs1_io_in),
      example.xiangshan.C32Regs()
    )
    val FAs1_io_out = FAs1TransOutputs.io_out
    var tmp2 = List(FAs1_io_out(0), FAs0_io_out(1), FAs1_io_out(1))
    io_out = io_out := tmp2

    (
      C53Outputs(io_out),
      C53Regs()
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }

  def c53Run(timeout: Int, inputs: C53Inputs, regInit: C53Regs): (C53Outputs, C53Regs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      c53Run(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
  def run(inputs: C53Inputs, randomInitValue: C53Regs): (C53Outputs, C53Regs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = C53Regs()
    c53Run(100, inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}