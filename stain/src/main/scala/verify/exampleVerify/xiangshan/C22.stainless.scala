package exampleVerify.xiangshan

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class C22Inputs(io_in: List[UInt])
case class C22Outputs(io_out: List[UInt])
case class C22Regs()

case class C22() {
  def inputsRequire(inputs: C22Inputs): Boolean = inputs match {
    case C22Inputs(io_in) =>
      io_in.length == 2 &&
      io_in.forall(_.width == 1)
  }
  def outputsRequire(outputs: C22Outputs): Boolean = outputs match {
    case C22Outputs(io_out) =>
      io_out.length == 2 &&
      io_out.forall(_.width == 1)
  }
  def regsRequire(regs: C22Regs): Boolean = regs match {
    case C22Regs() =>
      true
  }

  def trans(inputs: C22Inputs, regs: C22Regs): (C22Outputs, C22Regs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_out = List.fill(2)(UInt.empty(1))

    // body
    var temp = List.fill(1)(UInt.empty(2))
    until(0, temp.length).foreach((i: BigInt) => {
      val (a, b) = (inputs.io_in(0)(i), inputs.io_in(1)(i))
      val sum = (a ^ b)
      val cout = (a & b)
      temp = temp.updated(i, Cat(cout, sum))
    })
    until(0, io_out.length).foreach((i: BigInt) => io_out = io_out.updated(i, Cat(temp.reverse.map((x$2: UInt) => x$2(i)))))

    (
      C22Outputs(io_out),
      C22Regs()
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }

  def c22Run(timeout: Int, inputs: C22Inputs, regInit: C22Regs): (C22Outputs, C22Regs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      c22Run(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
  def run(inputs: C22Inputs, randomInitValue: C22Regs): (C22Outputs, C22Regs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = C22Regs()
    c22Run(100, inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}