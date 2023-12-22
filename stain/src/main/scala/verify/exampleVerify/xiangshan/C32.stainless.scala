package exampleVerify.xiangshan

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class C32Inputs(io_in: List[UInt])
case class C32Outputs(io_out: List[UInt])
case class C32Regs()

case class C32() {
  def inputsRequire(inputs: C32Inputs): Boolean = inputs match {
    case C32Inputs(io_in) =>
      io_in.length == 3 &&
      io_in.forall(_.width == 1)
  }
  def outputsRequire(outputs: C32Outputs): Boolean = outputs match {
    case C32Outputs(io_out) =>
      io_out.length == 2 &&
      io_out.forall(_.width == 1)
  }
  def regsRequire(regs: C32Regs): Boolean = regs match {
    case C32Regs() =>
      true
  }

  def trans(inputs: C32Inputs, regs: C32Regs): (C32Outputs, C32Regs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_out = List.fill(2)(UInt.empty(1))

    // body
    var temp = List.fill(1)(UInt.empty(2))
    (0 until temp.length).foreach((i: BigInt) => {
      val (a, b, cin) = (inputs.io_in(0)(i), inputs.io_in(1)(i), inputs.io_in(2)(i))
      val a_xor_b = (a ^ b)
      val a_and_b = (a & b)
      val sum = (a_xor_b ^ cin)
      val cout = (a_and_b | (a_xor_b & cin))
      temp = temp.updated(i, Cat(cout, sum))
    })
    (0 until io_out.length).foreach((i: BigInt) => io_out = io_out.updated(i, Cat(temp.reverse.map((x$4: UInt) => x$4(i)))))

    (
      C32Outputs(io_out),
      C32Regs()
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }

  def c32Run(timeout: Int, inputs: C32Inputs, regInit: C32Regs): (C32Outputs, C32Regs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      c32Run(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
  def run(inputs: C32Inputs, randomInitValue: C32Regs): (C32Outputs, C32Regs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = C32Regs()
    c32Run(100, inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}