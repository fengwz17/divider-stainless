package verify

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import chicala._
import stainless.annotation.library


case class CarrySaveAdderMToN_Inputs(
    io_in: List[UInt]
)
case class CarrySaveAdderMToN_Outputs(
    io_out: List[UInt]
)

@opaque @library
case class CSA2_2(len: BigInt) {
  def inputsRequire(inputs: CarrySaveAdderMToN_Inputs): Boolean = inputs match {
    case CarrySaveAdderMToN_Inputs(io_in) =>
      io_in.length == 2 &&
      io_in.forall(_.width == len)
  }
  def outputsRequire(outputs: CarrySaveAdderMToN_Outputs): Boolean = outputs match {
    case CarrySaveAdderMToN_Outputs(io_out) =>
      io_out.length == 2 &&
      io_out.forall(_.width == len)
  }

  def trans(inputs: CarrySaveAdderMToN_Inputs): CarrySaveAdderMToN_Outputs = {
    require(inputsRequire(inputs))
    inputs match {
      case CarrySaveAdderMToN_Inputs(io_in) =>
        // output
        var io_out: List[UInt] = List.fill(2)(UInt(0, len))

        // begin
        var temp = List.fill(len)(UInt(0, 2))
        temp = until(0, temp.size).map { i =>
          val (a, b) = (io_in(0)(i), io_in(1)(i))
          val sum    = a ^ b
          val cout   = a & b
          Cat(cout, sum)
        }
        io_out = until(0, io_out.size).map { i => Cat(temp.reverse.map(_(i)).map(_.asUInt)) }

        // return
        CarrySaveAdderMToN_Outputs(io_out)
    }
  } ensuring (outputs => outputsRequire(outputs))
}

@opaque @library
case class CSA3_2(len: BigInt) {
  def inputsRequire(inputs: CarrySaveAdderMToN_Inputs): Boolean = inputs match {
    case CarrySaveAdderMToN_Inputs(io_in) =>
      io_in.length == 3 &&
      io_in.forall(_.width == len)
  }
  def outputsRequire(outputs: CarrySaveAdderMToN_Outputs): Boolean = outputs match {
    case CarrySaveAdderMToN_Outputs(io_out) =>
      io_out.length == 2 &&
      io_out.forall(_.width == len)
  }

  def trans(inputs: CarrySaveAdderMToN_Inputs): CarrySaveAdderMToN_Outputs = {
    require(inputsRequire(inputs))
    inputs match {
      case CarrySaveAdderMToN_Inputs(io_in) =>
        // output
        var io_out: List[UInt] = List.fill(2)(UInt(0, len))

        // begin
        var temp = List.fill(len)(UInt(0, 2))
        temp = until(0, temp.size).map { i =>
          val (a, b, cin) = (io_in(0)(i), io_in(1)(i), io_in(2)(i))
          val a_xor_b     = a ^ b
          val a_and_b     = a & b
          val sum         = a_xor_b ^ cin
          val cout        = a_and_b | (a_xor_b & cin)
          Cat(cout, sum)
        }
        io_out = until(0, io_out.size).map { i => Cat(temp.reverse.map(_(i)).map(_.asUInt)) }

        // return
        CarrySaveAdderMToN_Outputs(io_out)
    }
  } ensuring (outputs => outputsRequire(outputs))
}

@opaque @library
case class CSA5_3(len: BigInt) {
  def inputsRequire(inputs: CarrySaveAdderMToN_Inputs): Boolean = inputs match {
    case CarrySaveAdderMToN_Inputs(io_in) =>
      io_in.length == 5 &&
      io_in.forall(_.width == len)
  }
  def outputsRequire(outputs: CarrySaveAdderMToN_Outputs): Boolean = outputs match {
    case CarrySaveAdderMToN_Outputs(io_out) =>
      io_out.length == 3 &&
      io_out.forall(_.width == len)
  }

  def trans(inputs: CarrySaveAdderMToN_Inputs): CarrySaveAdderMToN_Outputs = {
    require(inputsRequire(inputs))
    inputs match {
      case CarrySaveAdderMToN_Inputs(io_in) =>
        // output
        var io_out: List[UInt] = List.fill(3)(UInt(0, len))

        // begin
        val FAs = List.fill(2)(CSA3_2(len))

        var FAs_0_io_in   = io_in.take(3)
        val FAs_0_outputs = FAs(0).trans(CarrySaveAdderMToN_Inputs(FAs_0_io_in))
        val FAs_0_io_out  = FAs_0_outputs.io_out

        var FAs_1_io_in   = List(FAs_0_io_out(0), io_in(3), io_in(4))
        val FAs_1_outputs = FAs(1).trans(CarrySaveAdderMToN_Inputs(FAs_1_io_in))
        val FAs_1_io_out  = FAs_1_outputs.io_out

        io_out = List(FAs_1_io_out(0), FAs_0_io_out(1), FAs_1_io_out(1))

        // return
        CarrySaveAdderMToN_Outputs(io_out)
    }
  } ensuring (outputs => outputsRequire(outputs))
}

object C22 { def apply() = CSA2_2(1) }
object C32 { def apply() = CSA3_2(1) }
object C53 { def apply() = CSA5_3(1) }
