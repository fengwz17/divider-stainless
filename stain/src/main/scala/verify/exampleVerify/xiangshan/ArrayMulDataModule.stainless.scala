package example.xiangshan

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class ArrayMulDataModuleInputs(
    io_a: UInt,
    io_b: UInt,
    io_regEnables: List[Bool]
)
case class ArrayMulDataModuleOutputs(io_result: UInt)
case class ArrayMulDataModuleRegs()

case class ArrayMulDataModule(len: BigInt) {
  def inputsRequire(inputs: ArrayMulDataModuleInputs): Boolean = inputs match {
    case ArrayMulDataModuleInputs(io_a, io_b, io_regEnables) =>
      io_a.width == len &&
      io_b.width == len &&
      io_regEnables.length == 2
  }
  def outputsRequire(outputs: ArrayMulDataModuleOutputs): Boolean = outputs match {
    case ArrayMulDataModuleOutputs(io_result) =>
      io_result.width == (2 * len)
  }
  def regsRequire(regs: ArrayMulDataModuleRegs): Boolean = regs match {
    case ArrayMulDataModuleRegs() =>
      true
  }

  def preCond(inputs: ArrayMulDataModuleInputs, regs: ArrayMulDataModuleRegs): Boolean = {
    (len >= 5)
    && (i >= 0 && i < len && i % 2 == 0)
    && (a >= 0 && a <= Pow2(len - 2) - 1)
    && (b > 0 && b <= Pow2(len - 2) - 1)
    && (ksum == asum)
    && (asum == asumSign)
    && (a - (a / Pow2(i)) * Pow2(i) == asumUnsign)
    && (i >= BigInt(2) && last_x == ((BigInt(2) * a) / Pow2(i - 2) % Pow2(3)) || i < BigInt(2) && last_x == BigInt(0))
    && (asumUnsign == asumSign + (last_x / Pow2(2)) * Pow2(i))
    // val pp_sum_ksum_b = if (i < 2) 0 else Pow2(len + 3) * Pow2(i - 2) + ksum * b
    && (pp_sum == Pow2(len + 3) * Pow2neg(i - 2) + ksum * b)
  }

  def trans(inputs: ArrayMulDataModuleInputs, regs: ArrayMulDataModuleRegs): (ArrayMulDataModuleOutputs, ArrayMulDataModuleRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_result = UInt.empty((2 * len))

    // body
    def signExt(a: UInt, len: BigInt): UInt = {
      val aLen = a.width
      val signBit = a((aLen - 1))
      if ((aLen >= len)) a((len - 1), 0) else Cat(Fill((len - aLen), signBit), a)
    }
    val (a, b) = (inputs.io_a, inputs.io_b)
    var b_sext = UInt.empty((len + 1))
    var bx2 = UInt.empty((len + 1))
    var neg_b = UInt.empty((len + 1))
    var neg_bx2 = UInt.empty((len + 1))
    b_sext = b_sext := signExt(b, (len + 1))
    bx2 = bx2 := (b_sext << 1)
    neg_b = neg_b := ~b_sext.asUInt
    neg_bx2 = neg_bx2 := (neg_b << 1)
    val columns = List.fill((2 * len))(List())
    var last_x = Lit(0, 3).U
    Range(0, len, 2).foreach((i: BigInt) => {
      val x = if ((i == 0)) Cat(a(1, 0), Lit(0, 1).U) else if (((i + 1) == len)) signExt(a(i, (i - 1)), 3) else a((i + 1), (i - 1))
      val pp_temp = MuxLookup(x, Lit(0).U, List((Lit(1).U -> b_sext), (Lit(2).U -> b_sext), (Lit(3).U -> bx2), (Lit(4).U -> neg_bx2), (Lit(5).U -> neg_b), (Lit(6).U -> neg_b)))
      val s = pp_temp(len)
      val t = MuxLookup(last_x, Lit(0, 2).U, List((Lit(4).U -> Lit(2, 2).U), (Lit(5).U -> Lit(1, 2).U), (Lit(6).U -> Lit(1, 2).U)))
      last_x = x
      val (pp, weight) = if ((i == 0)) (Cat(List(~s, s, s, pp_temp)), 0) else if (((i == (len - 1)) || (i == (len - 1)))) (Cat(List(~s, pp_temp, t)), (i - 2)) else (Cat(List(Lit(1, 1).U, ~s, pp_temp, t)), (i - 2))
      (0 until columns.length).foreach((j: BigInt) => if (((j >= weight) && (j < (weight + pp.width)))) columns = columns.updated(j, (columns(j) :+ pp((j - weight)))))
    })
    def addOneColumn(col: List[Bool], cin: List[Bool]): (List[Bool], List[Bool], List[Bool]) = {
      val sum = List()
      val cout1 = List()
      val cout2 = List()
      if ((col.size == 1)) sum = (col ++ cin) else if ((col.size == 2)) {
        val c22 = example.xiangshan.C22()
        inputs.c22_io_in = inputs.c22_io_in := col
        sum = {
          val rassoc$1 = c22_io_out(0).asBool
          (rassoc$1 +: cin)
        }
        cout2 = List(c22_io_out(1).asBool)
      } else if ((col.size == 3)) {
        val c32 = example.xiangshan.C32()
        inputs.c32_io_in = inputs.c32_io_in := col
        sum = {
          val rassoc$2 = c32_io_out(0).asBool
          (rassoc$2 +: cin)
        }
        cout2 = List(c32_io_out(1).asBool)
      } else if ((col.size == 4)) {
        val c53 = example.xiangshan.C53()
        inputs.c53_io_in = inputs.c53_io_in := (col.take(4) :+ (if (cin.nonEmpty) cin.head else Lit(0).U))
        sum = (List(c53_io_out(0).asBool) ++ (if (cin.nonEmpty) cin.drop(1) else Nil))
        cout1 = List(c53_io_out(1).asBool)
        cout2 = List(c53_io_out(2).asBool)
      } else {
        val cin_1 = if (cin.nonEmpty) List(cin.head) else Nil
        val cin_2 = if (cin.nonEmpty) cin.drop(1) else Nil
        val (s_1, c_1_1, c_1_2) = addOneColumn(col.take(4), cin_1)
        val (s_2, c_2_1, c_2_2) = addOneColumn(col.drop(4), cin_2)
        sum = (s_1 ++ s_2)
        cout1 = (c_1_1 ++ c_2_1)
        cout2 = (c_1_2 ++ c_2_2)
      }
      (sum, cout1, cout2)
    }
    def addAll(cols: List[List[Bool]], depth: BigInt): (UInt, UInt) = {
      if (cols.forall((x$9: List[Bool]) => (x$9.size <= 2))) {
        val sum = Cat(cols.map((x$10: List[Bool]) => x$10(0)).reverse)
        val k = 0
        (0 until cols.size).foreach((i: BigInt) => if ((cols(i).size == 1)) k = (i + 1))
        val carry = Cat(cols.drop(k).map((x$11: List[Bool]) => x$11(1)).reverse)
        (sum, Cat(carry, Lit(0, k).U))
      } else {
        val columns_next = List.fill((2 * len))(List())
        val cout1 = List()
        val cout2 = List()
        (0 until cols.length).foreach((i: BigInt) => {
          val (s, c1, c2) = addOneColumn(cols(i), cout1)
          columns_next = columns_next.updated(i, (s ++ cout2))
          cout1 = c1
          cout2 = c2
        })
        val toNextLayer = columns_next
        addAll(toNextLayer, (depth + 1))
      }
    }
    val (sum, carry) = addAll(columns, 0)
    io_result = io_result := (sum + carry)

    (
      ArrayMulDataModuleOutputs(io_result),
      ArrayMulDataModuleRegs()
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }

  def arrayMulDataModuleRun(timeout: Int, inputs: ArrayMulDataModuleInputs, regInit: ArrayMulDataModuleRegs): (ArrayMulDataModuleOutputs, ArrayMulDataModuleRegs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      arrayMulDataModuleRun(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
  def run(inputs: ArrayMulDataModuleInputs, randomInitValue: ArrayMulDataModuleRegs): (ArrayMulDataModuleOutputs, ArrayMulDataModuleRegs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = ArrayMulDataModuleRegs()
    arrayMulDataModuleRun(100, inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}