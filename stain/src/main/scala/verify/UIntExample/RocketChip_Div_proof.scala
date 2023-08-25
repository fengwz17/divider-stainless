package UIntExample

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._
  
// case class MultiplierReq(dataBits: Int, tagBits: Int) extends Bundle {
//   val fn  = UInt(4.W) // aluFn.SZ_ALU_FN
//   val dw  = UInt(1.W)
//   val in1 = UInt(dataBits.W)
//   val in2 = UInt(dataBits.W)
//   val tag = UInt(tagBits.W)
// }

// class MultiplierResp(dataBits: Int, tagBits: Int) extends Bundle {
//   val data = UInt(dataBits.W)
//   val tag  = UInt(tagBits.W)
// }

// class MultiplierIO(val dataBits: Int, val tagBits: Int) extends Bundle {
//   val req  = Flipped(Decoupled(new MultiplierReq(dataBits, tagBits)))
//   val resp = Decoupled(new MultiplierResp(dataBits, tagBits))
// }
case class MultiplierIO(
  in1: UInt,
  in2: UInt
)

case class Outputs(
  out: UInt
)

case class Regs(
  divisor: UInt,
  remainder: UInt,
  count: UInt,
  ghost_R: UInt,
  ghost_Q: UInt
)

case class MulDivParams(
    mulUnroll: BigInt = 1,
    divUnroll: BigInt = 1,
    mulEarlyOut: Boolean = false,
    divEarlyOut: Boolean = false,
    divEarlyOutGranularity: Int = 1
)

case class RocketChip_Div_proof(cfg: MulDivParams, width: BigInt, nXpr: Int = 32) {

  def inputsRequire(inputs: MultiplierIO): Boolean = inputs match {
    case MultiplierIO(in1, in2) =>
      width >= 0 &&
      in1.width == width &&
      in2.width == width
  }
  def outputsRequire(outputs: Outputs): Boolean = outputs match {
    case Outputs(out) =>
      width >= 0 &&
      out.width == width
  }

  def regsRequire(regs: Regs): Boolean = regs match {
    case Regs(divisor, remainder, count, ghost_R, ghost_Q) =>
      divisor.width == width &&
      remainder.width == 2 * width + 1 &&
      count.width == width &&
      ghost_R.width == width &&
      ghost_Q.width == width
  }

  def preCond(inputs: MultiplierIO, regs: Regs, cfg: MulDivParams): Boolean = {
    cfg.divUnroll >= 1 && cfg.divUnroll <= width && 
    (regs.count.value >= 0 && regs.count.value < width / cfg.divUnroll) &&
    (regs.divisor.value == inputs.in2.value) &&
    // (regs.count.value == BigInt(0) && regs.remainder.value == inputs.in1.value
    //   || regs.count.value >= BigInt(1) && regs.remainder.value >= BigInt(0)) &&
    (regs.count.value >= 0 && regs.remainder.value >= 0) &&
    (regs.ghost_R.value == regs.remainder.value / Pow2(regs.count.value)) &&
    (regs.ghost_Q.value == regs.remainder.value - regs.ghost_R.value * Pow2(regs.count.value)) &&
    (regs.ghost_R.value + inputs.in2.value * regs.ghost_Q.value * Pow2(width - regs.count.value + 1) == 2 * inputs.in1.value)
  }

  def postCond(inputs: MultiplierIO, outputs: Outputs, regs: Regs): Boolean = {
    // (regs.count.value >= 0 && regs.count.value < width / cfg.divUnroll) &&
    // (regs.divisor.value == inputs.in2.value) &&
    // (regs.count.value == BigInt(0) && regs.remainder.value == inputs.in1.value
    //   || regs.count.value >= BigInt(1) && regs.remainder.value >= BigInt(0)) &&
    // (regs.ghost_R.value == regs.remainder.value / Pow2(regs.count.value)) && 
    // (regs.ghost_Q.value == regs.remainder.value - regs.ghost_R.value * Pow2(regs.count.value)) &&
    // (regs.ghost_R.value + inputs.in2.value * regs.ghost_Q.value * Pow2(width - regs.count.value + 1) == 2 * inputs.in1.value)
    true
  }

  // lemmas
  @opaque @inlineOnce @library
  def fooWhilePropShiftRegRange(reg: BigInt, cnt: BigInt, len: BigInt): Unit = {
      require(len >= BigInt(1))
      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(reg >= 0)

      val hl = reg / Pow2(len)
      val ll = reg - hl * Pow2(len)
      {
        reg / Pow2(cnt)                                             ==:| trivial |:
        (ll + Pow2(len) * hl) / Pow2(cnt)                           ==:| Pow2.Pow2Mul(len, cnt, len - cnt) |:
        (ll + Pow2(cnt) * Pow2(len - cnt) * hl) / Pow2(cnt)         ==:| trivial |:
        Pow2(len - cnt) * hl + ll / Pow2(cnt)                       ==:| trivial |:
        reg / Pow2(len) * Pow2(len - cnt) + ll / Pow2(cnt)        
      }.qed
  }.ensuring(_ => reg / Pow2(cnt) >= reg / Pow2(len) * Pow2(len - cnt))

  @opaque @inlineOnce @library
  def fooWhilePropRshiftReg(a: BigInt, b: BigInt, len: BigInt, e:BigInt, cnt: BigInt, R: BigInt, reg: BigInt): Unit = {
      require(len >= BigInt(1))
      require(a < Pow2(len) && a >= BigInt(0))
      require(b < Pow2(len) && b > BigInt(0))

      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(0 <= e && e <= 1)
      require(reg >= 0)
      require(reg / Pow2(len) >= b * e)
      require(R >= 0)
      require(R == reg / Pow2(cnt))

      // val e = Mux(hi >= b, BigInt(1), BigInt(0))

      val R1 = R - b * Pow2(len - cnt) * e
      assert(R1 == reg / Pow2(cnt) - b * Pow2(len - cnt) * e)

      val shiftReg1 = 2 * reg - b * e * Pow2(len + 1) + e

      val cnt1 = cnt + BigInt(1)

      val h = reg / Pow2(cnt)
      val l = reg - h * Pow2(cnt)
      assert(reg == h * Pow2(cnt) + l)
      assert(l <= Pow2(cnt) - 1)
      assert(2 * l + e < Pow2(cnt + 1))
      
      // reg / Pow2(cnt) >= reg / Pow2(len) * Pow2(len - cnt)
      // h >= reg / Pow2(len) * Pow2(len - cnt), shifteg / Pow2(len) >= b * e
      // h >= b * e * Pow2(len - cnt)
      fooWhilePropShiftRegRange(reg, cnt, len)
      assert(h - b * e * Pow2(len - cnt) >= 0)

      cnt match {
        case cnt if cnt <= len => {
          shiftReg1 / Pow2(cnt + 1)                                                                        ==:| trivial |:
          (2 * reg - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)                                            ==:| trivial |:
          (2 * (h * Pow2(cnt) + l) - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)                            ==:| trivial |:
          (h * Pow2(cnt + 1) + 2 * l + e - b * e * Pow2(len + 1)) / Pow2(cnt + 1)                          ==:| Pow2.Pow2Mul(len + 1, len - cnt, cnt + 1) |:
          (h * Pow2(cnt + 1) + 2 * l + e - b * e * Pow2(len - cnt) * Pow2(cnt + 1)) / Pow2(cnt + 1)        ==:| trivial |:
          (Pow2(cnt + 1) * (h - b * e * Pow2(len - cnt)) + 2 * l + e) / Pow2(cnt + 1)                      ==:| {2 * l + e < Pow2(cnt + 1)} |:
          h - b * e * Pow2(len - cnt)                                                                      ==:| trivial |:
          (reg / Pow2(cnt)) - b * e * Pow2(len - cnt)                                                      ==:| trivial |:
          R1 
        }.qed
      }      
  }.ensuring(_ => R - b * Pow2(len - cnt) * e == (2 * reg - b * e * Pow2(len + 1) + e) / Pow2(cnt + 1)) 
 
  // trans
  def trans(cfg: MulDivParams, nXpr: BigInt = 32, inputs: MultiplierIO, regs: Regs): (Outputs, Regs) = {  
    require(inputsRequire(inputs) && regsRequire(regs) && preCond(inputs, regs, cfg))
    // def minDivLatency = (cfg.divUnroll > 0).option(if (cfg.divEarlyOut) 3 else 1 + w / cfg.divUnroll)
    // def minMulLatency = (cfg.mulUnroll > 0).option(if (cfg.mulEarlyOut) 2 else w / cfg.mulUnroll)
    // def minLatency: Int       = (minDivLatency ++ minMulLatency).min

    var out = UInt.empty(width)
    
    var divisor_next = regs.divisor
    var remainder_next = regs.remainder
    var count_next = regs.count
    var R_next = regs.ghost_R
    var Q_next = regs.ghost_Q

    val w = width
    val mulw = w

    // val count = log2Ceil(mulw / cfg.mulUnroll)
    val count = regs.count
    val divisor = regs.divisor
    val remainder = regs.remainder

    val (lhs_in, lhs_sign) = (inputs.in1, false)
    val (rhs_in, rhs_sign) = (inputs.in2, false)

    val subtractor        = remainder(2 * w, w) - divisor
    val result = remainder(w - 1, 0)

    /* 0 until cfg.divUnroll 
     * 0, 1, ..., cfg.divUnroll - 1
     */ 
    // val unrolls = ((0 until cfg.divUnroll) scanLeft remainder) { case (rem, i) =>
    //   // the special case for iteration 0 is to save HW, not for correctness
    //   val difference = if (i == 0) subtractor else rem(2 * w, w) - divisor(w - 1, 0)
    //   val less       = difference(w)
    //   Cat(Mux(less, rem(2 * w - 1, w), difference(w - 1, 0)), rem(w - 1, 0), !less)
    // }.tail

    val difference = subtractor
    val less       = difference(w)
    val unrolls    =    
      Cat(List(Mux(less, remainder(2 * w - 1, w), difference(w - 1, 0)), 
        remainder(w - 1, 0), (!less).asUInt))
    
    @library
    def unrolls_value(unrolls: UInt, remainder: UInt, difference: UInt, less: Bool): Unit = {
      val tmp_mux = Mux(less, remainder(2 * w - 1, w), difference(w - 1, 0))
    
      assert(remainder(w - 1, 0).value == (remainder.value / Pow2(0)) % Pow2(w))
      assert((!less).asUInt.value == (1 - less.asBigInt))
      val tmp_cat_list = List(Mux(less, remainder(2 * w - 1, w), difference(w - 1, 0)), 
          remainder(w - 1, 0), (!less).asUInt)
      val tmp_cat_list_tail = List(remainder(w - 1, 0), (!less).asUInt)
      assert(tmp_cat_list_tail == tmp_cat_list.tail)
      assert(tmp_cat_list_tail.size == 2)
      assert(tmp_cat_list_tail.head.width == remainder(w - 1, 0).width)
      assert(tmp_cat_list_tail.tail.head.width == (!less).asUInt.width)
      assert(Cat(tmp_cat_list_tail).width == w + 1)
      assert(tmp_cat_list == tmp_cat_list.head :: tmp_cat_list_tail)
      assert(tmp_cat_list.head == tmp_mux)
      assert(Cat(tmp_cat_list).value == tmp_mux.value * Pow2(w + 1) + Cat(tmp_cat_list_tail).value)
      assert(Cat(tmp_cat_list).value == tmp_mux.value * Pow2(w + 1) + Cat(List(remainder(w - 1, 0), (!less).asUInt)).value)

    } ensuring(_ => unrolls.value == (remainder.value / Pow2(w) - divisor.value * less.asBigInt) * Pow2(w + 1) 
        + remainder.value % Pow2(w) * 2 + (1 - less.asBigInt))
   
    // remainder := unrolls.last
    remainder_next = remainder_next := unrolls
    
    // ghost variables
    val h = remainder.value / Pow2(w)
    val l = remainder.value - h * Pow2(w)
    val negLess = 1 - less.asBigInt
    
    @library
    def remainder_update(remainder_next: UInt, remainder: UInt, inputs: MultiplierIO, negLess: BigInt): Unit = {
      {
        remainder_next.value ==:| trivial |:
        (remainder.value / Pow2(w) - inputs.in2.value * negLess) * Pow2(w + 1) + remainder.value % Pow2(w) * 2 + negLess ==:| trivial |:
        (h - inputs.in2.value * negLess) * Pow2(w + 1) + l * 2 + negLess ==:| trivial |:
        (h - inputs.in2.value * negLess) * Pow2(w) * 2 + l * 2 + negLess ==:| trivial |:
        (h * Pow2(w) - inputs.in2.value * negLess * Pow2(w) + l) * 2 + negLess ==:| trivial |:
        remainder.value * 2 - inputs.in2.value * negLess * Pow2(w) * 2 + negLess 
      }.qed
    }
    

    val ghost_R_next_value = regs.ghost_R.value - inputs.in2.value * Pow2(w - count.value) * negLess
    // {
    //   remainder_next.value / Pow2(count.value + 1) ==:| trivial |:
    //   (remainder.value * 2 - inputs.in2.value * negLess * Pow2(w) * 2 + negLess) / Pow2(count.value + 1) ==:| fooWhilePropRshiftReg(inputs.in1.value, inputs.in2.value, w, negLess, count.value, regs.ghost_R.value, remainder.value) |:
    //   regs.ghost_R.value - inputs.in2.value * Pow2(w - count.value) * negLess                            ==:| trivial |:
    //   ghost_R_next_value
    // }.qed

    val ghost_Q_next_value = regs.ghost_Q.value * 2 + negLess
    {
      remainder_next.value - ghost_R_next_value * Pow2(count.value + 1) ==:| trivial |:
      (remainder.value * 2 - inputs.in2.value * negLess * Pow2(w) * 2 + negLess) 
        - ghost_R_next_value * Pow2(count.value + 1) ==:| trivial |:
      (remainder.value * 2 - inputs.in2.value * negLess * Pow2(w) * 2 + negLess)
        - (regs.ghost_R.value - inputs.in2.value * Pow2(w - count.value) * negLess) * Pow2(count.value + 1) ==:| trivial |:
      remainder.value * 2 - regs.ghost_R.value * Pow2(count.value + 1) 
        - inputs.in2.value * negLess * Pow2(w) * 2 + inputs.in2.value * Pow2(w - count.value) * negLess * Pow2(count.value + 1) + negLess ==:| Pow2.Pow2Mul(w + 1, w - count.value, count.value + 1) |:
      remainder.value * 2 - regs.ghost_R.value * Pow2(count.value + 1) - inputs.in2.value * negLess * Pow2(w + 1) + inputs.in2.value * Pow2(w + 1) * negLess + negLess ==:| trivial |:
      remainder.value * 2 - regs.ghost_R.value * Pow2(count.value + 1) + negLess ==:| trivial |:
      remainder.value * 2 - regs.ghost_R.value * Pow2(count.value) * 2 + negLess ==:| trivial |:
      (remainder.value - regs.ghost_R.value * Pow2(count.value)) * 2 + negLess   ==:| trivial |:
      regs.ghost_Q.value * 2 + negLess                             ==:| trivial |:
      ghost_Q_next_value
    }.qed

    {
      ghost_R_next_value + inputs.in2.value * ghost_Q_next_value * Pow2(w - (regs.count.value + 1) + 1) ==:| trivial |:
      (regs.ghost_R.value - inputs.in2.value * Pow2(w - regs.count.value) * negLess) 
        + inputs.in2.value * (regs.ghost_Q.value * 2 + negLess) * Pow2(w - regs.count.value) ==:| trivial |:
      regs.ghost_R.value - inputs.in2.value * Pow2(w - regs.count.value) * negLess + inputs.in2.value * regs.ghost_Q.value * 2 * Pow2(w - regs.count.value) 
        + inputs.in2.value * negLess * Pow2(w - regs.count.value) ==:| trivial |:
      regs.ghost_R.value + inputs.in2.value * regs.ghost_Q.value * Pow2(w - regs.count.value + 1) ==:| trivial |:
      2 * inputs.in1.value
    }.qed

    R_next = UInt(ghost_R_next_value, R_next.width)
    Q_next = UInt(ghost_Q_next_value, Q_next.width)

    // count := count + 1.U
    count_next = count_next := count + Lit(1).U
    
    out = out := result
    
    
    (
      Outputs(out),
      Regs(divisor, remainder_next, count_next, R_next, Q_next)
    )

    // if (count_next < w / cfg.divUnroll) {
    //   Div(cfg, width, nXpr, inputs, regs_next, step_next)
    // }
    // else {
    //   (out, regs_next)
    // }
  } ensuring { case (outputs, regNexts) => 
    outputsRequire(outputs) && regsRequire(regNexts) && postCond(inputs, outputs, regNexts)
  }

  // @ignore
  // def Run(timeout: BigInt, inputs: Inputs, regInit: Regs): (Outputs, Regs) = {
  //   require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))

  //   val (newOutputs, newRegs) = trans(inputs, regInit)

  //   if (timeout > 1) {
  //     Run(timeout - 1, inputs, newRegs)
  //   } else {
  //     (newOutputs, newRegs)
  //   }
  // } ensuring { case (outputs, regNexts) =>
  //   outputsRequire(outputs) && regsRequire(regNexts)
  // }
}