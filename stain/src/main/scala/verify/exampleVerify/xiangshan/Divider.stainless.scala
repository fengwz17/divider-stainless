package exampleVerify.xiangshan

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

@library
case class DividerInputs(
    io_in_valid: Bool,
    // io_in_bits: List[UInt],
    io_in_bits_0: UInt,
    io_in_bits_1: UInt,
    io_sign: Bool,
    io_out_ready: Bool
)

@library
case class DividerOutputs(
    io_in_ready: Bool,
    io_out_valid: Bool,
    io_out_bits: UInt,
    io_out_bits_nexts_value: BigInt
)

@library
case class DividerRegs(
    state: UInt,
    shiftReg: UInt,
    aSignReg: Bool,
    qSignReg: Bool,
    bReg: UInt,
    aValx2Reg: UInt,
    cnt: UInt,

    // ghost vars
    ghost_r: BigInt,
    ghost_q: BigInt,
    cycle: BigInt
)

case class Divider(len: BigInt = 64) {
  require(len >= 1)
  @library
  def inputsRequire(inputs: DividerInputs): Boolean = inputs match {
    case DividerInputs(io_in_valid, io_in_bits_0, io_in_bits_1, io_sign, io_out_ready) =>
      // io_in_bits.length == 2 &&
      // io_in_bits.forall(_.width == len)
      io_in_bits_0.width == len && 0 <= io_in_bits_0.value && io_in_bits_0.value < Pow2(len) && 
      io_in_bits_1.width == len && 0 <= io_in_bits_1.value && io_in_bits_1.value < Pow2(len) && 
      io_in_valid.value == true
  }
  @library
  def outputsRequire(outputs: DividerOutputs): Boolean = outputs match {
    case DividerOutputs(io_in_ready, io_out_valid, io_out_bits, io_out_bits_next) =>
      io_out_bits.width == (len * 2) && io_out_bits.value >= 0 && io_out_bits.value < Pow2(len * 2)
  }
  @library
  def regsRequire(regs: DividerRegs): Boolean = regs match {
    case DividerRegs(state, shiftReg, aSignReg, qSignReg, bReg, aValx2Reg, cnt, ghost_r, ghost_q, cycle) =>
      state.width == 3 && state.value >= 0 && state.value < Pow2(3) &&
      shiftReg.width == (1 + (len * 2)) && shiftReg.value >= 0 && shiftReg.value < Pow2(1 + (len * 2)) &&
      // Unknown size bReg &&
      // Unknown size aValx2Reg &&
      cnt.width == bitLength(len) && cnt.value >= 0 && cnt.value <= len &&
      cycle >= 0 && cycle < 2 * len  &&
      0 <= regs.ghost_r && 0 <= regs.ghost_q
  }

  // @inline
  @library
  def preCond(inputs: DividerInputs, regs: DividerRegs): Boolean = {
    preCond_idle(inputs, regs) || preCond_log2(inputs, regs) || preCond_shift(inputs, regs) || 
      preCond_compt(inputs, regs) || preCond_finish(inputs, regs)
  }
  // @inline
  @library
  def postCond(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs, outputs: DividerOutputs): Boolean = {
    ((regs.state.value < BigInt(4)) && (regs.cnt.value <= len - 1) && (postCond_idle(inputs, regs, regNexts) && postCond_log2(inputs, regs, regNexts) && postCond_shift(inputs, regs, regNexts) && 
    postCond_compt(inputs, regs, regNexts, outputs))) ||
      (regs.state.value == BigInt(4) && regs.cnt.value == len && postCond_finish(inputs, regs, regNexts, outputs))
  }
  
  // // @inline
  // def preCond(inputs: DividerInputs, regs: DividerRegs): Boolean = {
  //   preCond_idle(inputs, regs)
  // }
  // // @inline
  // def postCond(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs, outputs: DividerOutputs): Boolean = {
  //   (regs.state.value < BigInt(4)) && (regs.cnt.value <= len - 1) && postCond_idle(inputs, regs, regNexts)
  // }
  @library
  def state_cond(regs: DividerRegs): Boolean = {
    regs.state.value == BigInt(0) ||
    regs.state.value == BigInt(1) ||
    regs.state.value == BigInt(2) ||
    regs.state.value == BigInt(3) ||
    regs.state.value == BigInt(4)
  }
  @inline @library
  def preCond_idle(inputs: DividerInputs, regs: DividerRegs): Boolean = {
    regs.state.value == BigInt(0) && regs.cnt.value == BigInt(0)
  }
  @inline @library
  def postCond_idle(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs): Boolean = {
    // (io_in_valid == true) => (preCond_idle => preCond_log2) 
    // (io_in_valid == false) => preCond_idle
    regNexts.cycle == regs.cycle + 1 &&
    !preCond_idle(inputs, regs) || preCond_log2(inputs, regNexts)
  }
  @inline @library
  def preCond_log2(inputs: DividerInputs, regs: DividerRegs): Boolean = {
    val (a, b) = (inputs.io_in_bits_0, inputs.io_in_bits_1)
    val (aSign, aVal) = abs(a, inputs.io_sign)
    val (bSign, bVal) = abs(b, inputs.io_sign)
    val divBy0 = (b === Lit(0, len).U)
    regs.state.value == BigInt(1) && regs.cnt.value == BigInt(0) &&
    regs.aSignReg.value == aSign.value &&
    regs.qSignReg.value == ((aSign ^ bSign) && !divBy0).value &&
    regs.bReg.value == bVal.value &&
    regs.aValx2Reg.value == aVal.value * 2
  }
  @inline @library
  def postCond_log2(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs): Boolean = {
    regNexts.cycle == regs.cycle + 1 &&
    !preCond_log2(inputs, regs) || preCond_idle(inputs, regNexts)
  }
  @inline @library
  def preCond_shift(inputs: DividerInputs, regs: DividerRegs): Boolean = {
    val (a, b) = (inputs.io_in_bits_0, inputs.io_in_bits_1)
    val (aSign, aVal) = abs(a, inputs.io_sign)
    val (bSign, bVal) = abs(b, inputs.io_sign)
    val divBy0 = (b === Lit(0, len).U)
    val canSkipShift = ((Lit(len).U + Log2(regs.bReg)) - Log2(regs.aValx2Reg))
    aVal.value >= BigInt(0) && bVal.value >= BigInt(0) &&
    regs.aSignReg.value == aSign.value &&
    regs.qSignReg.value == ((aSign ^ bSign) && !divBy0).value &&
    regs.bReg.value == bVal.value &&
    regs.aValx2Reg.value == aVal.value * 2 &&
    regs.state.value == BigInt(2) && 
    regs.cnt.value == (Mux(divBy0, Lit(0).U, Mux((canSkipShift >= Lit((len - 1)).U), Lit((len - 1)).U, canSkipShift))).value
  }
  @library
  def postCond_shift(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs): Boolean = {
    regNexts.cycle == regs.cycle + 1 &&
    !preCond_shift(inputs, regs) || preCond_compt(inputs, regNexts)
  }
  @library
  def preCond_compt(inputs: DividerInputs, regs: DividerRegs): Boolean = {
    // require(inputs.io_in_bits.length == 2 && inputs.io_in_bits.forall(_.width == len))
    // require(inputs.io_in_bits_0.width == len && inputs.io_in_bits_1.width == len)
    val (a, b) = (inputs.io_in_bits_0, inputs.io_in_bits_1)
    val (aSign, aVal) = abs(a, inputs.io_sign)
    val (bSign, bVal) = abs(b, inputs.io_sign)
    val divBy0 = (b === Lit(0, len).U)
    0 <= a.value && a.value < Pow2(len) &&
    0 <= b.value && b.value < Pow2(len) && 
    // regs.qSignReg.value == false &&
    // regs.aSignReg.value == false &&
    regs.aSignReg.value == aSign.value &&
    regs.qSignReg.value == ((aSign ^ bSign) && !divBy0).value &&
    regs.state.value == BigInt(3) &&
    // regs.bReg.value == in2 &&
    regs.bReg.value == bVal.value &&
    regs.aValx2Reg.value == aVal.value * 2 &&
    // regs.shiftReg.value == (regs.aValx2Reg << regs.cnt).value
    regs.shiftReg.value >= BigInt(0) &&
    0 <= regs.cnt.value && regs.cnt.value < len && 
    0 <= regs.ghost_r && 0 <= regs.ghost_q &&
    aVal.value == regs.bReg.value * regs.ghost_q * Pow2(len - regs.cnt.value) + regs.ghost_r && 
    regs.ghost_r == regs.shiftReg.value / Pow2(regs.cnt.value + 1) &&
    regs.shiftReg.value == regs.ghost_q + regs.ghost_r * Pow2(regs.cnt.value + 1)    
  }
  @library
  def postCond_compt(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs, outputs: DividerOutputs): Boolean = {
    // require(inputs.io_in_bits.length == 2 && inputs.io_in_bits.forall(_.width == len))
    // require(inputs.io_in_bits_0.width == len && inputs.io_in_bits_1.width == len)
    val in1 = inputs.io_in_bits_0.value
    val in2 = inputs.io_in_bits_1.value
    regNexts.cycle == regs.cycle + 1 &&
    regNexts.cnt.value == regs.cnt.value + 1 && 
    !preCond_compt(inputs, regs) || (
      (!(regs.cnt.value == (len - 1)) || preCond_finish(inputs, regNexts)) && 
        (!(regs.cnt.value < (len - 1)) || preCond_compt(inputs, regNexts)))
  }
  @library
  def preCond_finish(inputs: DividerInputs, regs: DividerRegs): Boolean = {
    regs.state.value == BigInt(4) && inputs.io_out_ready.value == true &&
    regs.cnt.value == len &&
    inputs.io_in_bits_0.value == inputs.io_in_bits_1.value * regs.shiftReg.value % Pow2(len) + regs.shiftReg.value / Pow2(len + 1) 
  }
  @library
  def postCond_finish(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs, outputs: DividerOutputs): Boolean = {
    val in1 = inputs.io_in_bits_0.value
    val in2 = inputs.io_in_bits_1.value
    !(regs.state.value == BigInt(4)) || (
      regNexts.cnt.value == len &&
      regNexts.state.value == BigInt(0) &&
      outputs.io_out_bits.value / Pow2(len) == regs.shiftReg.value / Pow2(len + 1) &&
      outputs.io_out_bits.value % Pow2(len) == regs.shiftReg.value % Pow2(len) &&
      in1 == in2 * outputs.io_out_bits(len - 1, 0).value + outputs.io_out_bits(2 * len - 1, len).value
    )
  }

  // lemma
  @opaque @library
  def lemma_r_q_invariant(inputs: DividerInputs, regs: DividerRegs, ghost_Q_next: BigInt, ghost_R_next: BigInt, e: BigInt): Unit = {
    // val in1 = a.value
    // val in2 = b.value
    // require(len >= BigInt(1))
    // require(in1 < Pow2(len) && in1 >= BigInt(0))
    // require(in2 < Pow2(len) && in2 > BigInt(0))
    val r = regs.ghost_r
    val q = regs.ghost_q
    val cnt = regs.cnt.value
    val r_next = ghost_R_next
    val q_next = ghost_Q_next
    val cnt_next = regs.cnt.value + 1
    // require(regs.cnt.value >= BigInt(0) && regs.cnt.value <= len - 1)
    // require(0 <= e && e <= 1)
    // require(regs.ghost_r >= 0)
    // require(inputs.io_in_bits_0.value 
    //   == inputs.io_in_bits_1.value * regs.ghost_q * Pow2(len - regs.cnt.value) + regs.ghost_r)
    // require(q_next == 2 * regs.ghost_q + e)
    // require(r_next == regs.ghost_r - inputs.io_in_bits_1.value * Pow2(len - regs.cnt.value - 1) * e)
    // require(cnt_next == regs.cnt.value + 1)
    val in1 = inputs.io_in_bits_0.value
    val in2 = inputs.io_in_bits_1.value
   
    {
      in2 * q_next * Pow2(len - cnt_next) + r_next                                        ==:| trivial |:
      in2 * (2 * q + e) * Pow2(len - cnt - 1) + (r - in2 * Pow2(len - cnt - 1) * e)       ==:| trivial |:
      in2 * (2 * q + e) * Pow2(len - cnt - 1) + r - in2 * Pow2(len - cnt - 1) * e         ==:| trivial |:
      in2 * q * Pow2(len - cnt) + in2 * e * Pow2(len - cnt - 1) + r - in2 * Pow2(len - cnt - 1) * e ==:| trivial |:
      in2 * q * Pow2(len - cnt) + r                                                       ==:| trivial |:
      in1
    }.qed

  }.ensuring(_ => inputs.io_in_bits_1.value * ghost_Q_next * Pow2(len - regs.cnt.value - 1) + ghost_R_next 
      == inputs.io_in_bits_0.value)

  @opaque 
  def lemma_shiftReg_range(shiftReg: BigInt, cnt: BigInt, len: BigInt): Unit = {
      require(len >= BigInt(1))
      require(cnt >= BigInt(0) && cnt <= len - 1)
      require(shiftReg >= 0)

      val hl = shiftReg / Pow2(len)
      val ll = shiftReg - hl * Pow2(len)
      {
        shiftReg / Pow2(cnt + 1)                                        ==:| trivial |:
        (ll + Pow2(len) * hl) / Pow2(cnt + 1)                           ==:| Pow2.Pow2Mul(len, cnt + 1, len - cnt - 1) |:
        (ll + Pow2(cnt + 1) * Pow2(len - cnt - 1) * hl) / Pow2(cnt + 1) ==:| trivial |:
        Pow2(len - cnt - 1) * hl + ll / Pow2(cnt + 1)                   ==:| trivial |:
        shiftReg / Pow2(len) * Pow2(len - cnt - 1) + ll / Pow2(cnt + 1)        
      }.qed
      // Pow2.Pow2Mul(len, cnt + 1, len - cnt - 1)
  }.ensuring(_ => shiftReg / Pow2(cnt + 1) >= shiftReg / Pow2(len) * Pow2(len - cnt - 1))

  // check again
  @opaque @library 
  def lemma_shiftReg_update(inputs: DividerInputs, regs: DividerRegs, shiftReg_next: UInt, enough: Bool): Unit = {
    val hi = regs.shiftReg((len * 2), len)
    val lo = regs.shiftReg((len - 1), 0)
    // require(shiftReg_next.value == 
    //   Cat(Mux(enough, hi - regs.bReg, hi)((len - 1), 0), Cat(lo, enough.asUInt)).value % Pow2(2 * len + 1))
    // require(enough.value == (hi.value >= regs.bReg.value))
    // require(inputs.io_in_bits_1.value == regs.bReg.value)
    // assert(Mux(enough, (hi - regs.bReg), hi).value == hi.value - regs.bReg.value * enough.asBigInt)
    val tmp_hi = Mux(enough, (hi - regs.bReg), hi)((len - 1), 0)
    val tmp_lo = Cat(lo, enough.asUInt)
    {
      shiftReg_next.value                       ==:| trivial |:
      Cat(tmp_hi, tmp_lo).value % Pow2(2 * len + 1) ==:| trivial |:
      Cat(tmp_hi, tmp_lo).value                     ==:| trivial |:
      tmp_hi.value * Pow2(tmp_lo.width) + tmp_lo.value ==:| trivial |:
      tmp_hi.value * Pow2(len + 1) + tmp_lo.value      ==:| trivial |:
      (Mux(enough, (hi - regs.bReg), hi).value % Pow2(len)) * Pow2(len + 1) + tmp_lo.value ==:| trivial |:
      Mux(enough, (hi - regs.bReg), hi).value * Pow2(len + 1) + tmp_lo.value ==:| trivial |:
      (hi.value - regs.bReg.value * enough.asBigInt) * Pow2(len + 1) + tmp_lo.value ==:| trivial |:
      (hi.value - regs.bReg.value * enough.asBigInt) * Pow2(len + 1) + lo.value * Pow2(enough.asUInt.width) + enough.asUInt.value ==:| trivial |:
      hi.value * Pow2(len + 1) - regs.bReg.value * enough.asBigInt * Pow2(len + 1) + lo.value * 2 + enough.asBigInt               ==:| trivial |:
      2 * regs.shiftReg.value - regs.bReg.value * enough.asBigInt * Pow2(len + 1) + enough.asBigInt
    }.qed
  }.ensuring(_ => shiftReg_next.value == 2 * regs.shiftReg.value - inputs.io_in_bits_1.value * enough.asBigInt * Pow2(len + 1) + enough.asBigInt)
    

  @opaque @library
  def lemma_r_shiftReg_invariant(inputs: DividerInputs, regs: DividerRegs, r_next: BigInt, shiftReg_next: UInt, cnt_next: UInt): Unit = {
    require(len >= BigInt(1))
    val a = inputs.io_in_bits_0.value
    val b = inputs.io_in_bits_1.value
    val cnt = regs.cnt.value
    val shiftReg = regs.shiftReg.value
    val R = regs.ghost_r
    val R1 = r_next
    val shiftReg1 = shiftReg_next.value
    val cnt1 = cnt_next.value
    val e = if (shiftReg / Pow2(len) >= b) BigInt(1) else BigInt(0)  

    // require(a < Pow2(len) && a >= BigInt(0))
    // require(b < Pow2(len) && b >= BigInt(0))

    // require(cnt >= BigInt(0) && cnt <= len - 1)
    // require(0 <= e && e <= 1)
    // require(shiftReg >= 0)
    // require(shiftReg / Pow2(len) >= b * e) // e == hi >= b == shiftReg / Pow2(len) >= b
    // require(R >= 0)
    // require(R == shiftReg / Pow2(cnt + 1))
    // require(R1 == R - b * Pow2(len - cnt - 1) * e)
    // require(shiftReg1 == 2 * shiftReg - b * e * Pow2(len + 1) + e)
    // require(cnt1 == cnt + 1)

    val h = shiftReg / Pow2(cnt + 1)
    val l = shiftReg - h * Pow2(cnt + 1)
    assert(shiftReg == h * Pow2(cnt + 1) + l)
    assert(l <= Pow2(cnt + 1) - 1)
    assert(2 * l + e < Pow2(cnt + 2))
    
    // shiftReg / Pow2(cnt + 1) >= shiftReg / Pow2(len) * Pow2(len - cnt - 1)
    // h >= shiftReg / Pow2(len) * Pow2(len - cnt - 1), shifteg / Pow2(len) >= b * e
    // h >= b * e * Pow2(len - cnt - 1)
    lemma_shiftReg_range(shiftReg, cnt, len)
    assert(h - b * e * Pow2(len - cnt - 1) >= 0)

    cnt match {
      case cnt if cnt <= len - 1 => {
        shiftReg1 / Pow2(cnt1 + 1)                                                                            ==:| trivial |:                                                                            
        shiftReg1 / Pow2(cnt + 2)                                                                             ==:| trivial |:
        (2 * shiftReg - b * e * Pow2(len + 1) + e) / Pow2(cnt + 2)                                            ==:| trivial |:
        (2 * (h * Pow2(cnt + 1) + l) - b * e * Pow2(len + 1) + e) / Pow2(cnt + 2)                             ==:| trivial |:
        (h * Pow2(cnt + 2) + 2 * l + e - b * e * Pow2(len + 1)) / Pow2(cnt + 2)                               ==:| Pow2.Pow2Mul(len + 1, len - cnt - 1, cnt + 2) |:
        (h * Pow2(cnt + 2) + 2 * l + e - b * e * Pow2(len - cnt - 1) * Pow2(cnt + 2)) / Pow2(cnt + 2)         ==:| trivial |:
        (Pow2(cnt + 2) * (h - b * e * Pow2(len - cnt - 1)) + 2 * l + e) / Pow2(cnt + 2)                       ==:| {2 * l + e < Pow2(cnt + 2)} |:
        h - b * e * Pow2(len - cnt - 1)                                                                       ==:| trivial |:
        (shiftReg / Pow2(cnt + 1)) - b * e * Pow2(len - cnt - 1)                                              ==:| trivial |:
        R1 
      }.qed
    }      
  }.ensuring(_ => r_next == shiftReg_next.value / Pow2(cnt_next.value + 1))
  
  @opaque @library
  def lemma_shiftReg_r_q_invariant(inputs: DividerInputs, regs: DividerRegs, cnt_next: UInt, shiftReg_next: UInt, r_next: BigInt, q_next: BigInt, e: BigInt): Unit = {
    val shiftReg1 = shiftReg_next.value
    val shiftReg = regs.shiftReg.value
    val b = inputs.io_in_bits_1.value
    val R = regs.ghost_r
    val R1 = r_next
    val Q = regs.ghost_q
    val Q1 = q_next
    val cnt = regs.cnt.value
    val cnt1 = cnt_next.value
    // require(len >= BigInt(1))
    // // require(a < Pow2(len) && a >= BigInt(0))
    // require(b < Pow2(len) && b > BigInt(0))

    // require(cnt >= BigInt(0) && cnt <= len - 1)
    // // require(0 <= e && e <= 1)
    // // require(shiftReg >= 0)
    // // require(R >= 0)
    // require(R1 == R - b * e * Pow2(len - cnt - 1))
    // require(shiftReg == Q + R * Pow2(cnt + 1))

    {
      shiftReg_next.value                                       ==:| trivial |:
      shiftReg1                                                 ==:| trivial |:
      2 * shiftReg - b * e * Pow2(len + 1) + e                  ==:| trivial |:
      2 * (R * Pow2(cnt + 1) + Q) - b * e * Pow2(len + 1) + e   ==:| trivial |:
      2 * Q + e + R * Pow2(cnt + 2) - b * e * Pow2(len + 1)     ==:| Pow2.Pow2Mul(len + 1, cnt + 2, len - cnt - 1) |:
      2 * Q + e + Pow2(cnt + 2) * (R - b * e * Pow2(len - cnt - 1)) ==:| trivial |:
      R1 * Pow2(cnt1 + 1) + Q1                                      ==:| trivial |:
      r_next * Pow2(cnt_next.value + 1) + q_next
    }.qed
  }.ensuring(_ => shiftReg_next.value == r_next * Pow2(cnt_next.value + 1) + q_next)

  // inner function
  @library
  def abs(a: UInt, sign: Bool): (Bool, UInt) = {
    // require(a.width == len)
    val s = (a((len - 1)) && sign)
    (s, Mux(s, -a, a))
  } ensuring(res => res._2.value >= 0)

  @library
  def trans(inputs: DividerInputs, regs: DividerRegs): (DividerOutputs, DividerRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))
    require(preCond(inputs, regs))

    // output
    var io_in_ready = Bool.empty()
    var io_out_valid = Bool.empty()
    var io_out_bits = UInt.empty((len * 2))
    var io_out_bits_nexts_value = BigInt(0)
    // reg next
    var state_next = regs.state
    var shiftReg_next = regs.shiftReg
    var aSignReg_next = regs.aSignReg
    var qSignReg_next = regs.qSignReg
    var bReg_next = regs.bReg
    var aValx2Reg_next = regs.aValx2Reg
    var cnt_next = regs.cnt

    // ghost vars
    var ghost_r_next = regs.ghost_r
    var ghost_q_next = regs.ghost_q
    val cycle_next = regs.cycle + BigInt(1)

    // body
    val (s_idle, s_log2, s_shift, s_compute, s_finish) = (Lit(0, 3).U, Lit(1, 3).U, Lit(2, 3).U, Lit(3, 3).U, Lit(4, 3).U)
    val (a, b) = (inputs.io_in_bits_0, inputs.io_in_bits_1)

    assert(a.value == inputs.io_in_bits_0.value)
    assert(b.value == inputs.io_in_bits_1.value)
    // assert(a.width == len && b.width == len)
    
    val divBy0 = (b === Lit(0, len).U)
    val hi = regs.shiftReg((len * 2), len)
    val lo = regs.shiftReg((len - 1), 0)
    val (aSign, aVal) = abs(a, inputs.io_sign)
    val (bSign, bVal) = abs(b, inputs.io_sign)
    assert(aVal.value >= 0 && bVal.value >= 0)

    // if b.length >= a.length, canSkipShift >= len - 1
    val canSkipShift = ((Lit(len).U + Log2(regs.bReg)) - Log2(regs.aValx2Reg))
    assert(regs.aValx2Reg.value < Pow2(len + 1) && regs.aValx2Reg.value >= 0)
    Log2.lemma_Log2LePow2(regs.aValx2Reg, len + 1)
    assert(Log2(regs.aValx2Reg).value <= len)
    assert(canSkipShift.value >= 0)
    val enough = (hi.asUInt >= regs.bReg.asUInt)
    assert(enough.value == (hi.value >= regs.bReg.value))
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
      aValx2Reg_next = aValx2Reg_next := Cat(aVal, Lit(0).U)
    }
    if (when(newReq)) {
      state_next = state_next := s_log2
    } else if (when((regs.state === s_log2))) {
      cnt_next = cnt_next := Mux(divBy0, Lit(0).U, Mux((canSkipShift >= Lit((len - 1)).U), Lit((len - 1)).U, canSkipShift))
      state_next = state_next := s_shift
      assert(cnt_next.value >= 0)
    } else if (when((regs.state === s_shift))) {
      shiftReg_next = shiftReg_next := (regs.aValx2Reg << regs.cnt)
      state_next = state_next := s_compute
      
      // proof state == s_shift -> preCond_compute
      assert(shiftReg_next.value >= 0)
      assert(0 <= cnt_next.value && cnt_next.value < len)
      ghost_r_next = aVal.value
      ghost_q_next = BigInt(0)
      assert(0 <= ghost_r_next && 0 <= ghost_q_next)
      assert(aVal.value == bReg_next.value * ghost_q_next * Pow2(len - regs.cnt.value) + ghost_r_next)
      // regs.ghost_r == regs.shiftReg.value / Pow2(regs.cnt.value + 1)
      {
        shiftReg_next.value / Pow2(cnt_next.value + 1) ==:| trivial |:
        (regs.aValx2Reg << regs.cnt).value / Pow2(cnt_next.value + 1) ==:| trivial |:
        (regs.aValx2Reg.value * Pow2(regs.cnt.value)) / Pow2(cnt_next.value + 1) ==:| trivial |:
        aVal.value * 2 * Pow2(cnt_next.value) / Pow2(cnt_next.value + 1) ==:| trivial |:
        aVal.value * Pow2(cnt_next.value + 1) / Pow2(cnt_next.value + 1) ==:| trivial |:
        aVal.value                                                       ==:| trivial |:
        ghost_r_next
      }.qed

    } else if (when((regs.state === s_compute))) {
      assert(preCond_compt(inputs, regs))
      // shiftReg_next = shiftReg_next := Cat(List(Mux(enough, (hi - regs.bReg), hi)((len - 1), 0), lo, enough))
      shiftReg_next = shiftReg_next := Cat(Mux(enough, (hi - regs.bReg), hi)((len - 1), 0), Cat(lo, enough.asUInt))
      cnt_next = cnt_next := (regs.cnt + Lit(1).U)   

      // assist check
      assert(shiftReg_next.width == (len * 2 + 1))
      assert(shiftReg_next.value == Cat(Mux(enough, (hi - regs.bReg), hi)((len - 1), 0), Cat(lo, enough.asUInt)).value % Pow2(2 * len + 1))
      // assert(io_out_bits.value == regs.shiftReg.value / Pow2(len + 1) * Pow2(len) + regs.shiftReg.value % Pow2(len))
      // io_out_bits_nexts_value = shiftReg_next.value / Pow2(len + 1) * Pow2(len) + shiftReg_next.value % Pow2(len) 

      // ghost vars update
      ghost_r_next = regs.ghost_r - regs.bReg.value * Pow2(len - regs.cnt.value - 1) * enough.asBigInt
      ghost_q_next = regs.ghost_q * 2 + enough.asBigInt

      // prove
      assert(regs.cnt.value >= BigInt(0) && regs.cnt.value <= len - 1)
      // prove in1 == in2 * q * Pow2(len - cnt) + r   
      assert(cnt_next.value == regs.cnt.value + 1)
      assert(ghost_r_next == regs.ghost_r - inputs.io_in_bits_1.value * Pow2(len - regs.cnt.value - 1) * enough.asBigInt)
      assert(ghost_q_next == regs.ghost_q * 2 + enough.asBigInt)

      {
        inputs.io_in_bits_0.value ==:| lemma_r_q_invariant(inputs, regs, ghost_q_next, ghost_r_next, enough.asBigInt) |:
        inputs.io_in_bits_1.value * ghost_q_next * Pow2(len - cnt_next.value) + ghost_r_next
      }.qed

      assert(shiftReg_next.value == Cat(Mux(enough, (hi - regs.bReg), hi)((len - 1), 0), Cat(lo, enough.asUInt)).value % Pow2(2 * len + 1))
      // prove shiftReg_next == 2 * shiftReg - in2 * e * Pow2(len + 1) + e
      {
        shiftReg_next.value ==:| lemma_shiftReg_update(inputs, regs, shiftReg_next, enough) |:
        2 * regs.shiftReg.value - inputs.io_in_bits_1.value * enough.asBigInt * Pow2(len + 1) + enough.asBigInt
      }.qed
      
      assert(shiftReg_next.value == 2 * regs.shiftReg.value - inputs.io_in_bits_1.value * enough.asBigInt * Pow2(len + 1) + enough.asBigInt)

      // prove r == shiftReg / Pow2(cnt + 1)
      {
        ghost_r_next ==:| lemma_r_shiftReg_invariant(inputs, regs, ghost_r_next, shiftReg_next, cnt_next) |:
        shiftReg_next.value / Pow2(cnt_next.value + 1)
      }.qed

      // prove shiftReg == q + r * Pow2(cnt + 1)
      {
        shiftReg_next.value ==:| lemma_shiftReg_r_q_invariant(inputs, regs, cnt_next, shiftReg_next, ghost_r_next, ghost_q_next, enough.asBigInt) |:
        ghost_q_next + ghost_r_next * Pow2(cnt_next.value + 1)
      }.qed

      if (when((regs.cnt === Lit(len - 1).U))) {
        state_next = state_next := s_finish
      }
    } else if (when((regs.state === s_finish))) {
      if (when(inputs.io_out_ready)) {
        state_next = state_next := s_idle
      }
    }

    val outputs = DividerOutputs(
        io_in_ready,
        io_out_valid,
        io_out_bits,
        io_out_bits_nexts_value
      )
    val regNexts = DividerRegs(
        state_next,
        shiftReg_next,
        aSignReg_next,
        qSignReg_next,
        bReg_next,
        aValx2Reg_next,
        cnt_next,
        ghost_r_next,
        ghost_q_next,
        cycle_next
      )

    (outputs, regNexts)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts) && postCond(inputs, regs, regNexts, outputs)
  }

  @library
  def outputsProp(inputs: DividerInputs, regs: DividerRegs, outputs: DividerOutputs): Boolean = {
    val in1 = inputs.io_in_bits_0.value
    val in2 = inputs.io_in_bits_1.value
    in1 == in2 * outputs.io_out_bits(len - 1, 0).value + outputs.io_out_bits(2 * len - 1, len).value
  }
  
  @library
  def dividerRun(inputs: DividerInputs, regInit: DividerRegs, outputs: DividerOutputs): (DividerOutputs, DividerRegs) = {
    require(inputsRequire(inputs) && regsRequire(regInit))
    require(preCond(inputs, regInit))
    decreases(2 * len - regInit.cycle)
    val (newOutputs, newRegs) = trans(inputs, regInit)
    // assert(postCond(inputs, regInit, newRegs, newOutputs))
    assert(regInit.cnt.value <= len)
    if (regInit.cnt.value <= len - 1) {
      dividerRun(inputs, newRegs, newOutputs)
    } else {
      /* 
       * else branch: 
       * last cycle is the final cycle of s_compute,
       * at the start of this cycle: regInit.cnt == len, regInit.state == s_finish
       * we get the expected output at this cycle
       */
      assert(regInit.cnt.value == len)  
      (newOutputs, newRegs)
    }
  // } ensuring { case (newOutputs, regNexts) =>
  //   outputsRequire(newOutputs) && regsRequire(regNexts) && outputsProp(inputs, regNexts, newOutputs)
  }

  @library
  def run(inputs: DividerInputs, randomInitValue: DividerRegs, outputs: DividerOutputs): (DividerOutputs, DividerRegs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = DividerRegs(
      Lit(0, 3).U,
      randomInitValue.shiftReg,
      randomInitValue.aSignReg,
      randomInitValue.qSignReg,
      randomInitValue.bReg,
      randomInitValue.aValx2Reg,
      Lit(0, bitLength(len)).U,
      randomInitValue.ghost_r,
      randomInitValue.ghost_q,
      randomInitValue.cycle
    )
    dividerRun(inputs, regInit, outputs)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts) && outputsProp(inputs, regNexts, outputs)
  }
}