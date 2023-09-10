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
    io_out_bits: UInt
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
    ghost_q: BigInt
)

case class Divider(len: BigInt = 64) {
  def inputsRequire(inputs: DividerInputs): Boolean = inputs match {
    case DividerInputs(io_in_valid, io_in_bits_0, io_in_bits_1, io_sign, io_out_ready) =>
      // io_in_bits.length == 2 &&
      // io_in_bits.forall(_.width == len)
      io_in_bits_0.width == len &&
      io_in_bits_1.width == len
  }
  def outputsRequire(outputs: DividerOutputs): Boolean = outputs match {
    case DividerOutputs(io_in_ready, io_out_valid, io_out_bits) =>
      io_out_bits.width == (len * 2)
  }
  def regsRequire(regs: DividerRegs): Boolean = regs match {
    case DividerRegs(state, shiftReg, aSignReg, qSignReg, bReg, aValx2Reg, cnt, ghost_r, ghost_q) =>
      state.width == 3 &&
      shiftReg.width == (1 + (len * 2)) &&
      // Unknown size bReg &&
      // Unknown size aValx2Reg &&
      cnt.width == bitLength(len)
  }

  def preCond(inputs: DividerInputs, regs: DividerRegs): Boolean = {
    // require(inputs.io_in_bits.length == 2 && inputs.io_in_bits.forall(_.width == len))
    // require(inputs.io_in_bits_0.width == len && inputs.io_in_bits_1.width == len)
  
    val in1 = inputs.io_in_bits_0.value
    val in2 = inputs.io_in_bits_1.value
    len > 0 &&
    inputs.io_in_valid.value == true &&
    0 <= in1 && in1 < Pow2(len) &&
    0 <= in2 && in2 < Pow2(len) && 
    regs.qSignReg.value == false &&
    regs.aSignReg.value == false &&
    regs.state.value == BigInt(3) && regs.state.width == BigInt(3) &&
    regs.bReg.value == in2 &&
    regs.shiftReg.value >= BigInt(0) &&
    0 <= regs.cnt.value && regs.cnt.value < len && 
    0 <= regs.ghost_r && 0 <= regs.ghost_q &&
    in1 == in2 * regs.ghost_q * Pow2(len - regs.cnt.value) + regs.ghost_r && 
    regs.ghost_r == regs.shiftReg.value / Pow2(regs.cnt.value + 1) &&
    regs.shiftReg.value == regs.ghost_q + regs.ghost_r * Pow2(regs.cnt.value + 1)    
  }

  def postCond(inputs: DividerInputs, regs: DividerRegs, outputs: DividerOutputs): Boolean = {
    // require(inputs.io_in_bits.length == 2 && inputs.io_in_bits.forall(_.width == len))
    // require(inputs.io_in_bits_0.width == len && inputs.io_in_bits_1.width == len)
    val in1 = inputs.io_in_bits_0.value
    val in2 = inputs.io_in_bits_1.value
    len > 0 &&
    inputs.io_in_valid.value == true &&
    0 <= in1 && in1 < Pow2(len) &&
    0 <= in2 && in2 < Pow2(len) && 
    regs.bReg.value == in2 &&
    regs.shiftReg.value >= BigInt(0) &&
    0 <= regs.cnt.value && regs.cnt.value <= len &&
    in1 == in2 * regs.ghost_q * Pow2(len - regs.cnt.value) + regs.ghost_r &&
    regs.ghost_r == regs.shiftReg.value / Pow2(regs.cnt.value + 1) &&
    regs.shiftReg.value == regs.ghost_q + regs.ghost_r * Pow2(regs.cnt.value + 1) &&
    // hold iff cnt == len, need proof
    outputs.io_out_bits(2 * len - 1, len).value == regs.ghost_r &&
    outputs.io_out_bits(len - 1, 0).value == regs.ghost_q
  }

  // lemma
  @opaque @library
  def lemma_var_value_width(value: BigInt, width: BigInt): Unit = {
  }.ensuring(_ => 0 <= value && value < Pow2(width) && 0 < width)

  @opaque @library
  def lemma_r_q_invariant(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs, e: BigInt): Unit = {
    // val in1 = a.value
    // val in2 = b.value
    // require(len >= BigInt(1))
    // require(in1 < Pow2(len) && in1 >= BigInt(0))
    // require(in2 < Pow2(len) && in2 > BigInt(0))
    require(regs.cnt.value >= BigInt(0) && regs.cnt.value <= len - 1)
    require(0 <= e && e <= 1)
    require(regs.ghost_r >= 0)
    require(inputs.io_in_bits_0.value 
      == inputs.io_in_bits_1.value * regs.ghost_q * Pow2(len - regs.cnt.value) + regs.ghost_r)
    require(regNexts.ghost_q == 2 * regs.ghost_q + e)
    require(regNexts.ghost_r == regs.ghost_r - inputs.io_in_bits_1.value * Pow2(len - regs.cnt.value - 1) * e)
    require(regNexts.cnt.value == regs.cnt.value + 1)
    val in1 = inputs.io_in_bits_0.value
    val in2 = inputs.io_in_bits_1.value
    val r = regs.ghost_r
    val q = regs.ghost_q
    val cnt = regs.cnt.value
    val r_next = regNexts.ghost_r
    val q_next = regNexts.ghost_q
    val cnt_next = regNexts.cnt.value
    {
      in2 * q_next * Pow2(len - cnt_next) + r_next                                        ==:| trivial |:
      in2 * (2 * q + e) * Pow2(len - cnt - 1) + (r - in2 * Pow2(len - cnt - 1) * e)       ==:| trivial |:
      in2 * (2 * q + e) * Pow2(len - cnt - 1) + r - in2 * Pow2(len - cnt - 1) * e         ==:| trivial |:
      in2 * q * Pow2(len - cnt) + in2 * e * Pow2(len - cnt - 1) + r - in2 * Pow2(len - cnt - 1) * e ==:| trivial |:
      in2 * q * Pow2(len - cnt) + r                                                       ==:| trivial |:
      in1
    }.qed

  }.ensuring(_ => inputs.io_in_bits_1.value * regNexts.ghost_q * Pow2(len - regNexts.cnt.value) + regNexts.ghost_r 
      == inputs.io_in_bits_0.value)

  @opaque @library
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
  }.ensuring(_ => shiftReg / Pow2(cnt + 1) >= shiftReg / Pow2(len) * Pow2(len - cnt - 1))

  // check again
  @opaque @library 
  def lemma_shiftReg_update(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs, enough: Bool): Unit = {
    val hi = regs.shiftReg((len * 2), len)
    val lo = regs.shiftReg((len - 1), 0)
    require(regNexts.shiftReg.value == 
      Cat(Mux(enough, hi - regs.bReg, hi)((len - 1), 0), Cat(lo, enough.asUInt)).value % Pow2(2 * len + 1))
    require(enough.value == (hi.value >= regs.bReg.value))
    require(inputs.io_in_bits_1.value == regs.bReg.value)
    assert(Mux(enough, (hi - regs.bReg), hi).value == hi.value - regs.bReg.value * enough.asBigInt)
    val tmp_hi = Mux(enough, (hi - regs.bReg), hi)((len - 1), 0)
    val tmp_lo = Cat(lo, enough.asUInt)
    {
      regNexts.shiftReg.value                       ==:| trivial |:
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
  }.ensuring(_ => regNexts.shiftReg.value == 2 * regs.shiftReg.value - inputs.io_in_bits_1.value * enough.asBigInt * Pow2(len + 1) + enough.asBigInt)
    

  @opaque @library
  def lemma_r_shiftReg_invariant(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs, e: BigInt): Unit = {
    require(len >= BigInt(1))
    val a = inputs.io_in_bits_0.value
    val b = inputs.io_in_bits_1.value
    val cnt = regs.cnt.value
    val shiftReg = regs.shiftReg.value
    val R = regs.ghost_r
    val R1 = regNexts.ghost_r
    val shiftReg1 = regNexts.shiftReg.value
    val cnt1 = regNexts.cnt.value

    require(a < Pow2(len) && a >= BigInt(0))
    require(b < Pow2(len) && b >= BigInt(0))

    require(cnt >= BigInt(0) && cnt <= len - 1)
    require(0 <= e && e <= 1)
    require(shiftReg >= 0)
    require(shiftReg / Pow2(len) >= b * e) // e == hi >= b == shiftReg / Pow2(len) >= b
    require(R >= 0)
    require(R == shiftReg / Pow2(cnt + 1))
    require(R1 == R - b * Pow2(len - cnt - 1) * e)
    require(shiftReg1 == 2 * shiftReg - b * e * Pow2(len + 1) + e)
    require(cnt1 == cnt + 1)

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
  }.ensuring(_ => regNexts.ghost_r == regNexts.shiftReg.value / Pow2(regNexts.cnt.value + 1))
  
  @opaque @library
  def lemma_shiftReg_r_q_invariant(inputs: DividerInputs, regs: DividerRegs, regNexts: DividerRegs, e: BigInt): Unit = {
    val shiftReg1 = regNexts.shiftReg.value
    val shiftReg = regs.shiftReg.value
    val b = inputs.io_in_bits_1.value
    val R = regs.ghost_r
    val R1 = regNexts.ghost_r
    val Q = regs.ghost_q
    val Q1 = regNexts.ghost_q
    val cnt = regs.cnt.value
    val cnt1 = regNexts.cnt.value
    // require(len >= BigInt(1))
    // // require(a < Pow2(len) && a >= BigInt(0))
    // require(b < Pow2(len) && b > BigInt(0))

    require(cnt >= BigInt(0) && cnt <= len - 1)
    // require(0 <= e && e <= 1)
    // require(shiftReg >= 0)
    // require(R >= 0)
    require(R1 == R - b * e * Pow2(len - cnt - 1))
    require(shiftReg == Q + R * Pow2(cnt + 1))

    {
      regNexts.shiftReg.value                                   ==:| trivial |:
      shiftReg1                                                 ==:| trivial |:
      2 * shiftReg - b * e * Pow2(len + 1) + e                  ==:| trivial |:
      2 * (R * Pow2(cnt + 1) + Q) - b * e * Pow2(len + 1) + e   ==:| trivial |:
      2 * Q + e + R * Pow2(cnt + 2) - b * e * Pow2(len + 1)     ==:| Pow2.Pow2Mul(len + 1, cnt + 2, len - cnt - 1) |:
      2 * Q + e + Pow2(cnt + 2) * (R - b * e * Pow2(len - cnt - 1)) ==:| trivial |:
      R1 * Pow2(cnt1 + 1) + Q1                                      ==:| trivial |:
      regNexts.ghost_r * Pow2(regNexts.cnt.value + 1) + regNexts.ghost_q
    }.qed
  }.ensuring(_ => regNexts.shiftReg.value == regNexts.ghost_r * Pow2(regNexts.cnt.value + 1) + regNexts.ghost_q)

  // check again
  @opaque @library
  def lemma_out_bits_r(outputs: DividerOutputs, regs: DividerRegs): Unit = {
    require(regs.shiftReg.value / Pow2(len + 1) == regs.ghost_r)
    require(regs.shiftReg((len * 2), len + 1).value == outputs.io_out_bits((len * 2 - 1), len).value)
    {
      outputs.io_out_bits(2 * len - 1, len).value     ==:| trivial |:
      regs.shiftReg((len * 2), len + 1).value ==:| trivial |:
      regs.shiftReg.value / Pow2(len + 1)     ==:| trivial |:
      regs.ghost_r                  
    }.qed
  }.ensuring(_ => outputs.io_out_bits(2 * len - 1, len).value == regs.ghost_r)

  // inner function
  @library
  def abs(a: UInt, sign: Bool): (Bool, UInt) = {
    // require(a.width == len)
    val s = (a((len - 1)) && sign)
    (s, Mux(s, -a, a))
  }

  def trans(inputs: DividerInputs, regs: DividerRegs): (DividerOutputs, DividerRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))
    require(preCond(inputs, regs))

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

    // ghost vars
    var ghost_r_next = regs.ghost_r
    var ghost_q_next = regs.ghost_q

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

    // if b.length >= a.length, canSkipShift >= len - 1
    val canSkipShift = ((Lit(len).U + Log2(regs.bReg)) - Log2(regs.aValx2Reg))
    val enough = (hi.asUInt >= regs.bReg.asUInt)
    val r = hi(len, 1)
    val resQ = Mux(regs.qSignReg, -lo, lo)
    val resR = Mux(regs.aSignReg, -r, r)
    io_out_bits = io_out_bits := Cat(resR, resQ)
    io_out_valid = io_out_valid := (regs.state === s_finish)
    io_in_ready = io_in_ready := (regs.state === s_idle)
    val newReq = ((regs.state === s_idle) && (io_in_ready && inputs.io_in_valid))
    assert(when(newReq) == false)
    assert(when(regs.state === s_compute))
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
    } else if (when((regs.state === s_shift))) {
      shiftReg_next = shiftReg_next := (regs.aValx2Reg << regs.cnt)
      state_next = state_next := s_compute
    } else if (when((regs.state === s_compute))) {
      // shiftReg_next = shiftReg_next := Cat(List(Mux(enough, (hi - regs.bReg), hi)((len - 1), 0), lo, enough))
      shiftReg_next = shiftReg_next := Cat(Mux(enough, (hi - regs.bReg), hi)((len - 1), 0), Cat(lo, enough.asUInt))
      cnt_next = cnt_next := (regs.cnt + Lit(1).U)   

      // assist check
      assert(shiftReg_next.width == (len * 2 + 1))
      assert(shiftReg_next.value == Cat(Mux(enough, (hi - regs.bReg), hi)((len - 1), 0), Cat(lo, enough.asUInt)).value % Pow2(2 * len + 1))

      // ghost vars update
      ghost_r_next = regs.ghost_r - regs.bReg.value * Pow2(len - regs.cnt.value - 1) * enough.asBigInt
      ghost_q_next = regs.ghost_q * 2 + enough.asBigInt

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
        io_out_bits
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
        ghost_q_next
      )
    
    if (regs.state.value == s_compute.value) {
      // prove in1 == in2 * q * Pow2(len - cnt) + r   
      assert(regNexts.cnt.value == regs.cnt.value + 1)
      assert(regNexts.ghost_r == regs.ghost_r - inputs.io_in_bits_1.value * Pow2(len - regs.cnt.value - 1) * enough.asBigInt)
      assert(regNexts.ghost_q == regs.ghost_q * 2 + enough.asBigInt)

      {
        inputs.io_in_bits_0.value ==:| lemma_r_q_invariant(inputs, regs, regNexts, enough.asBigInt) |:
        inputs.io_in_bits_1.value * regNexts.ghost_q * Pow2(len - regNexts.cnt.value) + regNexts.ghost_r
      }.qed

      // prove shiftReg_next == 2 * shiftReg - in2 * e * Pow2(len + 1) + e
      {
        regNexts.shiftReg.value ==:| lemma_shiftReg_update(inputs, regs, regNexts, enough) |:
        2 * regs.shiftReg.value - inputs.io_in_bits_1.value * enough.asBigInt * Pow2(len + 1) + enough.asBigInt
      }.qed
      
      assert(regNexts.shiftReg.value == 2 * regs.shiftReg.value - inputs.io_in_bits_1.value * enough.asBigInt * Pow2(len + 1) + enough.asBigInt)

      // prove r == shiftReg / Pow2(cnt + 1)
      {
        regNexts.ghost_r ==:| lemma_r_shiftReg_invariant(inputs, regs, regNexts, enough.asBigInt) |:
        regNexts.shiftReg.value / Pow2(regNexts.cnt.value + 1)
      }.qed

      // prove shiftReg == q + r * Pow2(cnt + 1)
      {
        regNexts.shiftReg.value ==:| lemma_shiftReg_r_q_invariant(inputs, regs, regNexts, enough.asBigInt) |:
        regNexts.ghost_q + regNexts.ghost_r * Pow2(regNexts.cnt.value + 1)
      }.qed
    }

    (outputs, regNexts)
  } ensuring { case (outputs, regNexts) => 
    outputsRequire(outputs) && regsRequire(regNexts) && postCond(inputs, regNexts, outputs)
  }

  def outputsProp(inputs: DividerInputs, regs: DividerRegs, outputs: DividerOutputs): Boolean = {
    val in1 = inputs.io_in_bits_0.value
    val in2 = inputs.io_in_bits_1.value
    len > 0 &&
    in1 == in2 * outputs.io_out_bits(len - 1, 0).value + outputs.io_out_bits(2 * len - 1, len).value
  }
  
  @ignore
  def dividerRun(inputs: DividerInputs, regInit: DividerRegs): (DividerOutputs, DividerRegs) = {
    require(inputsRequire(inputs) && regsRequire(regInit))
    require(preCond(inputs, regInit))
    decreases(len - regInit.cnt.value)
    val (newOutputs, newRegs) = trans(inputs, regInit)
    assert(newRegs.cnt.value <= len)
    if (newRegs.cnt.value <= len - 1) {
      dividerRun(inputs, newRegs)
    } else {
      assert(newRegs.cnt.value == len)
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts) && outputsProp(inputs, regNexts, outputs)
  }

  @ignore
  def run(inputs: DividerInputs, randomInitValue: DividerRegs): (DividerOutputs, DividerRegs) = {
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
      randomInitValue.ghost_q
    )
    dividerRun(inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}