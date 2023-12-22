package exampleVerify.rocketchip

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._
import chisel3.util.log2Floor
import divider.NutshellFixedClockTest0

case class DivInputs(
    io_req_valid: Bool,
    io_req_bits_dw: UInt,
    io_req_bits_in1: UInt,
    io_req_bits_in2: UInt,
    io_req_bits_tag: UInt,
    io_req_bits_fn: UInt,
    io_resp_ready: Bool
)
case class DivOutputs(
    io_req_ready: Bool,
    io_resp_valid: Bool,
    io_resp_bits_data: UInt,
    io_resp_bits_tag: UInt
)
case class DivRegs(
    state: UInt,
    req_dw: UInt,
    req_in1: UInt,
    req_in2: UInt,
    req_tag: UInt,
    req_fn: UInt,
    count: UInt,
    neg_out: Bool,
    isHi: Bool,
    resHi: Bool,
    divisor: UInt,
    remainder: UInt,
    ghost_Q: UInt
)

case class Div(
    mulUnroll: BigInt = 1,
    divUnroll: BigInt = 1,
    mulEarlyOut: Boolean = false,
    divEarlyOut: Boolean = false,
    divEarlyOutGranularity: BigInt = 1,
    w: BigInt,
    nXpr: BigInt = 32
) {
  require(divEarlyOut == false && nXpr > 0 && w > 0 && mulUnroll == 0 && divUnroll > 0 && divUnroll <= w)
  @library
  def inputsRequire(inputs: DivInputs): Boolean = inputs match {
    case DivInputs(io_req_valid, io_req_bits_dw, io_req_bits_in1, io_req_bits_in2, io_req_bits_tag, io_req_bits_fn, io_resp_ready) =>
      io_req_bits_dw.width == 1 &&
      io_req_bits_in1.width == w &&
      io_req_bits_in2.width == w &&
      io_req_bits_tag.width == log2Up(nXpr) &&
      io_req_bits_fn.width == 4
  }
  @library
  def outputsRequire(outputs: DivOutputs): Boolean = outputs match {
    case DivOutputs(io_req_ready, io_resp_valid, io_resp_bits_data, io_resp_bits_tag) =>
      io_resp_bits_data.width == w &&
      io_resp_bits_tag.width == log2Up(nXpr)
  }
  @library
  def regsRequire(regs: DivRegs): Boolean = regs match {
    case DivRegs(state, req_dw, req_in1, req_in2, req_tag, req_fn, count, neg_out, isHi, resHi, divisor, remainder, ghost_Q) =>
      state.width == 3 &&
      req_dw.width == 1 &&
      req_in1.width == w &&
      req_in2.width == w &&
      req_tag.width == log2Up(nXpr) &&
      req_fn.width == 4 &&
      count.width == log2Ceil(((w / divUnroll) + 1)) &&
      divisor.width == (w + 1) &&
      remainder.width == ((2 * (if ((mulUnroll == 0)) w else ((((w + mulUnroll) - 1) / mulUnroll) * mulUnroll))) + 2)
  }
  @library
  def preCond(inputs: DivInputs, regs: DivRegs): Boolean = {
    w <= 32 &&
    divUnroll == 1 &&
    regs.state == Lit(3, 3).U && // assume state == s_div
    regs.resHi == Lit(false).B &&
    regs.isHi == Lit(false).B &&
    inputs.io_req_bits_fn != Lit(4).U && // assume lhsSigned == rhsSigned == false
    (regs.count.value >= 0 && regs.count.value <= w / divUnroll) &&
    // rem == Pow2(cnt) * in1 - Pow2(w + 1) * in2 * gq + gq
    (regs.remainder.value == Pow2(regs.count.value * inputs.io_req_bits_in1.value) 
      - Pow2(w + 1) * inputs.io_req_bits_in2.value * regs.ghost_Q.value + regs.ghost_Q.value) &&
    (regs.divisor.value == inputs.io_req_bits_in2.value) &&
    // (regs.count.value == BigInt(0) && regs.remainder.value == inputs.in1.value
    //   || regs.count.value >= BigInt(1) && regs.remainder.value >= BigInt(0)) &&
    (regs.count.value >= 0 && regs.remainder.value >= 0)
    // (regs.ghost_R.value == regs.remainder.value / Pow2(regs.count.value)) &&
    // (regs.ghost_Q.value == regs.remainder.value - regs.ghost_R.value * Pow2(regs.count.value)) &&
    // (regs.ghost_R.value + inputs.io_req_bits_in2.value * regs.ghost_Q.value * Pow2(w - regs.count.value + 1) == 2 * inputs.io_req_bits_in1.value)
  }
  @library
  def postCond(inputs: DivInputs, outputs: DivOutputs, regs: DivRegs): Boolean = {
    (regs.count.value >= 0 && regs.count.value <= w / divUnroll) &&
    (regs.divisor.value == inputs.io_req_bits_in2.value) &&
    // (regs.count.value == BigInt(0) && regs.remainder.value == inputs.in1.value
    //   || regs.count.value >= BigInt(1) && regs.remainder.value >= BigInt(0)) &&
    regs.remainder.value >= 0 // &&
    // (regs.ghost_R.value == regs.remainder.value / Pow2(regs.count.value)) &&
    // (regs.ghost_Q.value == regs.remainder.value - regs.ghost_R.value * Pow2(regs.count.value)) &&
    // (regs.ghost_R.value + inputs.io_req_bits_in2.value * regs.ghost_Q.value * Pow2(w - regs.count.value + 1) == 2 * inputs.io_req_bits_in1.value)
 
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

  // inv: remainder.value = Pow2(count) * inputs.io_req_bits_in1.value 
  //                          - Pow2(w + 1) * inputs.io_req_bits_in2.value * ghost_Q.value + ghost_Q.value    
  @opaque @library
  def lemma_rem_gq_update(regs: DivRegs, inputs: DivInputs, i: BigInt, rem_next: BigInt, cnt_next: BigInt, ghost_Q_next: UInt, negLess: BigInt): Unit = {
    val rem = regs.remainder.value
    val cnt = regs.count.value
    val gq = regs.ghost_Q.value
    val in1 = inputs.io_req_bits_in1.value
    val in2 = inputs.io_req_bits_in2.value
    val gq_next = ghost_Q_next.value
    require(rem == Pow2(cnt * i) * in1 - Pow2(w + 1) * in2 * gq + gq)
    require(gq_next == gq * 2 + negLess)
    require(rem_next == rem * 2 - in2 * negLess * Pow2(w + 1) + negLess)
    require(cnt_next == regs.count.value * i + 1)
    {
      rem_next ==:| trivial |:
      rem * 2 - in2 * negLess * Pow2(w + 1) + negLess ==:| trivial |:
      Pow2(cnt * i + 1) * in1 - Pow2(w + 2) * in2 * gq + gq * 2 - in2 * negLess * Pow2(w + 1) + negLess  ==:| trivial |:
      Pow2(cnt * i + 1) * in1 - Pow2(w + 1) * in2 * (gq * 2 + negLess) + gq * 2 + negLess                ==:| trivial |:
      Pow2(cnt * i + 1) * in1 - Pow2(w + 1) * in2 * gq_next + gq_next                                    
    }.qed
  }.ensuring(_ => rem_next == Pow2(cnt_next) * inputs.io_req_bits_in1.value - Pow2(w + 1) * inputs.io_req_bits_in2.value * ghost_Q_next.value + ghost_Q_next.value)

  @library
  def remainder_update(remainder_next: UInt, remainder: UInt, divisor: UInt, negLess: BigInt, w: BigInt): Unit = {
    val h = remainder.value / Pow2(w)
    val l = remainder.value - h * Pow2(w)
    // val negLess = 1 - less
    {
      remainder_next.value ==:| trivial |:
      (remainder.value / Pow2(w) - divisor.value * negLess) * Pow2(w + 1) + remainder.value % Pow2(w) * 2 + negLess ==:| trivial |:
      (h - divisor.value * negLess) * Pow2(w + 1) + l * 2 + negLess ==:| trivial |:
      (h - divisor.value * negLess) * Pow2(w) * 2 + l * 2 + negLess ==:| trivial |:
      (h * Pow2(w) - divisor.value * negLess * Pow2(w) + l) * 2 + negLess ==:| trivial |:
      remainder.value * 2 - divisor.value * negLess * Pow2(w) * 2 + negLess 
    }.qed
  } ensuring(_ => remainder_next.value == remainder.value * 2 - divisor.value * negLess * Pow2(w + 1) + negLess)

  @library
  def lemma_eout(regs: DivRegs, inputs: DivInputs, rem_next: UInt, cnt_next: UInt, gq_next: UInt, eOutPos: UInt, divUnroll: BigInt): Unit = {
  val rem = regs.remainder
    require(rem.value == inputs.io_req_bits_in1.value)
    require(rem.value < Pow2(w))
    require(gq_next.value == BigInt(0))
    require(rem_next.value == rem.value * Pow2(eOutPos.value))
    require(cnt_next.value == eOutPos.value / Pow2(log2Floor(divUnroll)))
    {
      eOutPos.value ==:| trivial |:
      eOutPos.value / Pow2(log2Floor(divUnroll)) * Pow2(log2Floor(divUnroll)) ==:| trivial |:
      cnt_next.value * Pow2(log2Floor(divUnroll)) ==:| Pow2.Pow2Log(divUnroll) |:
      cnt_next.value * divUnroll
    }.qed
    {
      rem_next.value ==:| trivial |:
      rem.value * Pow2(eOutPos.value) ==:| trivial |:
      rem.value * Pow2(cnt_next.value) * divUnroll 
    }.qed
  }.ensuring(rem_next.value == Pow2(cnt_next.value * divUnroll) * inputs.io_req_bits_in1.value 
      - Pow2(w + 1) * regs.divisor.value * ghost_Q_next.value + ghost_Q_next.value )

  // inner function
  // w <= 32 return false,  
  @library
  def halfWidth(reqDw: UInt): Bool = {
    (Lit((w > 32)).B && (reqDw === Lit(false).B))
  } ensuring(res => res.value == false)
  @library
  def sext(x: UInt, halfW: Bool, signed: Bool): (UInt, Bool) = {
    val sign = (signed && Mux(halfW, x(((w / 2) - 1)), x((w - 1))))
    val hi = Mux(halfW, Fill((w / 2), sign), x((w - 1), (w / 2)))
    (Cat(hi, x(((w / 2) - 1), 0)), sign)
  }

  @library
  def scanLeft(l: List[BigInt], rem: UInt, i: BigInt, inputs: DivInputs, regs: DivRegs, subtractor: UInt, ghost_Q: UInt): (List[UInt], List[UInt]) = { 
    require(l.forall(_ >= 0) && l.forall(_ < divUnroll))
    require(i >= 0)
    // require(
    //   l match {
    //     case Nil() => true
    //     case Cons(h, t) => h == i && {
    //       t match {
    //         case Nil() => true
    //         case Cons(th, tt) => th == i + 1
    //       }
    //     }
    //   })
    // require(rem.value == regs.remainder.value / Pow2(i))
    // require(subtractor.value == (regs.remainder((2 * w), w) - regs.divisor).value)

    @library               
    def f_scanLeft(rem: UInt, i: BigInt, subtractor: UInt, regs: DivRegs, inputs: DivInputs, ghost_Q: UInt): (UInt, UInt) = {
      val divisor = regs.divisor
      val subtractor = regs.remainder(2 * w, w) - divisor
      val cnt = regs.count.value
      val in1 = inputs.io_req_bits_in1.value
      val in2 = inputs.io_req_bits_in2.value
      require(i >= 0 && i < divUnroll)
      require(rem.value == Pow2(cnt * i) * in1 - Pow2(w + 1) * divisor.value * ghost_Q.value + ghost_Q.value)
      require(subtractor.value == regs.remainder.value / Pow2(w) - divisor.value)
      require(!(i == 0) || rem.value == regs.remainder.value)
      
      // function body
      val difference = if (i == 0) subtractor else rem(2 * w, w) - divisor(w - 1, 0)
      val less       = difference(w)
      val rem_next = Cat(Mux(less, rem(2 * w - 1, w), difference(w - 1, 0)), Cat(rem(w - 1, 0), !less))
      
      // proof
      val nl         = (!less).asBigInt

      // ghost variables
      val gq_next = UInt(ghost_Q.value * 2 + nl, ghost_Q.width)

      // rem update: rem_next == rem * 2 - in2 * negLess * Pow2(w + 1) + negLess
      assert(difference.value == rem.value / Pow2(w) - divisor.value)
      @library
      def lemma_rem_update(rem_next: UInt, rem: UInt, divisor: UInt, nl: BigInt): Unit = {
        require(rem.value < Pow2(2 * w))
        require(difference.value < Pow2(w))
        // require(rem_next.value == Mux(less, rem(2 * w - 1, w), difference(w - 1, 0)) * Pow2(w + 1) + rem(w - 1, 0) * 2 + nl)
        {
          rem_next.value ==:| trivial |:
          Mux(less, rem(2 * w - 1, w), difference(w - 1, 0)).value * Pow2(w + 1) + rem(w - 1, 0).value * 2 + nl   ==:| trivial |:
          (if(less.value) rem.value / Pow2(w) else difference.value) * Pow2(w + 1) + rem.value % Pow2(w) * 2 + nl ==:| trivial |:
          (rem.value / Pow2(w) - divisor.value * nl) * Pow2(w + 1) + rem.value % Pow2(w) * 2 + nl  ==:| remainder_update(rem_next, rem, divisor, nl, w) |:
          rem.value * 2 - divisor.value * nl * Pow2(w + 1) + nl
        }.qed
      }.ensuring(_ => rem_next.value == rem.value * 2 - divisor.value * nl * Pow2(w + 1) + nl)

      {
        rem_next.value ==:| lemma_rem_update(rem_next, rem, divisor, nl) |:
        rem.value * 2 - divisor.value * nl * Pow2(w + 1) + nl
      }.qed

      // res == rem_next 
      // inv: rem = Pow2(cnt * i) * in1 - Pow2(w + 1) * in2 * ghost_Q + ghost_Q
      val cnt_next = regs.count.value * i + 1
      {
        rem_next.value ==:| lemma_rem_gq_update(regs, inputs, i, rem_next.value, cnt_next, gq_next, nl) |:
        Pow2(cnt * i + 1) * in1 - Pow2(w + 1) * divisor.value * gq_next.value + gq_next.value
      }.qed
      
      (rem_next, gq_next)
    } ensuring(res => res._1.value == Pow2(regs.count.value * i + 1) * inputs.io_req_bits_in1.value 
        - Pow2(w + 1) * regs.divisor.value * res._2.value + res._2.value)
    
    val rem_list = l match {
      case Nil() => rem :: Nil()
      case Cons(h, tail) => {
        assert(h >= 0 && h < divUnroll)
        rem :: scanLeft(tail, f_scanLeft(rem, h, subtractor, regs, inputs, ghost_Q)._1, i + 1, inputs, regs, subtractor, ghost_Q)._1
      }
    }
    val gq_list = l match {
      case Nil() => ghost_Q :: Nil()
      case Cons(h, tail) => {
        assert(h >= 0 && h < divUnroll)
        ghost_Q :: scanLeft(tail, f_scanLeft(rem, h, subtractor, regs, inputs, ghost_Q)._2, i + 1, inputs, regs, subtractor, ghost_Q)._2
      }
    }
    (rem_list, gq_list)
  } ensuring {res => 
      res._1 != Nil[UInt]() && res._1.tail != Nil[UInt]() && res._1.tail.last != Nil() && res._1.tail.last.value >= 0
      res._2 != Nil[UInt]() && res._2.tail != Nil[UInt]() && res._2.tail.last != Nil() && res._2.tail.last.value >= 0} 

  @library
  def f_until(start: BigInt, until: BigInt): List[BigInt] = {
    require(start <= until)
    require(start >= 0 && until <= divUnroll)
    decreases(until - start)
    if(until <= start) Nil[BigInt]() else Cons(start, f_until(start + 1, until))
  } ensuring{(res: List[BigInt]) => res.size == until - start && res.forall(_ >= 0) && res.forall(_ < divUnroll) && res.head == 0}

  def trans(inputs: DivInputs, regs: DivRegs): (DivOutputs, DivRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))
    require(preCond(inputs, regs))

    // output
    var io_req_ready = Bool.empty()
    var io_resp_valid = Bool.empty()
    var io_resp_bits_data = UInt.empty(w)
    var io_resp_bits_tag = UInt.empty(log2Up(nXpr))
    // reg next
    var state_next = regs.state
    var req_dw_next = regs.req_dw
    var req_in1_next = regs.req_in1
    var req_in2_next = regs.req_in2
    var req_tag_next = regs.req_tag
    var req_fn_next = regs.req_fn
    var count_next = regs.count
    var neg_out_next = regs.neg_out
    var isHi_next = regs.isHi
    var resHi_next = regs.resHi
    var divisor_next = regs.divisor
    var remainder_next = regs.remainder

    // var ghost_R_next = regs.ghost_R
    var ghost_Q_next = regs.ghost_Q

    // body
    def minDivLatency: BigInt = if (divEarlyOut) 3 else (1 + (w / divUnroll))
    def minLatency: BigInt = minDivLatency
    val mulw = if ((mulUnroll == 0)) w else ((((w + mulUnroll) - 1) / mulUnroll) * mulUnroll)
    val fastMulW = if ((mulUnroll == 0)) false else (((w / 2) > mulUnroll) && ((w % (2 * mulUnroll)) == 0)) // false if div
    val (s_ready, s_neg_inputs, s_mul, s_div, s_dummy, s_neg_output, s_done_mul, s_done_div) = (Lit(0, 3).U, Lit(1, 3).U, Lit(2, 3).U, Lit(3, 3).U, Lit(4, 3).U, Lit(5, 3).U, Lit(6, 3).U, Lit(7, 3).U)
    var cmdMul = Lit(false).B
    var cmdHi = Lit(false).B
    var lhsSigned = Lit(false).B
    var rhsSigned = Lit(false).B
    if ((divUnroll != 0)) if ((inputs.io_req_bits_fn === Lit(4).U).value) {
      cmdMul = cmdMul := Lit(false).B
      cmdHi = cmdHi := Lit(false).B
      lhsSigned = lhsSigned := Lit(true).B
      rhsSigned = rhsSigned := Lit(true).B
    }
    
    val (lhs_in, lhs_sign) = sext(inputs.io_req_bits_in1, halfWidth(inputs.io_req_bits_dw), lhsSigned)
    val (rhs_in, rhs_sign) = sext(inputs.io_req_bits_in2, halfWidth(inputs.io_req_bits_dw), rhsSigned)
    val subtractor = (regs.remainder((2 * w), w) - regs.divisor)
    val result = Mux(regs.resHi, regs.remainder((2 * w), (w + 1)), regs.remainder((w - 1), 0)) // if w <= 32, resHi == false, result = regs.remainder(w - 1, 0)
    val negated_remainder = -result
    if ((divUnroll != 0)) if (when((regs.state === s_neg_inputs))) {
      if (when(regs.remainder((w - 1)))) remainder_next = remainder_next := negated_remainder
      
      if (when(regs.divisor((w - 1)))) divisor_next = divisor_next := subtractor
      state_next = state_next := s_div
    }
    if ((divUnroll != 0)) if (when((regs.state === s_neg_output))) {
      remainder_next = remainder_next := negated_remainder
      state_next = state_next := s_done_div
      resHi_next = resHi_next := Lit(false).B
    }
    val divby0 = ((regs.count === Lit(0).U) && !subtractor(w))
    val align = <<(1, log2Floor(max(divUnroll, divEarlyOutGranularity)))
    val alignMask = ~Lit((align - 1), log2Ceil(w)).U
    val divisorMSB = (Log2(regs.divisor((w - 1), 0), w) & alignMask)
    val dividendMSB = (Log2(regs.remainder((w - 1), 0), w) | ~(alignMask))
    val eOutPos = ~(dividendMSB - divisorMSB)
    val eOut = (((regs.count === Lit(0).U) && !divby0) && (eOutPos >= Lit(align).U))
    // var unrolls = List[UInt]()
    if ((divUnroll != 0)) if (when((regs.state === s_div))) {
      // unrolls = (0 until divUnroll).scanLeft(regs.remainder)({ case (rem, i) => {
      //     val difference = if ((i == 0)) subtractor else (rem((2 * w), w) - regs.divisor((w - 1), 0))
      //     val less = difference(w)
      //     Cat((Mux(less, rem(((2 * w) - 1), w), difference((w - 1), 0)), Cat(rem((w - 1), 0), !less)))
      // }}).tail      
      val (unrolls, gq_next_list) = 
        ((scanLeft(f_until(BigInt(0), divUnroll), regs.remainder, BigInt(0), inputs, regs, subtractor, regs.ghost_Q))._1.tail,
        (scanLeft(f_until(BigInt(0), divUnroll), regs.remainder, BigInt(0), inputs, regs, subtractor, regs.ghost_Q))._2.tail)

      // rem = Pow2(cnt * divUnroll) * in1 - Pow2(w + 1) * divisor * ghost_Q + ghost_Q
      remainder_next = remainder_next := unrolls.last
      ghost_Q_next = ghost_Q_next := gq_next_list.last

      if (when((regs.count === Lit((w / divUnroll)).U))) {
        state_next = state_next := Mux(regs.neg_out, s_neg_output, s_done_div)
        resHi_next = resHi_next := regs.isHi
        if (((w % divUnroll) < (divUnroll - 1))) remainder_next = remainder_next := unrolls((w % divUnroll))
      }
      count_next = count_next := (regs.count + Lit(1).U)
      if (divEarlyOut) if (when(eOut)) {
        remainder_next = remainder_next := (regs.remainder((w - 1), 0) << eOutPos)
        count_next = count_next := (eOutPos >> log2Floor(divUnroll))
        
        // ghost_Q == 0 when count == 0
        ghost_Q_next = regs.ghost_Q
        // proof inv holds
        {
          remainder_next.value ==:| lemma_eout(regs, inputs, remainder_next, count_next, eOutPos, divUnroll) |:
          Pow2(count_next.value * divUnroll) * inputs.io_req_bits_in1.value 
            - Pow2(w + 1) * regs.divisor.value * ghost_Q_next.value + ghost_Q_next.value 
        }.qed
      }
      if (when((divby0 && !regs.isHi))) neg_out_next = neg_out_next := Lit(false).B 
    }
    // s_done_mul ^ s_done_div == 111 ^ 110 == 001, s_done_mul & ~s_done_div == 111 & ~110 == 001
    // if state == s_div, outMul == (011 & 001 === 001) == true; 
    // if state == s_mul, outMul == (010 & 001 === 001) == false
    val outMul = ((regs.state & (s_done_mul ^ s_done_div)) === (s_done_mul & ~s_done_div)) 
    io_resp_valid = io_resp_valid := (regs.state === s_done_div)
    if (when((inputs.io_resp_ready && io_resp_valid))) state_next = state_next := s_ready
    
    io_req_ready = io_req_ready := (regs.state === s_ready)
    if (when((io_req_ready && inputs.io_req_valid))) {
      state_next = state_next := Mux((lhs_sign || rhs_sign), s_neg_inputs, s_div)
      isHi_next = isHi_next := cmdHi
      resHi_next = resHi_next := Lit(false).B
      count_next = count_next := (if (fastMulW) Mux((cmdMul && halfWidth(inputs.io_req_bits_dw)), Lit(((w / mulUnroll) / 2)).U, Lit(0).U) else Lit(0).U)
      neg_out_next = neg_out_next := Mux(cmdHi, lhs_sign, (lhs_sign =/= rhs_sign))
      divisor_next = divisor_next := Cat(rhs_sign, rhs_in)
      remainder_next = remainder_next := lhs_in
      req_tag_next = req_tag_next := inputs.io_req_bits_tag
      req_dw_next = req_dw_next := inputs.io_req_bits_dw
      req_fn_next = req_fn_next := inputs.io_req_bits_fn
      req_in1_next = req_in1_next := inputs.io_req_bits_in1
      req_in2_next = req_in2_next := inputs.io_req_bits_in2
    }
    // fastMulw == false, so loOut == result(((w / 2) - 1), 0)
    // when w <= 32, halfWidth == false, so hiOut == result((w - 1), (w / 2)), io_resp_bits_data == result(w - 1, 0)
    val loOut = Mux(((Lit(fastMulW).B && halfWidth(regs.req_dw)) && outMul), result((w - 1), (w / 2)), result(((w / 2) - 1), 0))
    val hiOut = Mux(halfWidth(regs.req_dw), Fill((w / 2), loOut(((w / 2) - 1))), result((w - 1), (w / 2)))
    io_resp_bits_tag = io_resp_bits_tag := regs.req_tag
    io_resp_bits_data = io_resp_bits_data := Cat(hiOut, loOut)

    (
      DivOutputs(
        io_req_ready,
        io_resp_valid,
        io_resp_bits_data,
        io_resp_bits_tag
      ),
      DivRegs(
        state_next,
        req_dw_next,
        req_in1_next,
        req_in2_next,
        req_tag_next,
        req_fn_next,
        count_next,
        neg_out_next,
        isHi_next,
        resHi_next,
        divisor_next,
        remainder_next,
        // ghost_R_next,
        ghost_Q_next
      )
    )
  } // ensuring { case (outputs, regNexts) => outputsRequire(outputs) && regsRequire(regNexts) && postCond(inputs, outputs, regNexts) }
  
  @library
  def divRun(timeout: Int, inputs: DivInputs, regInit: DivRegs): (DivOutputs, DivRegs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      divRun(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }

  @ignore
  def run(inputs: DivInputs, randomInitValue: DivRegs): (DivOutputs, DivRegs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = DivRegs(
      Lit(0, 3).U,
      randomInitValue.req_dw,
      randomInitValue.req_in1,
      randomInitValue.req_in2,
      randomInitValue.req_tag,
      randomInitValue.req_fn,
      randomInitValue.count,
      randomInitValue.neg_out,
      randomInitValue.isHi,
      randomInitValue.resHi,
      randomInitValue.divisor,
      randomInitValue.remainder,
      randomInitValue.ghost_Q
    )
    divRun(100, inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}