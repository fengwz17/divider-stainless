package RocketChip

import chisel3._
import chisel3.util._

import RocketChip.util._

class Div(cfg: MulDivParams, width: Int, nXpr: Int = 32) extends Module {
  private def minDivLatency = (cfg.divUnroll > 0).option(if (cfg.divEarlyOut) 3 else 1 + w / cfg.divUnroll)
  def minLatency: Int       = minDivLatency.get

  val io = IO(new MultiplierIO(width, log2Up(nXpr)))

  val w        = io.req.bits.in1.getWidth
  val mulw     = if (cfg.mulUnroll == 0) w else (w + cfg.mulUnroll - 1) / cfg.mulUnroll * cfg.mulUnroll
  val fastMulW = if (cfg.mulUnroll == 0) false else w / 2 > cfg.mulUnroll && w % (2 * cfg.mulUnroll) == 0

  val s_ready :: s_neg_inputs :: s_div :: s_dummy :: s_neg_output :: s_done_div :: Nil = Enum(6)

  val state = RegInit(s_ready)

  val req = Reg(chiselTypeOf(io.req.bits))
  val count = Reg(
    UInt(
      log2Ceil((cfg.divUnroll != 0).option(w / cfg.divUnroll + 1).get).W
    )
  )
  val neg_out   = Reg(Bool())
  val isHi      = Reg(Bool())
  val resHi     = Reg(Bool())
  val divisor   = Reg(Bits((w + 1).W))        // div only needs w bits
  val remainder = Reg(Bits((2 * mulw + 2).W)) // div only needs 2*w+1 bits

  val cmdMul, cmdHi, lhsSigned, rhsSigned = WireInit(false.B)
  if (cfg.divUnroll != 0) {
    switch(io.req.bits.fn) {
      is(4.U) { // aluFn.FN_DIV
        cmdMul    := false.B
        cmdHi     := false.B
        lhsSigned := true.B
        rhsSigned := true.B
      }
    }
  }

  require(w == 32 || w == 64)
  def halfWidth(req: MultiplierReq) = (w > 32).B && req.dw === false.B

  def sext(x: Bits, halfW: Bool, signed: Bool) = {
    val sign = signed && Mux(halfW, x(w / 2 - 1), x(w - 1))
    val hi   = Mux(halfW, Fill(w / 2, sign), x(w - 1, w / 2))
    (Cat(hi, x(w / 2 - 1, 0)), sign)
  }
  val (lhs_in, lhs_sign) = sext(io.req.bits.in1, halfWidth(io.req.bits), lhsSigned)
  val (rhs_in, rhs_sign) = sext(io.req.bits.in2, halfWidth(io.req.bits), rhsSigned)

  val subtractor        = remainder(2 * w, w) - divisor
  val result            = Mux(resHi, remainder(2 * w, w + 1), remainder(w - 1, 0))
  val negated_remainder = -result

  if (cfg.divUnroll != 0) when(state === s_neg_inputs) {
    when(remainder(w - 1)) {
      remainder := negated_remainder
    }
    when(divisor(w - 1)) {
      divisor := subtractor
    }
    state := s_div
  }
  if (cfg.divUnroll != 0) when(state === s_neg_output) {
    remainder := negated_remainder
    state     := s_done_div
    resHi     := false.B
  }
  if (cfg.divUnroll != 0) when(state === s_div) {
    val unrolls = ((0 until cfg.divUnroll) scanLeft remainder) { case (rem, i) =>
      // the special case for iteration 0 is to save HW, not for correctness
      val difference = if (i == 0) subtractor else rem(2 * w, w) - divisor(w - 1, 0)
      val less       = difference(w)
      Cat(Mux(less, rem(2 * w - 1, w), difference(w - 1, 0)), rem(w - 1, 0), !less)
    }.tail

    remainder := unrolls.last
    when(count === (w / cfg.divUnroll).U) {
      state       := Mux(neg_out, s_neg_output, s_done_div)
      resHi       := isHi
      if (w        % cfg.divUnroll < cfg.divUnroll - 1)
        remainder := unrolls(w % cfg.divUnroll)
    }
    count := count + 1.U

    val divby0 = count === 0.U && !subtractor(w)
    if (cfg.divEarlyOut) {
      val align       = 1 << log2Floor(cfg.divUnroll max cfg.divEarlyOutGranularity)
      val alignMask   = ~((align - 1).U(log2Ceil(w).W))
      val divisorMSB  = Log2(divisor(w - 1, 0), w) & alignMask
      val dividendMSB = Log2(remainder(w - 1, 0), w) | ~alignMask
      val eOutPos     = ~(dividendMSB - divisorMSB)
      val eOut        = count === 0.U && !divby0 && eOutPos >= align.U
      when(eOut) {
        remainder := remainder(w - 1, 0) << eOutPos
        count     := eOutPos >> log2Floor(cfg.divUnroll)
      }
    }
    when(divby0 && !isHi) { neg_out := false.B }
  }
  when(io.resp.fire) {
    state := s_ready
  }
  when(io.req.fire) {
    state     := Mux(lhs_sign || rhs_sign, s_neg_inputs, s_div)
    isHi      := cmdHi
    resHi     := false.B
    count     := (if (fastMulW) Mux[UInt](cmdMul && halfWidth(io.req.bits), (w / cfg.mulUnroll / 2).U, 0.U) else 0.U)
    neg_out   := Mux(cmdHi, lhs_sign, lhs_sign =/= rhs_sign)
    divisor   := Cat(rhs_sign, rhs_in)
    remainder := lhs_in
    req       := io.req.bits
  }

  val outMul = (state & (s_done_div)) === (false.B & ~s_done_div)
  val loOut  = Mux(fastMulW.B && halfWidth(req) && outMul, result(w - 1, w / 2), result(w / 2 - 1, 0))
  val hiOut  = Mux(halfWidth(req), Fill(w / 2, loOut(w / 2 - 1)), result(w - 1, w / 2))
  io.resp.bits.tag := req.tag

  io.resp.bits.data := Cat(hiOut, loOut)
  io.resp.valid     := (state === s_done_div)
  io.req.ready      := state === s_ready
}
