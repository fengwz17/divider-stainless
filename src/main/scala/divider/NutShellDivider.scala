package divider

import chisel3._
import chisel3.util._

// class MulDivIO(val len: Int) extends Bundle {
//   val in = Flipped(DecoupledIO(Vec(2, Output(UInt(len.W)))))
//   val sign = Input(Bool())
//   val out = DecoupledIO(Output(UInt((len * 2).W)))
// }

class NutShellDivider(len: Int = 64) extends Module {
  val io = IO(new MulDivIO(len))

  def abs(a: UInt, sign: Bool): (Bool, UInt) = {
    val s = a(len - 1) && sign
    (s, Mux(s, -a, a))
  }

  val s_idle :: s_log2 :: s_shift :: s_compute :: s_finish :: Nil = Enum(5)
  val state = RegInit(s_idle)
  val newReq = (state === s_idle) && io.in.fire()

  val (a, b) = (io.in.bits(0), io.in.bits(1))
  val divBy0 = b === 0.U(len.W)

  val shiftReg = Reg(UInt((1 + len * 2).W))
  val hi = shiftReg(len * 2, len)
  val lo = shiftReg(len - 1, 0)

  val (aSign, aVal) = abs(a, io.sign)
  val (bSign, bVal) = abs(b, io.sign)
  val aSignReg = RegEnable(aSign, newReq)
  val qSignReg = RegEnable((aSign ^ bSign) && !divBy0, newReq)
  val bReg = RegEnable(bVal, newReq)
  val aValx2Reg = RegEnable(Cat(aVal, "b0".U), newReq)

  val cnt = Counter(len)
  when (newReq) {
    state := s_log2
  } .elsewhen (state === s_log2) {
    // `canSkipShift` is calculated as following:
    //   bEffectiveBit = Log2(bVal, XLEN) + 1.U
    //   aLeadingZero = 64.U - aEffectiveBit = 64.U - (Log2(aVal, XLEN) + 1.U)
    //   canSkipShift = aLeadingZero + bEffectiveBit
    //     = 64.U - (Log2(aVal, XLEN) + 1.U) + Log2(bVal, XLEN) + 1.U
    //     = 64.U + Log2(bVal, XLEN) - Log2(aVal, XLEN)
    //     = (64.U | Log2(bVal, XLEN)) - Log2(aVal, XLEN)  // since Log2(bVal, XLEN) < 64.U
    val canSkipShift = (len.U | Log2(bReg)) - Log2(aValx2Reg)
    // When divide by 0, the quotient should be all 1's.
    // Therefore we can not shift in 0s here.
    // We do not skip any shift to avoid this.
    cnt.value := Mux(divBy0, 0.U, Mux(canSkipShift >= (len-1).U, (len-1).U, canSkipShift))
    state := s_shift
  } .elsewhen (state === s_shift) {
    shiftReg := aValx2Reg << cnt.value
    state := s_compute
  } .elsewhen (state === s_compute) {
    val enough = hi.asUInt >= bReg.asUInt
    shiftReg := Cat(Mux(enough, hi - bReg, hi)(len - 1, 0), lo, enough)
    cnt.inc()
    when (cnt.value === (len-1).U) { state := s_finish }
  } .elsewhen (state === s_finish) {
    state := s_idle
  }

  val r = hi(len, 1)
  val resQ = Mux(qSignReg, -lo, lo)
  val resR = Mux(aSignReg, -r, r)
  io.out.bits := Cat(resR, resQ)

  io.out.valid := (state === s_finish) // FIXME: should deal with ready = 0
  io.in.ready := (state === s_idle)
}