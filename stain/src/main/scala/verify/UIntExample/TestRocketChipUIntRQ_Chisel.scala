package UIntExample

import chisel3._
import chisel3.util._

class TestRocketChipUIntRQ(len: Int = 64) extends Module {
  val io = IO(new Bundle {
    val in1  = Input(UInt(len.W))
    val in2  = Input(UInt(len.W))
    val outQ = Output(UInt(len.W))
    val outR = Output(UInt(len.W))
  })

  val s_init :: s_compute :: s_finish :: Nil = Enum(3)

  val cnt = Reg(UInt(len.W))
  val R = Reg(UInt((2 * len).W))
  val Q = Reg(UInt(len.W))
  val state = RegInit(s_init)

  when(state === s_init) {
    R := io.in1
    Q := 0.U
    cnt := 0.U
    state := s_compute
  }.elsewhen(state === s_compute) {
    val sub = len.U - cnt
    val shift = (io.in2 << (len.U - cnt))(2 * len - 1, 0)
    val subtractor = R - shift

    printf(p"R_len: ${R.getWidth}, io.in2: ${io.in2.getWidth}, len_len: ${len.U.getWidth}, sub_len: ${sub.getWidth}, shift_len: ${shift.getWidth}, subtractor: ${subtractor.getWidth}\n")
    printf("R: %b, io.in2: %b, len: %b, cnt: %b, sub: %b, shift: %b, subtractor: %b\n", R, io.in2, len.U, cnt, sub, shift, subtractor)
    
    val less = subtractor(2 * len - 1)
    R := Mux(less, R, subtractor)
    Q := Mux(less, Q << 1.U, (Q << 1.U) + 1.U)
    cnt := cnt + 1.U
  }
  //   when(cnt === (len - 1).U) { state := s_finish }
  // }.elsewhen(state === s_finish) {
  //   state := s_init
  // }
  
  printf("cnt: %d\n", cnt)
  printf("state: %d\n", state)
  io.outR := R
  io.outQ := Q
}