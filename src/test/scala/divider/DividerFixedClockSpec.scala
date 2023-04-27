package divider

import chisel3._
import chisel3.util._
import chiseltest._
import org.scalatest.flatspec.AnyFlatSpec

class DividerFixedClockSpec extends AnyFlatSpec with ChiselScalatestTester {
  behavior of "DividerFixedClock"
  it should "pass divid test" in {
    test(new DividerFixedClock(4)) { c =>
      c.io.in.valid.poke(true.B)
      c.io.in.bits(0).poke(5.U)
      c.io.in.bits(1).poke(3.U)
      c.clock.step(7)
      c.io.out.valid.expect(true.B)
      c.io.out.bits.expect("b1001".U)
      // var j = 0
      // while (j <= 20) {
      //   // println("hi: ", c.hi.peek())
      //   // println("lo: ", c.lo.peek())
      //   println(c.io.out.valid.peek())
      //   println(c.io.out.bits.peekInt())
      //   c.clock.step()
      //   j = j + 1
      // }
    }
  }
  // it should "could emit low-firrtl" in {
  //   (new chisel3.stage.ChiselStage)
  //     .emitFirrtl(new DividerFixedClock(64), Array("-E", "low", "--target-dir", "test_run_dir/" + getTestName))
  // }
  // it should "could emit btor2" in {
  //   (new chisel3.stage.ChiselStage)
  //     .emitFirrtl(new DividerFixedClock(64), Array("-E", "btor2", "--target-dir", "test_run_dir/" + getTestName))
  // }
}
