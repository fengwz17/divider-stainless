package XiangShan

import chisel3._
import chisel3.util._
import chiseltest._
import org.scalatest.flatspec.AnyFlatSpec

class ArrayMulDataModuleSpec extends AnyFlatSpec with ChiselScalatestTester {
  behavior of "ArrayMulDataModule"
  it should "pass Mul test" in {
    test(new ArrayMulDataModule(5)) { c =>
      c.io.a.poke(16.U)
      c.io.b.poke(1.U)
      c.io.regEnables(0).poke(true.B)
      c.io.regEnables(1).poke(false.B)
      // c.io.result.expect("b000001111".U)
      var j = 0
      while (j <= 20) {
        // println("hi: ", c.hi.peek())
        // println("lo: ", c.lo.peek())
        println(c.io.result.peek())
        c.clock.step()
        j = j + 1
      }
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
