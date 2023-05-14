package RocketChip

import chisel3._
import chisel3.util._
import chiseltest._
import org.scalatest.flatspec.AnyFlatSpec
import scala.util.Random

trait MulSpecTest {
  def seek(c: Mul, data: Int, timeout: Int = 100): Unit = {
    if (timeout >= 0) {
      if (c.io.resp.valid.peek().litToBoolean) {
        c.io.resp.bits.data.expect(data.U)
        c.io.resp.ready.poke(true.B)
        c.clock.step()
      } else {
        c.clock.step()
        seek(c, data, timeout - 1)
      }
    } else {
      assert(false, "timeout")
    }
  }

  def mulTest(c: Mul) = {
    val in1 = Random.nextInt(1000)
    val in2 = Random.nextInt(1000)
    val mul = in1 * in2

    c.io.req.valid.poke(true.B)
    c.io.req.bits.fn.poke(0.U) // Mul
    c.io.req.bits.dw.poke(true.B)
    c.io.req.bits.in1.poke(in1.U)
    c.io.req.bits.in2.poke(in2.U)

    seek(c, mul)
  }
}

class MulSpec extends AnyFlatSpec with ChiselScalatestTester with MulSpecTest {
  behavior of "MulDiv"
  it should "pass Mul test" in {
    test(new Mul(MulDivParams(), 64)).withAnnotations(Seq(WriteVcdAnnotation)) { c =>
      mulTest(c)
    }
  }
}
