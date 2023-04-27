import stainless.lang._

def foo(x: BigInt): BigInt = {
  require(0 <= x)
  require(x <= 5)
  var res = BigInt(11)
  var i = 2 * res
  val array = Array[BigInt](x)
  array.update(0, 1)
  assert(array(0) == 1)

  (while(i > 0) {
    i = i - 1
    res = res + i
  }) invariant(i >= 0 && res >= x)
  res
}