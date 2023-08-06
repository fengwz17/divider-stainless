package verify

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

// import chicala._
// import scala.collection.immutable.MapKeyValueTupleReverseIterator

object MultiplierTest {

  def Pow2(exp: BigInt): BigInt = {
      require(exp >= 0) 
      val result = exp match {
        case BigInt(0) => BigInt(1)
        case _ => BigInt(2) * Pow2(exp - 1)
      }
      result
  } ensuring(res => res > 0)

  @library
  def Pow2neg(exp: BigInt): BigInt = {
    val result = exp match {
      case neg if neg < BigInt(0) => BigInt(0)
      case _ => Pow2(exp)
    }
    result
  } ensuring(res => res >= 0)

  @opaque  @library
  def Pow2Mul(s: BigInt, x: BigInt, y: BigInt): Unit = {
    require(x >= 0)
    require(y >= 0)
    require(s == x + y)
    decreases(x)
    x match {
      case BigInt(0) => ()
      case _ => {
        Pow2(s)                           ==:| trivial |:
        Pow2(x + y)                       ==:| trivial |:
        BigInt(2) * Pow2(x - 1 + y)       ==:| Pow2Mul(x + y - 1, x - 1, y) |:
        BigInt(2) * Pow2(x - 1) * Pow2(y) ==:| trivial |:
        Pow2(x) * Pow2(y) 
      }.qed
    }
  }.ensuring(_ => Pow2(s) == Pow2(x) * Pow2(y))


  def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
    case true => y
    case _ => z
  } // ensuring(res => (x && (res == y)) || (!x && (res == z)))

  // @ignore
  // def Cat(a: BigInt, b: BigInt, len: BigInt): BigInt = {
  //   require(len >= 0 && a >= 0 && b >= 0)
  //   val result = len match {
  //     case zero if (len == 0) => a
  //     case _ => a * Pow2(len) + b
  //   }
  //   result
  // } ensuring(res => res >= 0)

  // @ignore
  // def Extract(a: BigInt, index: BigInt): (BigInt, BigInt) = {
  //     require(a >= 0 && index >= 0) // && Pow2(index) > 0)
  //     // high = a(n - 1, index)
  //     // low = a(index - 1, 0)
  //     val high = a / Pow2(index)
  //     // val low = a - high * Pow2(index)
  //     val low = a % Pow2(index)
  //     (high, low)
  // } ensuring(res => a == res._1 * Pow2(index) + res._2 && 0 <= res._2 && res._2 < Pow2(index))

  @opaque  @library
  def lemmaExtract_ai_a(i: BigInt, a: BigInt, len: BigInt): Unit = {
    require(BigInt(2) <= i && i < len)
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    val l1 = (BigInt(2) * a) / Pow2(i + 1)
    val l2 = (BigInt(2) * a - l1 * Pow2(i + 1)) / Pow2(i) 
    assert(BigInt(2) * a - l1 * Pow2(i + 1) < Pow2(i + 1))
    assert(l2 < BigInt(2) && l2 >= BigInt(0))
    val l3 = (BigInt(2) * a - l1 * Pow2(i + 1) - l2 * Pow2(i)) / Pow2(i - 2)
    assert(l3 < Pow2(2) && l3 >= BigInt(0))
    val l4 = BigInt(2) * a - l1 * Pow2(i + 1) - l2 * Pow2(i) - l3 * Pow2(i - 2)
    assert(l4 < Pow2(i - 2) && l4 >= BigInt(0))

    assert(BigInt(2) * a == l4 + l3 * Pow2(i - 2) + l2 * Pow2(i) + l1 * Pow2(i + 1))

    assert(l2 * Pow2(i) == l2 * Pow2(i - 2) * Pow2(2))
    assert(l1 * Pow2(i + 1) == l1 * Pow2(i - 2) * Pow2(3))
    {
      l2 * Pow2(i)                ==:| Pow2Mul(i, i - 2, BigInt(2)) |:
      l2 * Pow2(i - 2) * Pow2(2)
    }.qed
    {
      l1 * Pow2(i + 1)            ==:| Pow2Mul(i + 1, i - 2, BigInt(3)) |:
      l1 * Pow2(i - 2) * Pow2(3)
    }.qed

    {
      ((BigInt(2) * a) / Pow2(i - 2) % Pow2(3)) / Pow2(2)                                                                   ==:| trivial |:   
      ((l4 + l3 * Pow2(i - 2) + l2 * Pow2(i) + l1 * Pow2(i + 1)) / Pow2(i - 2) % Pow2(3)) / Pow2(2)                         ==:| trivial |:
      ((l4 + l3 * Pow2(i - 2) + l2 * Pow2(i - 2) * Pow2(2) + l1 * Pow2(i + 1)) / Pow2(i - 2) % Pow2(3)) / Pow2(2)           ==:| trivial |:
      ((l4 + l3 * Pow2(i - 2) + l2 * Pow2(i - 2) * Pow2(2) + l1 * Pow2(i - 2) * Pow2(3)) / Pow2(i - 2) % Pow2(3)) / Pow2(2) ==:| trivial |:
      ((l4 + (l3 + l2 * Pow2(2) + l1 * Pow2(3)) * Pow2(i - 2)) / Pow2(i - 2) % Pow2(3)) / Pow2(2)                       
    }.qed

    assert((l4 + (l3 + l2 * Pow2(2) + l1 * Pow2(3)) * Pow2(i - 2)) / Pow2(i - 2) == l3 + l2 * Pow2(2) + l1 * Pow2(3))
    assert(l3 + l2 * Pow2(2) < Pow2(3))
    val tmpl3l2l1 = l3 + l2 * Pow2(2) + l1 * Pow2(3)
    assert(tmpl3l2l1 % Pow2(3) ==  tmpl3l2l1 - tmpl3l2l1 / Pow2(3) * Pow2(3))
    assert((l3 + l2 * Pow2(2) + l1 * Pow2(3)) / Pow2(3) == l1)
    {
      ((l4 + (l3 + l2 * Pow2(2) + l1 * Pow2(3)) * Pow2(i - 2)) / Pow2(i - 2) % Pow2(3)) / Pow2(2) ==:| trivial |:
      (l3 + l2 * Pow2(2) + l1 * Pow2(3)) % Pow2(3) / Pow2(2)                                      ==:| trivial |:
      tmpl3l2l1 % Pow2(3) / Pow2(2)                                                               ==:| trivial |:
      (tmpl3l2l1 - tmpl3l2l1 / Pow2(3) * Pow2(3)) / Pow2(2)                                       ==:| trivial |:
      (l3 + l2 * Pow2(2) + l1 * Pow2(3) - (l3 + l2 * Pow2(2) + l1 * Pow2(3)) / Pow2(3) * Pow2(3)) / Pow2(2) ==:| trivial |:
      (l3 + l2 * Pow2(2) + l1 * Pow2(3) - l1 * Pow2(3)) / Pow2(2)                                 ==:| trivial |:
      (l3 + l2 * Pow2(2)) / Pow2(2)                                                               ==:| trivial |:
      l2
    }.qed
    // up to now, we proved:
    //    ((BigInt(2) * a) / Pow2(i - 2)) % Pow2(3)) / Pow2(2) == l2
    // then, we need to prove l2 == ((BigInt(2) * a) / Pow2(i)) % BigInt(2)
    val tmp_a_l1l2 = BigInt(2) * a - l1 * Pow2(i + 1) - l2 * Pow2(i)
    {
      l1 * Pow2(i + 1) ==:| trivial |:
      l1 * Pow2(i) * BigInt(2)
    }.qed
    assert(l1 * Pow2(i + 1) == l1 * Pow2(i) * BigInt(2))
    assert(BigInt(2) * a - l1 * Pow2(i + 1) < Pow2(i + 1))
    assert(tmp_a_l1l2 < Pow2(i))
    {
      ((BigInt(2) * a) / Pow2(i)) % BigInt(2)                                       ==:| trivial |:
      (l1 * Pow2(i + 1) + l2 * Pow2(i) + tmp_a_l1l2) / Pow2(i) % BigInt(2)          ==:| trivial |:
      (l1 * Pow2(i) * BigInt(2) + l2 * Pow2(i) + tmp_a_l1l2) / Pow2(i) % BigInt(2)  ==:| trivial |:
      ((l1 * BigInt(2) + l2) * Pow2(i) + tmp_a_l1l2) / Pow2(i) % BigInt(2)          ==:| trivial |:
      (l1 * BigInt(2) + l2) % BigInt(2)                                             ==:| trivial |:
      l2
    }.qed

    {
      ((BigInt(2) * a) / Pow2(i - 2) % Pow2(3)) / Pow2(2)                                         ==:| trivial |:
      ((l4 + (l3 + l2 * Pow2(2) + l1 * Pow2(3)) * Pow2(i - 2)) / Pow2(i - 2) % Pow2(3)) / Pow2(2) ==:| trivial |:
      l2                                                                                          ==:| trivial |:
      ((BigInt(2) * a) / Pow2(i)) % BigInt(2)
    }.qed
    assert(((BigInt(2) * a) / Pow2(i - 2) % Pow2(3)) / Pow2(2) == ((BigInt(2) * a) / Pow2(i)) % BigInt(2))
  }.ensuring(_ => (((BigInt(2) * a) / Pow2(i - 2)) % Pow2(3)) / Pow2(2) == ((BigInt(2) * a) / Pow2(i)) % BigInt(2))

  // (a / Pow2(i - 1)) == (2 * a / Pow2(i))
  @opaque  @library
  def lemmaPow2div(i: BigInt, a: BigInt, len: BigInt): Unit = {
    require(len >= 5)
    require(i >= BigInt(2) && i < len && i % 2 == 0)
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    val x = a / Pow2(i - 1)
    val y = a - x * Pow2(i - 1)
    assert(y < Pow2(i - 1))
    {
      2 * a / Pow2(i)                           ==:| trivial |:
      2 * (y + x * Pow2(i - 1)) / Pow2(i)       ==:| trivial |:
      (2 * y + x * Pow2(i)) / Pow2(i)           ==:| {2 * y < Pow2(i)} |:
      x                                         ==:| trivial |:
      a / Pow2(i - 1)
    }.qed
  }.ensuring(a / Pow2(i - 1) == (2 * a / Pow2(i)))

  // a / Pow2(x) / Pow2(y)  == a / Pow2(x + y)
  @opaque  @library
  def lemmaPow2DivAdd(a: BigInt, x: BigInt, y: BigInt): Unit = {
    require(x >= 0 && y >= 0)
    require(a >= 0)
    val h = a / Pow2(x + y)
    val l = a - h * Pow2(x + y)
    assert(l < Pow2(x + y))
    {
      Pow2(x + y) ==:| Pow2Mul(x + y, x, y) |:
      Pow2(x) * Pow2(y)
    }.qed
    assert(l < Pow2(x) * Pow2(y))
    val lh = l / Pow2(x)
    val ll = l - lh * Pow2(x)
    assert(lh * Pow2(x) <= l)
    assert(lh < Pow2(y))
    assert(ll < Pow2(x))
    {
      a / Pow2(x) / Pow2(y)                                             ==:| trivial |:
      (l + h * Pow2(x + y)) / Pow2(x) / Pow2(y)                         ==:| Pow2Mul(x + y, x, y) |:
      (l + h * Pow2(x) * Pow2(y)) / Pow2(x) / Pow2(y)                   ==:| trivial |:
      (ll + lh * Pow2(x) + h * Pow2(x) * Pow2(y)) / Pow2(x) / Pow2(y)   ==:| trivial |:
      (lh + h * Pow2(y)) / Pow2(y)                                      ==:| trivial |:
      h                                                                 ==:| trivial |:
      a / Pow2(x + y)
    }.qed
  }.ensuring(a / Pow2(x) / Pow2(y) == a / Pow2(x + y))

  @opaque  @library
  def lemmaPow2ModMod(a: BigInt, x: BigInt, y: BigInt): Unit = {
    require(a >= 0)
    require(x >= 0 && y >= 0)
    require(x >= y)
    val h = a / Pow2(x) 
    val l = a % Pow2(x)
    val hl = l / Pow2(y)
    val ll = l % Pow2(y)
    assert(ll < Pow2(y))
    assert(ll == l - hl * Pow2(y))
    assert(l == a - h * Pow2(x))
    assert(ll == a - h * Pow2(x) - hl * Pow2(y))
    assert((Pow2(y) * (h * Pow2(x - y) + hl) + ll) / Pow2(y) == h * Pow2(x - y) + hl) 
    Pow2Mul(x, x - y, y)
    assert(h * Pow2(x) == h * Pow2(x - y) * Pow2(y))
    {
      a % Pow2(y)                                                             ==:| trivial |:
      a - a / Pow2(y) * Pow2(y)                                               ==:| trivial |:
      a - (h * Pow2(x) + hl * Pow2(y) + ll) / Pow2(y) * Pow2(y)               ==:| Pow2Mul(x, x - y, y) |:
      a - (h * Pow2(x - y) * Pow2(y) + hl * Pow2(y) + ll) / Pow2(y) * Pow2(y) ==:| trivial |:
      a - (Pow2(y) * (h * Pow2(x - y) + hl) + ll) / Pow2(y) * Pow2(y)         ==:| trivial |:
      a - (h * Pow2(x - y) + hl) * Pow2(y)                                    ==:| trivial |:
      a - (h * Pow2(x - y) * Pow2(y) + hl * Pow2(y))                          ==:| Pow2Mul(x, x - y, y) |:
      a - h * Pow2(x) - hl * Pow2(y)                                          ==:| trivial |:
      ll                                                                      ==:| trivial |:
      l % Pow2(y)                                                             ==:| trivial |:
      a % Pow2(x) % Pow2(y)                               
    }.qed 
  }.ensuring(a % Pow2(y) == a % Pow2(x) % Pow2(y))
 
  @opaque  @library
  def lemmaPow2lt(c: BigInt, b: BigInt): Unit = {
    require(0 <= b)
    require(b < c)
    {
      Pow2(c)         ==:| trivial |:
      Pow2(c - b + b) ==:| Pow2Mul(c, c - b, b) |:
      Pow2(b) * Pow2(c - b)
    }.qed
    assert(c - b > 0)
    assert(Pow2(c - b) > 1)
    assert(Pow2(c) > Pow2(b))
  }.ensuring(_ => Pow2(c) > Pow2(b))

  @opaque @library
  def lemmaPow2Mod(a: BigInt, pow2b: BigInt, c: BigInt): Unit = {
    require(c >= BigInt(0))
    require(a >= c)
    require(pow2b >= 0)
    // lemmaPow2lt(c, b)
    require(pow2b < Pow2(c))
    assert(Pow2(a - c) >= 0)
    {
      ((Pow2(a - c) * Pow2(c) + pow2b)) / Pow2(c) ==:| trivial |:
      Pow2(a - c)
    }.qed
    {
      (Pow2(a) + pow2b) % Pow2(c)                                                 ==:| trivial |:
      (Pow2(a) + pow2b) - (Pow2(a) + pow2b) / Pow2(c) * Pow2(c)                 ==:| Pow2Mul(a, a - c, c) |:
      (Pow2(a) + pow2b) - ((Pow2(a - c) * Pow2(c) + pow2b)) / Pow2(c) * Pow2(c) ==:| trivial |:
      (Pow2(a) + pow2b) - Pow2(a - c) * Pow2(c)                                   ==:| Pow2Mul(a, a - c, c) |:
      (Pow2(a) + pow2b) - Pow2(a)                                                 ==:| trivial |:
      pow2b
    }.qed
  }.ensuring((Pow2(a) + pow2b) % Pow2(c) == pow2b)

  @opaque  @library
  def inductionProveAsumUnsign(i: BigInt, len: BigInt, a: BigInt, x: BigInt): Unit = {
    require(len >= 5)
    require(i >= 1 && i < len && i % 2 == 0)
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    require(x == a / Pow2(i - 1) % Pow2(3))
    val xh = x / 2
    val xl = x - xh * 2
    val h1 = a / Pow2(i + 2)
    val l1 = a - h1 * Pow2(i + 2)
    val h2 = a / Pow2(i - 1)
    val l2 = a - h2 * Pow2(i - 1)
    
    assert(h1 == h2 / Pow2(3))
    assert(x == h2 % Pow2(3))
    assert(h2 == h1 * Pow2(3) + x)
    {
      a                                       ==:| trivial |:
      h2 * Pow2(i - 1) + l2                   ==:| trivial |:
      (x + h1 * Pow2(3)) * Pow2(i - 1) + l2   ==:| Pow2Mul(i + 2, 3, i - 1) |:
      x * Pow2(i - 1) + h1 * Pow2(i + 2) + l2
    }.qed
    assert(a == x * Pow2(i - 1) + h1 * Pow2(i + 2) + l2)
    assert(xl <= BigInt(1))
    assert(l2 <= Pow2(i - 1) - 1)
    assert(xl * Pow2(i - 1) + l2 < Pow2(i))
    {
      a / Pow2(i)                                                               ==:| trivial |:
      (x * Pow2(i - 1) + h1 * Pow2(i + 2) + l2) / Pow2(i)                       ==:| trivial |:
      ((xl + xh * BigInt(2)) * Pow2(i - 1) + h1 * Pow2(i + 2) + l2) / Pow2(i)   ==:| trivial |:
      (xl * Pow2(i - 1) + xh * Pow2(i) + h1 * Pow2(i + 2) + l2) / Pow2(i)       ==:| Pow2Mul(i + 2, 2, i) |:
      (xl * Pow2(i - 1) + xh * Pow2(i) + h1 * Pow2(i) * Pow2(2) + l2) / Pow2(i) ==:| trivial |:
      (xl * Pow2(i - 1) + Pow2(i) * (xh + h1 * Pow2(2)) + l2) / Pow2(i)         ==:| trivial |:
      (xl * Pow2(i - 1) + l2 + Pow2(i) * (xh + h1 * Pow2(2))) / Pow2(i)         ==:| trivial |:
      (xh + h1 * Pow2(2)) + (xl * Pow2(i - 1) + l2) / Pow2(i)                   ==:| {xl * Pow2(i - 1) + l2 < Pow2(i)} |:
      xh + h1 * Pow2(2)
    }.qed
    assert(a / Pow2(i) == xh + h1 * Pow2(2))
    {
      a - a / Pow2(i) * Pow2(i) + Pow2(i) * (x / 2)         ==:| {a / Pow2(i) == xh + h1 * Pow2(2)} |:
      a - (xh + h1 * Pow2(2)) * Pow2(i) + Pow2(i) * xh      ==:| Pow2Mul(i + 2, i, 2) |:
      a - (xh * Pow2(i) + h1 * Pow2(i + 2)) + Pow2(i) * xh  ==:| trivial |:
      a - xh * Pow2(i) - h1 * Pow2(i + 2) + Pow2(i) * xh    ==:| trivial |: 
      a - h1 * Pow2(i + 2)                                  ==:| trivial |:
      a - (a / Pow2(i + 2)) * Pow2(i + 2)
    }.qed
    assert(a - (a / Pow2(i)) * Pow2(i) + Pow2(i) * (x / 2) == a - (a / Pow2(i + 2)) * Pow2(i + 2))
  }.ensuring(_ => a - (a / Pow2(i)) * Pow2(i) + Pow2(i) * (x / 2) == a - (a / Pow2(i + 2)) * Pow2(i + 2))
  
  @opaque  @library
  def lemmaPPtempSkb(x: BigInt, pp_temp: BigInt, s: BigInt, k: BigInt, b: BigInt, len: BigInt): Unit = {
    require(len >= 5)
    require(b > 0 && b <= Pow2(len - 2) - 1)
    val b_sext = b
    val bx2 = b * 2
    val neg_b = Pow2(len + 1) - BigInt(1) * b
    val neg_bx2 = Pow2(len + 1) - BigInt(2) * b
    val pp_temp_value = x match {
      case BigInt(1) => b_sext
      case BigInt(2) => b_sext
      case BigInt(3) => bx2
      case BigInt(4) => neg_bx2
      case BigInt(5) => neg_b
      case BigInt(6) => neg_b
      case _ => BigInt(0)
    }
    require(pp_temp == pp_temp_value)
    require(s == pp_temp / Pow2(len))
    val k_value = x match {
      case BigInt(1) => BigInt(1)
      case BigInt(2) => BigInt(1)
      case BigInt(3) => BigInt(2)
      case BigInt(4) => -BigInt(2)
      case BigInt(5) => -BigInt(1)
      case BigInt(6) => -BigInt(1)
      case _ => BigInt(0)
    }
    require(k == k_value)
     x match {
      case BigInt(1) => {
        assert(s == BigInt(0))
        assert(k == BigInt(1))
        pp_temp ==:| trivial |:
        b       ==:| trivial |:
        k * b   ==:| trivial |:
        Pow2(len + 1) * s + k * b    
      }.qed
      case BigInt(2) => {
        assert(s == BigInt(0))
        assert(k == BigInt(1))
        pp_temp ==:| trivial |:
        b       ==:| trivial |:
        k * b   ==:| trivial |:
        Pow2(len + 1) * s + k * b        
      }.qed
      case BigInt(3) => {
        assert(s == BigInt(0))
        assert(k == BigInt(2))
        pp_temp ==:| trivial |:
        2 * b   ==:| trivial |:
        k * b   ==:| trivial |:
        Pow2(len + 1) * s + k * b    
      }.qed
      case BigInt(4) => {
        assert(s == BigInt(1))
        assert(k == -BigInt(2))
        pp_temp ==:| trivial |:
        Pow2(len + 1) - BigInt(2) * b ==:| trivial |:
        Pow2(len + 1) * s + k * b     
      }.qed
      case BigInt(5) => {
        assert(s == BigInt(1))
        assert(k == -BigInt(1))
        pp_temp ==:| trivial |:
        Pow2(len + 1) - BigInt(1) * b ==:| trivial |:
        Pow2(len + 1) * s + k * b     
      }.qed
      case BigInt(6) => {
        assert(s == BigInt(1))
        assert(k == -BigInt(1))
        pp_temp ==:| trivial |:
        Pow2(len + 1) - BigInt(1) * b ==:| trivial |:
        Pow2(len + 1) * s + k * b     
      }.qed
      case _ => {
        assert(s == BigInt(0))
        assert(k == BigInt(0))
        pp_temp ==:| trivial |:
        BigInt(0)   ==:| trivial |:
        Pow2(len + 1) * s + k * b       
      }.qed
    }
  }.ensuring(_ => Pow2(len + 1) * s + k * b == pp_temp)

  @opaque  @library
  def lemma_ais1_ai_neg2aia1_k(x: BigInt, ais1: BigInt, ai: BigInt, aia1: BigInt, k: BigInt): Unit = {
    require(BigInt(0) <= x && x <= Pow2(3) - BigInt(1))
    require(aia1 == x / Pow2(2))
    require(ai == (x - aia1 * Pow2(2)) / BigInt(2))
    require(ais1 == x - aia1 * Pow2(2) - ai * BigInt(2))
    val k_value = x match {
      case BigInt(1) => BigInt(1)
      case BigInt(2) => BigInt(1)
      case BigInt(3) => BigInt(2)
      case BigInt(4) => -BigInt(2)
      case BigInt(5) => -BigInt(1)
      case BigInt(6) => -BigInt(1)
      case _ => BigInt(0)
    }
    require(k == k_value)
    assert(Pow2(3) - BigInt(1) == BigInt(7))
    x match {
      case BigInt(0) => {
        assert(aia1 == BigInt(0))
        assert(ai == BigInt(0))
        assert(ais1 == BigInt(0))
        assert(k == BigInt(0))
        ais1 + ai - BigInt(2) * aia1 ==:| trivial |:
        BigInt(0)                    ==:| trivial |:
        k
      }.qed
      case BigInt(1) => {
        assert(aia1 == BigInt(0))
        assert(ai == BigInt(0))
        assert(ais1 == BigInt(1))
        assert(k == BigInt(1))
        ais1 + ai - BigInt(2) * aia1 ==:| trivial |:
        BigInt(1)                    ==:| trivial |:
        k
      }.qed
      case BigInt(2) => {
        assert(aia1 == BigInt(0))
        assert(ai == BigInt(1))
        assert(ais1 == BigInt(0))
        assert(k == BigInt(1))
        ais1 + ai - BigInt(2) * aia1 ==:| trivial |:
        BigInt(1)                    ==:| trivial |:
        k
      }.qed
      case BigInt(3) => {
        assert(aia1 == BigInt(0))
        assert(ai == BigInt(1))
        assert(ais1 == BigInt(1))
        assert(k == BigInt(2))
        ais1 + ai - BigInt(2) * aia1 ==:| trivial |:
        BigInt(2)                    ==:| trivial |:
        k
      }.qed
      case BigInt(4) => {
        assert(aia1 == BigInt(1))
        assert(ai == BigInt(0))
        assert(ais1 == BigInt(0))
        assert(k == -BigInt(2))
        ais1 + ai - BigInt(2) * aia1 ==:| trivial |:
        -BigInt(2)                    ==:| trivial |:
        k
      }.qed
      case BigInt(5) => {
        assert(aia1 == BigInt(1))
        assert(ai == BigInt(0))
        assert(ais1 == BigInt(1))
        assert(k == -BigInt(1))
        ais1 + ai - BigInt(2) * aia1 ==:| trivial |:
        -BigInt(1)                    ==:| trivial |:
        k
      }.qed
      case BigInt(6) => {
        assert(aia1 == BigInt(1))
        assert(ai == BigInt(1))
        assert(ais1 == BigInt(0))
        assert(k == -BigInt(1))
        ais1 + ai - BigInt(2) * aia1 ==:| trivial |:
        -BigInt(1)                    ==:| trivial |:
        k
      }.qed
      case BigInt(7) => {
        assert(aia1 == BigInt(1))
        assert(ai == BigInt(1))
        assert(ais1 == BigInt(1))
        assert(k == BigInt(0))
        ais1 + ai - BigInt(2) * aia1 ==:| trivial |:
        BigInt(0)                    ==:| trivial |:
        k
      }.qed
    }
  }.ensuring(_ => ais1 + ai - BigInt(2) * aia1 == k)

  @opaque  @library 
  def lemma_pp_pow2weight_i0(len: BigInt, b: BigInt, pp: BigInt, s: BigInt, k: BigInt, pp_temp: BigInt, weight: BigInt): Unit = {
    require(len >= 5)
    require(b > 0 && b <= Pow2(len - 2) - 1)
    require(s == BigInt(0) || s == BigInt(1))
    require(pp_temp == Pow2(len + 1) * s + k * b)
    require(pp == ((1 - s) * Pow2(len + 3) + s * Pow2(len + 2) + s * Pow2(len + 1) + pp_temp))
    require(weight == BigInt(0))

    {
      pp * Pow2(weight) ==:| trivial |:
      ((1 - s) * Pow2(len + 3) + s * Pow2(len + 2) + s * Pow2(len + 1) + pp_temp) * Pow2(weight)                             ==:| {pp_temp == Pow2(len + 1) * s + k * b} |: 
      (Pow2(len + 3) - s * Pow2(len + 3) + s * Pow2(len + 2) + s * Pow2(len + 1) + Pow2(len + 1) * s + k * b) * Pow2(weight) ==:| trivial |:
      (Pow2(len + 3) + s * (-Pow2(len + 3) + Pow2(len + 2) + Pow2(len + 1) + Pow2(len + 1)) + k * b) * Pow2(weight)           ==:| trivial |:
      (Pow2(len + 3) + s * (-Pow2(len + 3) + Pow2(len + 2) + Pow2(len + 1) * 2) + k * b) * Pow2(weight)                       ==:| trivial |:
      (Pow2(len + 3) + s * (-Pow2(len + 3) + Pow2(len + 2) * 2) + k * b) * Pow2(weight)                                       ==:| trivial |:
      (Pow2(len + 3) + s * (-Pow2(len + 3) + Pow2(len + 3)) + k * b) * Pow2(weight)                                           ==:| trivial |:
      (Pow2(len + 3) + k * b) * Pow2(weight)                                                             ==:| trivial |:
      Pow2(len + 3) + k * b  
    }.qed
  }.ensuring(_ => pp * Pow2(weight) == Pow2(len + 3) + k * b)

  @opaque  @library
  def lemma_pp_pow2weight_i_last(len: BigInt, b: BigInt, pp: BigInt, s: BigInt, k: BigInt, pp_temp: BigInt, i: BigInt, weight: BigInt): Unit = {
    require(len >= 5)
    require(b > 0 && b <= Pow2(len - 2) - 1)
    require(s == BigInt(0) || s == BigInt(1))
    require(pp_temp == Pow2(len + 1) * s + k * b)
    require(pp == (((1 - s) * Pow2(len + 3) + pp_temp * 4)))
    require(i == len - 2 || i == len - 1)
    require(weight == i - BigInt(2))
    {
      Pow2(len + 1) * s * 4 ==:| trivial |:
      Pow2(len + 1) * s * Pow2(2) ==:| Pow2Mul(len + 3, len + 1, 2) |:
      Pow2(len + 3) * s
    }.qed
    {
      pp * Pow2(weight) ==:| trivial |:
      ((1 - s) * Pow2(len + 3) + pp_temp * 4) * Pow2(weight)                                  ==:| {pp_temp == Pow2(len + 1) * s + k * b} |: 
      (Pow2(len + 3) - s * Pow2(len + 3) + (Pow2(len + 1) * s + k * b) * 4) * Pow2(weight)    ==:| trivial |:
      (Pow2(len + 3) - s * Pow2(len + 3) + Pow2(len + 1) * s * 4 + k * b * 4) * Pow2(weight)  ==:| trivial |:
      (Pow2(len + 3) - s * Pow2(len + 3) + Pow2(len + 3) * s + k * b * 4) * Pow2(weight)      ==:| trivial |:
      (Pow2(len + 3) + k * b * 4) * Pow2(i - 2)                                               ==:| trivial |:
      Pow2(len + 3) * Pow2(i - 2) + k * b * Pow2(2) * Pow2(i - 2)                             ==:| Pow2Mul(len + i + 1, len + 3, i - 2) |:
      Pow2(len + i + 1) + k * b * Pow2(2) * Pow2(i - 2)                                       ==:| Pow2Mul(i, 2, i - 2) |:
      Pow2(len + i + 1) + k * b * Pow2(i)
    }.qed
  }.ensuring(_ => pp * Pow2(weight) == Pow2(len + i + 1) + k * b * Pow2(i))

  @opaque  @library
  def lemma_pp_pow2weight_i(len: BigInt, b: BigInt, pp: BigInt, s: BigInt, k: BigInt, pp_temp: BigInt, i: BigInt, weight: BigInt): Unit = {
    require(len >= 5)
    require(b > 0 && b <= Pow2(len - 2) - 1)
    require(s == BigInt(0) || s == BigInt(1))
    require(pp_temp == Pow2(len + 1) * s + k * b)
    require(pp == (Pow2(len + 4) + (1 - s) * Pow2(len + 3) + pp_temp * 4))
    require(i >= 2 && i <= len - 1)
    require(weight == i - BigInt(2))
    {
      Pow2(len + 3) * 3 * Pow2(i - 2) ==:| Pow2Mul(len + i + 1, len + 3, i - 2) |:
      Pow2(len + i + 1) * 3
    }.qed
    {
      pp * Pow2(weight) ==:| trivial |:
      (Pow2(len + 4) + (1 - s) * Pow2(len + 3) + pp_temp * 4) * Pow2(weight)                                          ==:|  {pp_temp == Pow2(len + 1) * s + k * b} |:
      (Pow2(len + 4) + Pow2(len + 3) - s * Pow2(len + 3) + (Pow2(len + 1) * s + k * b) * 4) * Pow2(weight)            ==:| trivial |:
      (Pow2(len + 4) + Pow2(len + 3) - s * Pow2(len + 3) + Pow2(len + 1) * s * 4 + k * b * 4) * Pow2(weight)          ==:| trivial |:
      (Pow2(len + 3) * BigInt(2) + Pow2(len + 3) - s * Pow2(len + 3) + Pow2(len + 3) * s + k * b * 4) * Pow2(weight)  ==:| trivial |:
      (Pow2(len + 3) * 3 + k * b * 4) * Pow2(weight)                                                                  ==:| trivial |: 
      (Pow2(len + 3) * 3 + k * b * 4) * Pow2(i - 2)                                                                   ==:| trivial |:
      Pow2(len + 3) * 3 * Pow2(i - 2) + k * b * 4 * Pow2(i - 2)                                                       ==:| trivial |:                                 
      Pow2(len + i + 1) * 3 + k * b * Pow2(2) * Pow2(i - 2)                                                           ==:| Pow2Mul(i, 2, i - 2) |:
      Pow2(len + i + 1) * 3 + k * b * Pow2(i)                                     
    }.qed
  }.ensuring(_ => pp * Pow2(weight) == Pow2(len + i + 1) * 3 + k * b * Pow2(i))

  @opaque  @library
  def lemma_last_x_next_i(len: BigInt, i: BigInt, a: BigInt, last_x_next: BigInt, x: BigInt): Unit = {
    require(len >= 5)
    require(i >= 2 && i < len && i % 2 == 0)
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    require(x == a / Pow2(i - 1) % Pow2(3))
    require(last_x_next == x)
    {
      last_x_next                           ==:| trivial |:
      x                                     ==:| trivial |:
      (a / Pow2(i - 1)) % Pow2(3)           ==:| lemmaPow2div(i, a, len) |:
      (2 * a / Pow2(i)) % Pow2(3)           ==:| trivial |:
      (2 * a / Pow2(i + 2 - 2)) % Pow2(3)
    }.qed
  }.ensuring(_ => last_x_next == (2 * a / Pow2(i + 2 - 2)) % Pow2(3))

  @opaque  @library
  def lemma_last_x_next_i0(len: BigInt, i: BigInt, a: BigInt, last_x_next: BigInt, x: BigInt): Unit = {
    require(len >= 5)
    require(i == BigInt(0))
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    require(x == a % 4 * 2)
    require(last_x_next == x)
    {
      last_x_next                           ==:| trivial |:
      x                                     ==:| trivial |:
      (a % 4) * 2                           ==:| trivial |:
      (2 * a) % Pow2(3)                     ==:| {i == BigInt(0)} |:
      (2 * a) / Pow2(i) % Pow2(3)           ==:| trivial |:
      (2 * a) / Pow2(i + 2 - 2) % Pow2(3) 
    }.qed
  }.ensuring(_ => last_x_next == (2 * a / Pow2(i + 2 - 2)) % Pow2(3))
  
  @opaque @library
  def lemma_last_x_next(len: BigInt, i: BigInt, a: BigInt, last_x_next: BigInt): Unit = {
    require(len >= 5)
    require(i >= 0 && i < len && i % 2 == 0)
    require(a >= 0 && a <= Pow2(len - 2) - 1)

    val xx = if(i==0) (a % 4) * 2 else if(i+1==len) a / Pow2(i - 1) else (a / Pow2(i - 1)) % Pow2(3)
    require(last_x_next == xx)
    i match {
      case BigInt(0) => {
        last_x_next                           ==:| lemma_last_x_next_i0(len, i, a, last_x_next, xx) |:
        (2 * a) / Pow2(i + 2 - 2) % Pow2(3) 
      }.qed
      case _ => {
        last_x_next                           ==:| lemma_last_x_next_i(len, i, a, last_x_next, xx) |:
        (2 * a / Pow2(i + 2 - 2)) % Pow2(3)
      }.qed
    }
  }.ensuring(_ => last_x_next == (2 * a / Pow2(i + 2 - 2)) % Pow2(3))


  @opaque  @library
  def lemma_last_x_aisi(len: BigInt, i: BigInt, a: BigInt, ais1: BigInt, x: BigInt, last_x: BigInt): Unit = {
    require(len >= 5)
    require(i >= 0 && i < len && i % 2 == 0)
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    require(i >= BigInt(2) && last_x == ((BigInt(2) * a) / Pow2(i - 2) % Pow2(3)) || i < BigInt(2) && last_x == BigInt(0))
    require(i < BigInt(2) && x == (a % 4) * 2 || i >= BigInt(2) && x == (a / Pow2(i - 1)) % Pow2(3))
    require(ais1 == x % BigInt(2))

    i match {
      case BigInt(0) => {
        last_x / Pow2(2) ==:| {i >= BigInt(2) && last_x == ((BigInt(2) * a) / Pow2(i - 2) % Pow2(3)) || i < BigInt(2) && last_x == BigInt(0)} |:
        BigInt(0)  ==:| trivial |:
        ais1 
      }.qed
      case _ => {   
        last_x / Pow2(2) ==:| {i >= BigInt(2) && last_x == ((BigInt(2) * a) / Pow2(i - 2) % Pow2(3)) || i < BigInt(2) && last_x == BigInt(0)} |:
        ((BigInt(2) * a) / Pow2(i - 2) % Pow2(3)) / Pow2(2)                                                   ==:| trivial |:
        (((BigInt(2) * a) / Pow2(i - 2)) % Pow2(3)) / Pow2(2)                                                 ==:| lemmaExtract_ai_a(i, a, len) |:
        ((BigInt(2) * a) / Pow2(i)) % BigInt(2)                                                               ==:| {BigInt(2) == Pow2(1)} |:   
        ((BigInt(2) * a) / Pow2(i)) % Pow2(1)                                                                 ==:| lemmaPow2ModMod(2 * a / Pow2(i), 3, 1) |:                                       
        ((BigInt(2) * a) / Pow2(i)) % Pow2(3) % Pow2(1)                                                       ==:| lemmaPow2div(i, a, len) |:
        (a / Pow2(i - 1)) % Pow2(3) % Pow2(1)                                                                 ==:| trivial |:
        x % Pow2(1)                                                                                           ==:| trivial |:      
        x % BigInt(2)                                                                                         ==:| trivial |:  
        ais1
      }.qed
    }
  }.ensuring(_ => last_x / Pow2(2) == ais1)
  
  @opaque  @library
  def lemma_ppSumNext_i0(i: BigInt, len: BigInt, pp_sum_next: BigInt, pp_sum: BigInt, pp: BigInt, weight: BigInt, k: BigInt, b: BigInt, ksum: BigInt, ksum_next: BigInt): Unit = {
    require(i == 0)
    require(len >= 5)
    require(pp_sum == BigInt(0))
    require(ksum == BigInt(0))
    require(weight >= 0)
    require(pp_sum_next == pp_sum + pp * Pow2(weight))
    require(pp * Pow2(weight) == Pow2(len + 3) + k * b)
    require(ksum_next * b == ksum * b + k * Pow2(i) * b)
    {
      pp_sum_next ==:| trivial |:
      pp_sum + pp * Pow2(weight) ==:| trivial |:
      Pow2(len + 3) + k * b      ==:| trivial |:
      Pow2(len + 3) * Pow2(i + 2 - 2) + ksum_next * b 
    }.qed
  }.ensuring(pp_sum_next ==  Pow2(len + 3) * Pow2(i + 2 - 2) + ksum_next * b)

  @opaque  @library
  def lemma_ppSumNext_in(i: BigInt, len: BigInt, pp_sum_next: BigInt, pp_sum: BigInt, pp: BigInt, weight: BigInt, k: BigInt, b: BigInt, ksum: BigInt, ksum_next: BigInt): Unit = {
    require(len >= 5)
    require(i == len - 1 || i == len - 2)
    require(pp_sum == Pow2(len + 3) * Pow2(i - 2) + ksum * b)
    require(weight >= 0)
    require(pp_sum_next == pp_sum + pp * Pow2(weight))
    require(pp * Pow2(weight) == Pow2(len + i + 1) + k * b * Pow2(i))
    require(ksum_next * b == ksum * b + k * Pow2(i) * b)
    {
      pp_sum_next ==:| trivial |:
      pp_sum + pp * Pow2(weight) ==:| trivial |:
      Pow2(len + 3) * Pow2(i - 2) + ksum * b + Pow2(len + i + 1) + k * b * Pow2(i) ==:| trivial |:
      Pow2(len + 3) * Pow2(i - 2) + Pow2(len + i + 1) + ksum_next * b              ==:| Pow2Mul(len + i + 1, len + 3, i - 2) |:
      Pow2(len + 3) * Pow2(i - 2) + Pow2(len + 3) * Pow2(i - 2) + ksum_next * b    ==:| trivial |:
      Pow2(len + 3) * Pow2(i - 1) + ksum_next * b   
    }.qed
  }.ensuring(pp_sum_next == Pow2(len + 3) * Pow2(i - 1) + ksum_next * b)

  @opaque  @library
  def lemma_ppSumNext_i(i: BigInt, len: BigInt, pp_sum_next: BigInt, pp_sum: BigInt, pp: BigInt, weight: BigInt, k: BigInt, b: BigInt, ksum: BigInt, ksum_next: BigInt): Unit = {
    require(len >= 5)
    require(BigInt(2) <= i && (i + 2 < len))
    require(pp_sum == Pow2(len + 3) * Pow2(i - 2) + ksum * b)
    require(weight >= 0)
    require(pp_sum_next == pp_sum + pp * Pow2(weight))
    require(pp * Pow2(weight) == Pow2(len + i + 1) * 3 + k * b * Pow2(i))
    require(ksum_next * b == ksum * b + k * Pow2(i) * b)
    {
        pp_sum_next ==:| trivial |:
        pp_sum + pp * Pow2(weight) ==:| trivial |:
        Pow2(len + 3) * Pow2(i - 2) + ksum * b + Pow2(len + i + 1) * 3 + k * b * Pow2(i) ==:| trivial |:
        Pow2(len + 3) * Pow2(i - 2) + Pow2(len + i + 1) * 3 + ksum_next * b              ==:| Pow2Mul(len + i + 1, len + 3, i - 2) |:
        Pow2(len + i + 1) + Pow2(len + i + 1) * 3 + ksum_next * b                        ==:| trivial |:
        Pow2(len + i + 1) * 4 + ksum_next * b                                            ==:| trivial |:
        Pow2(len + i + 3) + ksum_next * b                                                ==:| Pow2Mul(len + i + 3, len + 3, i) |:
        Pow2(len + 3) * Pow2(i) + ksum_next * b
    }.qed
  }.ensuring(pp_sum_next == Pow2(len + 3) * Pow2(i + 2 - 2) + ksum_next * b)

  @opaque @library
  def lemma_ksumNext(k: BigInt, ksum: BigInt, ksum_next: BigInt, b: BigInt, a: BigInt, x: BigInt, i: BigInt, len: BigInt): Unit = {
    require(len >= 5)
    require(i >= 0 && i < len && i % 2 == 0)
    val x = if(i==0) (a % 4) * 2 else if(i+1==len) a / Pow2(i - 1) else (a / Pow2(i - 1)) % Pow2(3)
    val kk = x match {
      case BigInt(1) => BigInt(1)
      case BigInt(2) => BigInt(1)
      case BigInt(3) => BigInt(2)
      case BigInt(4) => BigInt(0) - BigInt(2)
      case BigInt(5) => BigInt(0) - BigInt(1)
      case BigInt(6) => BigInt(0) - BigInt(1)
      case _ => BigInt(0)
    } 
    require(kk == k)
    require(ksum_next == ksum + k * Pow2(i))
    
    assert(ksum_next * b == ksum * b + k * Pow2(i) * b)
  }.ensuring(ksum_next * b == ksum * b + k * Pow2(i) * b)

  @opaque @library
  def lemma_ppsum(i: BigInt, len: BigInt, pp_sum: BigInt, pp: BigInt, weight: BigInt, k: BigInt, b: BigInt, ksum: BigInt): Unit = {
    require(len >= 5)
    require(i == 0 && i < len && i % 2 == 0)
    require(weight >= 0)
    // require(pp_sum == Pow2(len + 3) * Pow2(i - 2) + ksum * b)
    // require(pp * Pow2(weight) == Pow2(len + i + 1) * 3 + k * b * Pow2(i))
    // require(ksum * b == ksum * b)
    // assert(pp_sum + pp * Pow2(weight) == Pow2(len + 3) * Pow2(i - 2) + ksum * b + Pow2(len + i + 1) * 3 + k * b * Pow2(i))
  }.ensuring(_ => pp_sum == Pow2(len + 3) * Pow2(i - 2) + ksum * b)

  @opaque @library
  def lemma_asumUnsign_a(a: BigInt, i: BigInt, len: BigInt, asumUnsign: BigInt, asumUnsign_next: BigInt): Unit = {
    require(len >= 5)
    require(i >= 0 && i < len && i % 2 == 0)
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    require(a - (a / Pow2(i)) * Pow2(i) == asumUnsign)
    val x = if(i==0) (a % 4) * 2 else if(i+1==len) a / Pow2(i - 1) else (a / Pow2(i - 1)) % Pow2(3)
    require(asumUnsign_next == asumUnsign + Pow2(i) * (x / 2))
    i match {
      case BigInt(0) => {
        asumUnsign_next                                       ==:| trivial |:  
        asumUnsign + Pow2(i) * (x / 2)                        ==:| trivial |:
        asumUnsign + x / 2                                    ==:| trivial |:
        a - (a / Pow2(i)) * Pow2(i) + x / 2                   ==:| trivial |:
        a - a + x / 2                                         ==:| trivial |: 
        x / 2                                                 ==:| trivial |:
        (a % 4) * 2 / 2                                       ==:| trivial |:
        a - (a / 4) * 4                                       ==:| trivial |:
        a - (a / Pow2(2)) * Pow2(2)                           ==:| { i + 2 == 2 } |:
        a - (a / Pow2(i + 2)) * Pow2(i + 2)                      
      }.qed
      case _ => {
        asumUnsign_next                                       ==:| trivial |:
        asumUnsign + Pow2(i) * (x / 2)                        ==:| trivial |:
        a - (a / Pow2(i)) * Pow2(i) + Pow2(i) * (x / 2)       ==:| inductionProveAsumUnsign(i, len, a, x) |:
        a - (a / Pow2(i + 2)) * Pow2(i + 2)
      }.qed
    }
  }.ensuring(_ => asumUnsign_next == a - (a / Pow2(i + 2)) * Pow2(i + 2))
  
  @opaque @library
  def lemma_ppsum_a(a: BigInt, b: BigInt, i: BigInt, len: BigInt, pp_sum_next: BigInt, ksum_next: BigInt, asumUnsign_next: BigInt): Unit = {
    require(len >= 5)
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    require(b > 0 && b <= Pow2(len - 2) - 1)
    require(i == len - 1 || i == len - 2)
    require(pp_sum_next == Pow2(len + 3) * Pow2(i - 1) + ksum_next * b)
    val last_x_next = if(i==0) (a % 4) * 2 else if(i+1==len) a / Pow2(i - 1) else (a / Pow2(i - 1)) % Pow2(3)
    require(asumUnsign_next == a - (a / Pow2(i + 2)) * Pow2(i + 2))
    require(asumUnsign_next == ksum_next + (last_x_next / Pow2(2)) * Pow2(i + 2))
    assert(last_x_next / Pow2(2) == BigInt(0))
    {
      ksum_next       ==:| trivial |:
      asumUnsign_next ==:| trivial |:
      a
    }.qed
    {
      Pow2(len - 2) * Pow2(len - 2) ==:| Pow2Mul(2 * len - 4, len - 2, len - 2) |:
      Pow2(2 * len - 4)
    }.qed
    {
      a * b < Pow2(2 * len) because(
        a * b <= (Pow2(len - 2) - 1) * (Pow2(len - 2) - 1) &&
        (Pow2(len - 2) - 1) * (Pow2(len - 2) - 1) < Pow2(len - 2) * Pow2(len - 2) &&
        Pow2(len - 2) * Pow2(len - 2) == Pow2(2 * len - 4) 
      )
    }
    {
      pp_sum_next % Pow2(2 * len)                                   ==:| trivial |:
      (Pow2(len + 3) * Pow2(i - 1) + ksum_next * b) % Pow2(2 * len) ==:| Pow2Mul(len + i + 2, len + 3, i - 1) |:
      (Pow2(len + i + 2) + ksum_next * b) % Pow2(2 * len)           ==:| trivial |:
      (Pow2(len + i + 2) + a * b) % Pow2(2 * len)                   ==:| lemmaPow2Mod(len + i + 2, a * b, 2 * len)  |:
      a * b
    }.qed
  }.ensuring(_ => pp_sum_next % Pow2(2 * len) == a * b)
 
  def columnsWhile(i: BigInt, len: BigInt, last_x: BigInt, a: BigInt, b: BigInt, pp_sum: BigInt, 
    ksum: BigInt, asum: BigInt, asumSign: BigInt, asumUnsign: BigInt): (BigInt, BigInt, BigInt, BigInt) = {
    require(len >= 5)
    require(i >= 0 && i < len && i % 2 == 0)
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    require(b > 0 && b <= Pow2(len - 2) - 1)
    require(ksum == asum)
    require(asum == asumSign)
    require(a - (a / Pow2(i)) * Pow2(i) == asumUnsign)
    require(i >= BigInt(2) && last_x == ((BigInt(2) * a) / Pow2(i - 2) % Pow2(3)) || i < BigInt(2) && last_x == BigInt(0))
    require(asumUnsign == asumSign + (last_x / Pow2(2)) * Pow2(i))
    // val pp_sum_ksum_b = if (i < 2) 0 else Pow2(len + 3) * Pow2(i - 2) + ksum * b
    require(pp_sum == Pow2(len + 3) * Pow2neg(i - 2) + ksum * b)

    decreases(len - i)
    val x = if(i==0) (a % 4) * 2 else if(i+1==len) a / Pow2(i - 1) else (a / Pow2(i - 1)) % Pow2(3)
    val b_sext = b
    val bx2 = b * 2
    // val neg_b = Pow2(len + 1) - 1 - b
    // val neg_bx2 = Pow2(len + 1) - 2 * (1 + b)
    val neg_b = Pow2(len + 1) - BigInt(1) * b
    val neg_bx2 = Pow2(len + 1) - BigInt(2) * b

    val pp_temp = x match { 
      case BigInt(1) => b_sext
      case BigInt(2) => b_sext
      case BigInt(3) => bx2
      case BigInt(4) => neg_bx2
      case BigInt(5) => neg_b
      case BigInt(6) => neg_b
      case _ => BigInt(0)
    }
    val s = pp_temp / Pow2(len)
    assert(s == BigInt(0) || s == BigInt(1))

    // val t = last_x match {
    //   case BigInt(4) => BigInt(2)
    //   case BigInt(5) => BigInt(1)
    //   case BigInt(6) => BigInt(1)
    //   case _ => BigInt(0)
    // }
    val t = BigInt(0)
    // val t = 0.U(2.W)

    val last_x_next = x

    val (pp, weight) = i match {
      case BigInt(0) =>
        (((1 - s) * Pow2(len + 3) + s * Pow2(len + 2) + s * Pow2(len + 1) + pp_temp), BigInt(0))
      case n if (n==len-1) || (n==len-2) =>
        (((1 - s) * Pow2(len + 3) + pp_temp * 4 + t), i-2)
      case _ =>
        ((Pow2(len + 4) + (1 - s) * Pow2(len + 3) + pp_temp * 4 + t), i-2)
    }
    assert(weight >= 0)
    // for(j <- columns.indices){
    //   if(j >= weight && j < (weight + pp.getWidth)){
    //     columns(j) = columns(j) :+ pp(j-weight)
    //   }
    // }
    val pp_sum_next = pp_sum + pp * Pow2(weight)
    
    // prove ksum_next == asum_next
    val k = x match {
      case BigInt(1) => BigInt(1)
      case BigInt(2) => BigInt(1)
      case BigInt(3) => BigInt(2)
      case BigInt(4) => -BigInt(2)
      case BigInt(5) => -BigInt(1)
      case BigInt(6) => -BigInt(1)
      case _ => BigInt(0)
    } 

    val ksum_next = ksum + k * Pow2(i)

    // val k2i = k * Pow2(i)
    // assert(k2i * b == k * Pow2(i) * b)
    // assert(ksum_next * b == ksum * b + k * Pow2(i) * b)
    
    // prove pp_temp == 2^{n + 1} * s + k * b
    {
      pp_temp ==:| lemmaPPtempSkb(x, pp_temp, s, k, b, len) |:
      Pow2(len + 1) * s + k * b
    }.qed
    // // assert(pp_temp == Pow2(len + 1) * s + k * b)
    {
      i match {
        case BigInt(0) => 
          pp * Pow2(weight) ==:| lemma_pp_pow2weight_i0(len, b, pp, s, k, pp_temp, weight) |:
          Pow2(len + 3) + k * b 
        case n if (n==len-1) || (n==len-2) =>
          pp * Pow2(weight) ==:| lemma_pp_pow2weight_i_last(len, b, pp, s, k, pp_temp, i, weight) |:
          Pow2(len + i + 1) + k * b * Pow2(i)
        case _ =>  
          pp * Pow2(weight) ==:| lemma_pp_pow2weight_i(len, b, pp, s, k, pp_temp, i, weight) |:
          Pow2(len + i + 1) * 3 + k * b * Pow2(i)
      }
    }.qed
    {
      ksum_next * b ==:| trivial |:
      (ksum + k * Pow2(i)) * b ==:| trivial |:
      ksum * b + k * b * Pow2(i)
    }.qed
    // assert(ksum_next * b == ksum * b + k * Pow2(i) * b)

    // prove pp_sum_next == if i > 0 2^{n + 3} * 2^{i} + ksum_next * b 
    // {
    //   i match {
    //     case BigInt(0) => 
    //       pp_sum_next ==:| trivial |:
    //       pp_sum + pp * Pow2(weight) ==:| trivial |:
    //       Pow2(len + 3) + k * b      ==:| trivial |:
    //       Pow2(len + 3) * Pow2(i + 2 - 2) + ksum_next * b 
    //     case n if (n==len-1) || (n==len-2) =>
    //       pp_sum_next ==:| trivial |:
    //       pp_sum + pp * Pow2(weight) ==:| trivial |:
    //       Pow2(len + 3) * Pow2(i - 2) + ksum * b + Pow2(len + i + 1) + k * b * Pow2(i) ==:| trivial |:
    //       Pow2(len + 3) * Pow2(i - 2) + Pow2(len + i + 1) + ksum_next * b 
    //     case _ =>  
    //       pp_sum_next ==:| trivial |:
    //       pp_sum + pp * Pow2(weight) ==:| trivial |:
    //       Pow2(len + 3) * Pow2(i - 2) + ksum * b + Pow2(len + i + 1) * 3 + k * b * Pow2(i) ==:| trivial |:
    //       Pow2(len + 3) * Pow2(i - 2) + Pow2(len + i + 1 Pow2(len + 3) * Pow2(i - 2) + ksum * b) * 3 + ksum_next * b              ==:| Pow2Mul(len + i + 1, len + 3, i - 2) |:
    //       Pow2(len + i + 1) + Pow2(len + i + 1) * 3 + ksum_next * b                        ==:| trivial |:
    //       Pow2(len + i + 1) * 4 + ksum_next * b                                            ==:| trivial |:
    //       Pow2(len + i + 3) + ksum_next * b                                                ==:| Pow2Mul(len + i + 3, len + 3, i) |:
    //       Pow2(len + 3) * Pow2(i) + ksum_next * b
    //   }
    // }.qed
   
    {
      i match {
        case BigInt(0) =>
          pp_sum_next ==:| lemma_ppSumNext_i0(i, len, pp_sum_next, pp_sum, pp, weight, k, b, ksum, ksum_next) |:
          Pow2(len + 3) * Pow2(i + 2 - 2) + ksum_next * b 
        case last if (last == len - 1) || (last == len - 2) =>
          pp_sum_next ==:| lemma_ppSumNext_in(i, len, pp_sum_next, pp_sum, pp, weight, k, b, ksum, ksum_next) |:
          Pow2(len + 3) * Pow2(i - 1) + ksum_next * b
        case _ => 
          pp_sum_next ==:| lemma_ppSumNext_i(i, len, pp_sum_next, pp_sum, pp, weight, k, b, ksum, ksum_next) |:
          Pow2(len + 3) * Pow2(i + 2 - 2) + ksum_next * b
      }
    }.qed
    // {
    //   pp_sum_next ==:| lemma_ppsum(i + 2, len, pp_sum_next, pp, weight, k, b, ksum_next) |:
    //   Pow2(len + 3) * Pow2(i) + ksum_next * b      
    // }.qed
    
    // val ais1 = x % 2
    // val ai = (x / 2) % 2
    // val aia1 = x / Pow2(2)
    val aia1 = x / Pow2(2)
    val ai = (x - aia1 * Pow2(2)) / BigInt(2)
    val ais1 = x - aia1 * Pow2(2) - ai * BigInt(2)
    assert(x == aia1 * Pow2(2) + ai * BigInt(2) + ais1)
    
    val asum_next = asum + (ais1 + ai - BigInt(2) * aia1) * Pow2(i)
    {
      k ==:| lemma_ais1_ai_neg2aia1_k(x, ais1, ai, aia1, k) |:
      ais1 + ai - BigInt(2) * aia1
    }.qed

    assert(ais1 + ai - BigInt(2) * aia1 == k)
    assert(ksum_next == asum_next)

    // prove asum == asumSign
    // asum = \sum_{j=0}^{i} (a_{j-1} + a_{j} - 2a_{j+1}) * 2^j
    // asumSign = -2^{j+1} + \sum_{j=0}^{i} a_{j} * 2^j
    val asumSign_next = asumSign + ais1 * Pow2(i) + ai * Pow2(i) - aia1 * Pow2(i + 1) 
    assert(asum_next == asumSign_next)

    // assume asumUnsign == a(i-1, 0), prove asumUnsign_next == a(i+1, 0)
    //     then we can use asumUnsign == a(i-1, 0) == a mod 2^i
    //         to prove that asumUnsign == a when i + 2 >= len 
    // needs to prove a mod 2^i + ai * 2^i + ai+1 * 2^{i+1} = a mod 2^{i+2}
    val asumUnsign_next = asumUnsign + ai * Pow2(i) + aia1 * Pow2(i + 1)
    assert(x < Pow2(3))
    assert(ais1 < BigInt(2))
    assert(Pow2(2) == BigInt(2) * BigInt(2))
    assert(aia1 * Pow2(2) == aia1 * BigInt(2) * BigInt(2))
    {
      x / BigInt(2)                                                       ==:| trivial |: 
      (aia1 * Pow2(2) + ai * BigInt(2) + ais1) / BigInt(2)                ==:| trivial |:
      (aia1 * BigInt(2) * BigInt(2) + ai * BigInt(2) + ais1) / BigInt(2)  ==:| trivial |:
      ((aia1 * BigInt(2) + ai) * BigInt(2) + ais1) / BigInt(2)            ==:| trivial |:
      aia1 * BigInt(2) + ai                                              
    }.qed
    assert(x / BigInt(2) == BigInt(2) * aia1 + ai)
    // assert(asumUnsign_next == asumUnsign + Pow2(i) * (x / 2))
    // i match {
    //   case BigInt(0) => {
    //     asumUnsign_next                                       ==:| trivial |:  
    //     asumUnsign + Pow2(i) * (x / 2)                        ==:| trivial |:
    //     asumUnsign + x / 2                                    ==:| trivial |:
    //     a - (a / Pow2(i)) * Pow2(i) + x / 2                   ==:| trivial |:
    //     a - a + x / 2                                         ==:| trivial |: 
    //     x / 2                                                 ==:| trivial |:
    //     (a % 4) * 2 / 2                                       ==:| trivial |:
    //     a - (a / 4) * 4                                       ==:| trivial |:
    //     a - (a / Pow2(2)) * Pow2(2)                           ==:| { i + 2 == 2 } |:
    //     a - (a / Pow2(i + 2)) * Pow2(i + 2)                      
    //   }.qed
    //   case _ => {
    //     asumUnsign_next                                       ==:| trivial |:
    //     asumUnsign + Pow2(i) * (x / 2)                        ==:| trivial |:
    //     a - (a / Pow2(i)) * Pow2(i) + Pow2(i) * (x / 2)       ==:| inductionProveAsumUnsign(i, len, a, x) |:
    //     a - (a / Pow2(i + 2)) * Pow2(i + 2)
    //   }.qed
    // }
    // assert(asumUnsign_next == a - (a / Pow2(i + 2)) * Pow2(i + 2))
    {
      asumUnsign_next ==:| lemma_asumUnsign_a(a, i, len, asumUnsign, asumUnsign_next) |:
      a - (a / Pow2(i + 2)) * Pow2(i + 2)
    }.qed

    // assume asumUnsign == asumSign + a_{i - 1} * 2^i, 
    //     prove asumUnsign_next == asumSign_next + a_{i + 1} * 2^{i + 2}
    // first, prove last_x / 4 = a_{i - 1}
    // i match {
    //   case BigInt(0) => {
    //     last_x_next                           ==:| lemma_last_x_next_i0(len, i, a, last_x_next, x) |:
    //     (2 * a) / Pow2(i + 2 - 2) % Pow2(3) 
    //   }.qed
    //   case _ => {
    //     assert(i >= BigInt(2))
    //     last_x_next                           ==:| lemma_last_x_next(len, i, a, last_x_next, x) |:
    //     (2 * a / Pow2(i + 2 - 2)) % Pow2(3)
    //   }.qed
    // }
    {
      last_x_next ==:| lemma_last_x_next(len, i, a, last_x_next) |:
      (2 * a / Pow2(i + 2 - 2)) % Pow2(3)
    }.qed
    val i_next = i + 2
    // assert(last_x_next == (BigInt(2) * a) / Pow2(i_next - 2) % Pow2(3))

    {
      last_x / Pow2(2) ==:| lemma_last_x_aisi(len, i, a, ais1, x, last_x) |:
      ais1
    }.qed

    // assume asumUnsign == asumSign + a_{i - 1} * 2^i,
    //     prove asumUnsign_next == asumSign_next + a_{i + 1} * 2^{i + 2}   
    // here we already proved that last_x / 4 = a_{i - 1}, and last_x_next / 4 = a_{i + 1}, 
    //     thus we can use them to represent a_{i - 1} and a_{i + 1}.
    assert(last_x / Pow2(2) == ais1)
    assert(last_x_next / Pow2(2) == aia1)
    {
      aia1 * Pow2(i + 2) ==:| {Pow2(i + 2) == Pow2(i + 1) * BigInt(2)} |:
      aia1 * Pow2(i + 1) * BigInt(2)
    }.qed
    {
      asumSign_next + (last_x_next / Pow2(2)) * Pow2(i + 2)                                           ==:| trivial |:
      asumSign_next + aia1 * Pow2(i + 2)                                                              ==:| trivial |:
      asumSign + ais1 * Pow2(i) + ai * Pow2(i) - aia1 * Pow2(i + 1) + aia1 * Pow2(i + 2)              ==:| trivial |:
      asumSign + ais1 * Pow2(i) + ai * Pow2(i) - aia1 * Pow2(i + 1) + aia1 * Pow2(i + 1) * BigInt(2)  ==:| trivial |:
      asumSign + ais1 * Pow2(i) + ai * Pow2(i) + aia1 * Pow2(i + 1)                                   ==:| trivial |:
      asumUnsign - (last_x / Pow2(2)) * Pow2(i) + ais1 * Pow2(i) + ai * Pow2(i) + aia1 * Pow2(i + 1)  ==:| trivial |:
      asumUnsign - ais1 * Pow2(i) + ais1 * Pow2(i) + ai * Pow2(i) + aia1 * Pow2(i + 1)                ==:| trivial |:
      asumUnsign + ai * Pow2(i) + aia1 * Pow2(i + 1)                                                  ==:| trivial |:
      asumUnsign_next
    }.qed

    // up to now, we proved that asumUnsign_next == ksum_next + (last_x_next / Pow2(2)) * Pow2(i + 2)
    //     where last_x_next / 4 == x / 4 == a_{i + 1}, and a_{i + 1} == 0 when i + 2 >= len
    //         thus a == asumUnsign_next == ksum_next when i + 2 >= len
    assert(asumUnsign_next == ksum_next + (last_x_next / Pow2(2)) * Pow2(i + 2))

    if(i + 2 < len){
      columnsWhile(i_next, len, last_x_next, a, b, pp_sum_next, ksum_next, asum_next, asumSign_next, asumUnsign_next)
    }
    else {
      // assert(i + 2 >= len)
      assert(i == len - 1 || i == len - 2)
      assert(a / Pow2(i + 2) == 0)
      // assert(asumUnsign_next == a)
      {
        pp_sum_next % Pow2(2 * len) ==:| lemma_ppsum_a(a, b, i, len, pp_sum_next, ksum_next, asumUnsign_next) |:
        a * b
      }.qed
     
      (i + 2, a, b, pp_sum_next % Pow2(2 * len))
    }
  } ensuring(res => res._4 == res._2 * res._3)

  // def addOneColumn(col: List[Bool], cin: List[Bool]): (List[Bool], List[Bool], List[Bool]) = {
  //   var sum   = List[Bool]()
  //   var cout1 = List[Bool]()
  //   var cout2 = List[Bool]()

  //   col.size match {
  //     case 1 => {
  //       sum = col ++ cin
  //     }
  //     case 2 => {
  //       val c22 = C22()

  //       var c22_io_in   = col.map(_.asUInt)
  //       val c22_outputs = c22.trans(CarrySaveAdderMToN_Inputs(c22_io_in))
  //       val c22_io_out  = c22_outputs.io_out

  //       sum = c22_io_out(0).asBool :: cin
  //       cout2 = List(c22_io_out(1).asBool)
  //     }
  //     case 3 => {
  //       val c32 = C32()

  //       var c32_io_in   = col.map(_.asUInt)
  //       val c32_outputs = c32.trans(CarrySaveAdderMToN_Inputs(c32_io_in))
  //       val c32_io_out  = c32_outputs.io_out

  //       sum = c32_io_out(0).asBool :: cin
  //       cout2 = List(c32_io_out(1).asBool)
  //     }
  //     case 4 => {
  //       val c53 = C53()

  //       var c53_io_in   = col.take(4).map(_.asUInt) :+ (if (cin.nonEmpty) cin.head.asUInt else Lit(0).U)
  //       val c53_outputs = c53.trans(CarrySaveAdderMToN_Inputs(c53_io_in))
  //       val c53_io_out  = c53_outputs.io_out

  //       sum = List(c53_io_out(0).asBool) ++ (if (cin.nonEmpty) cin.drop(1) else Nil[Bool]())
  //       cout1 = List(c53_io_out(1).asBool)
  //       cout2 = List(c53_io_out(2).asBool)
  //     }
  //     case _ => {
  //       val cin_1               = if (cin.nonEmpty) List(cin.head) else Nil[Bool]()
  //       val cin_2               = if (cin.nonEmpty) cin.drop(1) else Nil[Bool]()
  //       val (s_1, c_1_1, c_1_2) = addOneColumn(col take 4, cin_1)
  //       val (s_2, c_2_1, c_2_2) = addOneColumn(col drop 4, cin_2)
  //       sum = s_1 ++ s_2
  //       cout1 = c_1_1 ++ c_2_1
  //       cout2 = c_1_2 ++ c_2_2
  //     }
  //   }
  //   (sum, cout1, cout2)
  // }
  @library
  def addAll(cols: List[List[BigInt]], depth: BigInt, len: BigInt): (BigInt, BigInt) = {
    // if (max(cols.map(_.size)) <= 2) {
    //   val sum = Cat(cols.map(_(0)).reverse.map(_.asUInt))
    //   var k = BigInt(0)
    //   while (cols(k).size == 1) k = k + 1
    //   val carry = Cat(cols.drop(k).map(_(1)).reverse.map(_.asUInt))
    //   (sum, Cat(carry, Lit(0, k).U))
    // } else {
    //   var columns_next = List.fill(2 * len)(List[Bool]())
    //   var cout1, cout2 = List[Bool]()

    //   columns_next = cols
    //     .foldLeft((cout1, cout2, List.empty[List[Bool]])) { case ((cout1, cout2, res), cols_i) =>
    //       val (s, c1, c2)    = addOneColumn(cols_i, cout1)
    //       val columns_next_i = s ++ cout2
    //       (c1, c2, res :+ columns_next_i)
    //     }
    //     ._3

    //   val toNextLayer = columns_next

    //   addAll(toNextLayer, depth + 1, len)
    // }
    val sum = BigInt(0)
    val carry = BigInt(0)
    (sum, carry)
  }

  def ArrayMulDataModule(len: BigInt, a: BigInt, b: BigInt, i: BigInt): BigInt = {
    require(len >= 5)
    require(a >= 0 && a <= Pow2(len - 2) - 1)
    require(b > 0 && b <= Pow2(len - 2) - 1)

    // val columns: Array[Seq[Bool]] = Array.fill(2*len)(Seq())
    // val columns: List[List[BigInt]] = List.fill(2*len)(List())

    val last_x = BigInt(0)

    val t: (BigInt, BigInt, BigInt, BigInt) = columnsWhile(BigInt(0), len, last_x, a, b, BigInt(0), BigInt(0), BigInt(0), BigInt(0), BigInt(0))
    val (sum, carry) = (BigInt(0), BigInt(0)) // addAll(cols = t._5, depth = 0, len)

    val result = sum + carry
    result
  } // ensuring(res => )
}