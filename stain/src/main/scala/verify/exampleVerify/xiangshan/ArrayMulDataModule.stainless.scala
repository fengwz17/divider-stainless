package exampleVerify.xiangshan

import stainless.lang._
import stainless.collection._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

import libraryUInt._

case class ArrayMulDataModuleInputs(
    io_a: UInt,
    io_b: UInt,
    io_regEnables: List[Bool]
)
case class ArrayMulDataModuleOutputs(io_result: UInt)
case class ArrayMulDataModuleRegs()

case class ArrayMulDataModule(len: BigInt) {
  def inputsRequire(inputs: ArrayMulDataModuleInputs): Boolean = inputs match {
    case ArrayMulDataModuleInputs(io_a, io_b, io_regEnables) =>
      io_a.width == len &&
      io_b.width == len &&
      io_regEnables.length == 2
  }
  def outputsRequire(outputs: ArrayMulDataModuleOutputs): Boolean = outputs match {
    case ArrayMulDataModuleOutputs(io_result) =>
      io_result.width == (2 * len)
  }
  def regsRequire(regs: ArrayMulDataModuleRegs): Boolean = regs match {
    case ArrayMulDataModuleRegs() =>
      true
  }

  // lemmas for booth encoding
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

  // lemmas for compression
  @library
  def lemma_pp_toZ(len: BigInt, pp: BigInt, pp_width: BigInt, j: BigInt, weight: BigInt, getIndexBigIntInput: BigInt): Unit = {
    require(len >= 5)
    require(pp_width >= 0 && pp_width <= len + 5)
    require(pp >= 0 && pp < Pow2(pp_width) && pp < Pow2(2 * len))
    require(j >= 0 && j <= 2 * len)
    require(weight >= 0 && weight <= len - 3)
    val getIndexBigInt = j match {
      case jj if (jj >= weight && jj < weight + pp_width) => getIndex(pp, j - weight)
      case _ => BigInt(0)
    }
    require(getIndexBigIntInput == getIndexBigInt)
    {
      j match {
        case jj if (jj >= weight && jj < weight + pp_width) => 
          {
            pp * Pow2(weight) % Pow2(j) + getIndexBigInt * Pow2(j) ==:| trivial |:
            pp * Pow2(weight) % Pow2(j) + getIndex(pp, j - weight) * Pow2(j) ==:| trivial |:
            pp * Pow2(weight) % Pow2(j) + (pp / Pow2(j - weight) % 2) * Pow2(j) ==:| lemmaPow2divMul(j, weight, pp, len) |:
            pp * Pow2(weight) % Pow2(j) + ((pp * Pow2(weight) / Pow2(j)) % 2) * Pow2(j) ==:| trivial |:
            pp * Pow2(weight) - pp * Pow2(weight) / Pow2(j) * Pow2(j) + (pp * Pow2(weight) / Pow2(j) - (pp * Pow2(weight) / Pow2(j)) / 2 * 2) * Pow2(j) ==:| trivial |:
            pp * Pow2(weight) - pp * Pow2(weight) / Pow2(j) * Pow2(j) + pp * Pow2(weight) / Pow2(j) * Pow2(j) - (pp * Pow2(weight) / Pow2(j)) / 2 * 2 * Pow2(j) ==:| trivial |:
            pp * Pow2(weight) - (pp * Pow2(weight) / Pow2(j)) / 2 * 2 * Pow2(j) ==:| trivial |:
            pp * Pow2(weight) - (pp * Pow2(weight) / Pow2(j)) / 2 * Pow2(j + 1) ==:| trivial |:
            pp * Pow2(weight) - (pp * Pow2(weight) / Pow2(j)) / Pow2(1) * Pow2(j + 1) ==:| lemmaPow2DivAdd(pp * Pow2(weight), j, 1) |:
            pp * Pow2(weight) - (pp * Pow2(weight) / Pow2(j + 1)) * Pow2(j + 1) ==:| trivial |:
            pp * Pow2(weight) % Pow2(j + 1)
          }.qed
        case jl if (jl < weight) =>
          {
            pp * Pow2(weight) % Pow2(j) + getIndexBigInt * Pow2(j) ==:| trivial |:
            pp * Pow2(weight) % Pow2(j) ==:| lemma_Pow2ModZero(pp, weight, j) |:
            BigInt(0)                   ==:| lemma_Pow2ModZero(pp, weight, j + 1) |:
            pp * Pow2(weight) % Pow2(j + 1)
          }.qed
        case jg if (jg >= weight + pp_width) => 
          {
            lemmaPow2lt(j, weight + pp_width)
            assert(Pow2(j) >= Pow2(weight + pp_width))
            {
              Pow2(pp_width) * Pow2(weight) ==:| Pow2Mul(pp_width + weight, pp_width, weight) |:
              Pow2(weight + pp_width)
            }.qed
            assert(pp * Pow2(weight) < Pow2(weight + pp_width))
            assert(pp * Pow2(weight) < Pow2(j))
            assert(pp * Pow2(weight) < Pow2(j + 1))
            pp * Pow2(weight) % Pow2(j) + getIndexBigInt * Pow2(j) ==:| trivial |:
            pp * Pow2(weight) % Pow2(j) ==:| lemma_Pow2Modilj(pp, weight, j) |:
            pp * Pow2(weight)           ==:| lemma_Pow2Modilj(pp, weight, j + 1) |:
            pp * Pow2(weight) % Pow2(j + 1)
          }.qed
        }
    }
  }.ensuring(pp * Pow2(weight) % Pow2(j) + getIndexBigIntInput * Pow2(j) == pp * Pow2(weight) % Pow2(j + 1))
  

  @library
  def c22(input: List[BigInt]): List[BigInt] = {
    require(input.size == 2)
    require(input(0) == 1 || input(0) == 0)
    require(input(1) == 1 || input(1) == 0)
    val (aInt, bInt) = (input(0), input(1))
    val a = if (aInt == 1) true else false
    val b = if (bInt == 1) true else false
    val sum = a ^ b
    val cout = a & b
    val sumInt = if (sum == true) BigInt(1) else BigInt(0)
    val coutInt = if (cout == true) BigInt(1) else BigInt(0)
    val res = List(sumInt, coutInt)
    res
  } ensuring(res => input(0) + input(1) == 2 * res(1) + res(0))

  @library
  def c32(input: List[BigInt]): List[BigInt] = {
    require(input.size == 3)
    require(input(0) == 1 || input(0) == 0)
    require(input(1) == 1 || input(1) == 0)
    require(input(2) == 1 || input(2) == 0)
    
    val (aInt, bInt, cinInt) = (input(0), input(1), input(2))
    val a = if (aInt == 1) true else false
    val b = if (bInt == 1) true else false
    val cin = if (cinInt == 1) true else false

    val a_xor_b     = a ^ b
    val a_and_b     = a & b
    val sum         = a_xor_b ^ cin
    val cout        = a_and_b | (a_xor_b & cin)

    val sumInt = if (sum == true) BigInt(1) else BigInt(0)
    val coutInt = if (cout == true) BigInt(1) else BigInt(0)
    val res = List(sumInt, coutInt)
    res
  } ensuring(res => input(0) + input(1) + input(2) == 2 * res(1) + res(0))
  
  @library
  def c53(input: List[BigInt]): List[BigInt] = {
    require(input.size == 5)
    require(input(0) == 1 || input(0) == 0)
    require(input(1) == 1 || input(1) == 0)
    require(input(2) == 1 || input(2) == 0)
    require(input(3) == 1 || input(3) == 0)
    require(input(4) == 1 || input(4) == 0)
    
    val FA_0_in = List(input(0), input(1), input(2))
    val FA_0_out = c32(FA_0_in)
    val FA_1_in = List(FA_0_out(0), input(3), input(4))
    val FA_1_out = c32(FA_1_in)
    val out = List(FA_1_out(0), FA_0_out(1), FA_1_out(1))
    out
  } ensuring(res => input(0) + input(1) + input(2) + input(3) + input(4) == 2 * res(2) + 2 * res(1) + res(0))

   @ignore
  // prove a specific case that the List matrix size is 2 * (2 * len)
  def lemma_toZ_equalto_Sum_row2(l: List[List[Boolean]]): Unit = {
  }

  // inner function lifting
    @ignore
  def ppsumColumnsWhile(i: BigInt, len: BigInt, last_x: BigInt, a: BigInt, b: BigInt, pp_sum: BigInt, 
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
   
    {
      asumUnsign_next ==:| lemma_asumUnsign_a(a, i, len, asumUnsign, asumUnsign_next) |:
      a - (a / Pow2(i + 2)) * Pow2(i + 2)
    }.qed

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
      ppsumColumnsWhile(i_next, len, last_x_next, a, b, pp_sum_next, ksum_next, asum_next, asumSign_next, asumUnsign_next)
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

  @library
  def columnsWhile(len: BigInt, j: BigInt, weight: BigInt, pp: BigInt, pp_width: BigInt, columns: List[List[Boolean]], newColumns: List[List[Boolean]], 
    toZ_columns: BigInt, toZ_newColumns: BigInt): List[List[Boolean]] = {
    require(len >= 5)
    require(j >= 0 && j < 2 * len)
    require(weight >= 0 && weight <= len - 3)
    require(pp_width >= 0 && pp_width <= len + 5)
    require(pp >= 0 && pp < Pow2(pp_width) && pp < Pow2(2 * len))
    require(columns.size == 2 * len - j)
    require(newColumns.size == j)
    require(toZ_columns >= 0)
    require(toZ_newColumns >= 0)
    require(toZ_newColumns == toZ_columns + pp * Pow2(weight) % Pow2(j))

    decreases(2 * len - j)
    
    val newColumns_last_next = if(j >= weight && j < weight + pp_width) {
      val getIndexBool = if (getIndex(pp, j - weight) == 1) true else false
      getIndexBool :: columns.head
    }
    else {
      columns.head
    }
    val newColumns_next = newColumns :+ newColumns_last_next

    val j_next = j + 1
    val columns_next = columns.tail
    val toZ_columns_next = toZ_columns + Sum(columns.head) * Pow2(j)
    val toZ_newColumns_next = toZ_newColumns + Sum(newColumns_last_next) * Pow2(j)

    // prove toZ_newColumns_next == toZ_columns_next + pp * Pow2(weight) % Pow2(j + 1)
    val getIndexBigInt = j match {
      case n if (n >= weight && n < weight + pp_width) => getIndex(pp, j - weight)
      case _ => BigInt(0)
    }
    assert(Sum(newColumns_last_next) == Sum(columns.head) + getIndexBigInt)

    {
      toZ_newColumns_next ==:| trivial |:
      toZ_newColumns + Sum(newColumns_last_next) * Pow2(j) ==:| trivial |:
      toZ_columns + pp * Pow2(weight) % Pow2(j) + Sum(newColumns_last_next) * Pow2(j) ==:| trivial |:
      toZ_columns + pp * Pow2(weight) % Pow2(j) + (Sum(columns.head) + getIndexBigInt) * Pow2(j) ==:| trivial |:
      toZ_columns + pp * Pow2(weight) % Pow2(j) + Sum(columns.head) * Pow2(j) + getIndexBigInt * Pow2(j) ==:| trivial |:
      toZ_columns + Sum(columns.head) * Pow2(j) + pp * Pow2(weight) % Pow2(j) + getIndexBigInt * Pow2(j) ==:| trivial |:
      toZ_columns_next + pp * Pow2(weight) % Pow2(j) + getIndexBigInt * Pow2(j)                          ==:| lemma_pp_toZ(len, pp, pp_width, j, weight, getIndexBigInt) |:
      toZ_columns_next + pp * Pow2(weight) % Pow2(j + 1)
    }.qed

    if (j_next < 2 * len) {
      columnsWhile(len, j_next, weight, pp, pp_width, columns_next, newColumns_next, toZ_columns_next, toZ_newColumns_next)
    }
    else {
      assert(j + 1 == 2 * len)
      assert(toZ_newColumns_next == toZ_columns_next + pp * Pow2(weight) % Pow2(2 * len))
      newColumns_next
    }
  } ensuring(res => res.size == 2 * len)

  @library
  def rowWhile(l: List[List[Boolean]], len: BigInt, i: BigInt, toZ_current: BigInt, row_0: List[BigInt], row_1: List[BigInt]): (BigInt, List[BigInt], List[BigInt]) = {   
    require(l.size == 2 * len - i)
    require(0 <= i && i <= 2 * len - 1)
    require(l.forall(_.size <= 2))
    require(row_0.size == i)
    require(row_1.size == i)
    require(toZ_current >= BigInt(0))
    require(toZ_current == toZ(row_0) + toZ(row_1))
    // val current_list_i = l.head
    // require(current_list_i.size == BigInt(2))
    // require(l.tail.head != Nil())
    // require(l.tail.head.size == BigInt(2))
    decreases(2 * len - i)
    val current_list_i = l.head

    // list = {true :: Nil} true false
    val i_size = current_list_i.size
    val (current_list_i_0, current_list_i_1) = i_size match {
      case BigInt(0) => (false, false)
      case BigInt(1) => (current_list_i.head, false)
      case BigInt(2) => (current_list_i.head, current_list_i.tail.head)
    }
    val toZ_next = toZ_current + (asBigInt(current_list_i_0) + asBigInt(current_list_i_1)) * Pow2(i)
    val row_0_next = row_0 :+ asBigInt(current_list_i_0)
    val row_1_next = row_1 :+ asBigInt(current_list_i_1)
    // val row_0_BigInt = row_0.map(asBigInt(_))
    // val row_0_next_BigInt = row_0_next.map(asBigInt(_))
    // assert(row_0_next_BigInt == row_0_BigInt :+ asBigInt(current_list_i_0))
    // assert(toZ(row_0.map(asBigInt(_))) + asBigInt(current_list_i_0) * Pow2(i) == toZ(row_0_next.map(asBigInt(_))))
    lemma_toZ_append(row_0_next, row_0, asBigInt(current_list_i_0))
    lemma_toZ_append(row_1_next, row_1, asBigInt(current_list_i_1))
    assert(toZ(row_0_next) == toZ(row_0) + Pow2(i) * asBigInt(current_list_i_0))
    assert(toZ(row_1_next) == toZ(row_1) + Pow2(i) * asBigInt(current_list_i_1))
    assert(toZ_next == toZ(row_0_next) + toZ(row_1_next))
    // {
    //   toZ(row_0_next.map(asBigInt(_))) ==:|  |:
    //   toZ(row_0.map(asBigInt(_))) + asBigInt(current_list_i_0) * Pow2(i) == toZ(row_0_next.map(asBigInt(_)))
    // }.qed

    // Cons[List[Boolean]](Cons[Boolean](false, Cons[Boolean](false, Nil[Boolean]())), Cons[List[Boolean]](Nil[Boolean](), Nil[List[Boolean]]()))
    // false :: false :: Nil()
    // Nil() :: Nil[List[Boolean]]()

    if(i + 1 <= 2 * len - 1) {
      rowWhile(l.tail, len, i + 1, toZ_next, row_0_next, row_1_next)
    }
    else {
      assert(i == 2 * len - 1)
      (toZ_next, row_0_next, row_1_next)
    }
  } ensuring(res => res._1 == toZ(res._2) + toZ(res._3))

  // x x x x
  // x   x
  // 从size为2的最低位开始，一直到最高位，size == 2
  @library
  def addAllWhile(len: BigInt, i: BigInt, cols: List[List[Boolean]], columns_update: List[List[Boolean]], 
    cout1: List[Boolean], cout2: List[Boolean], Inv: BigInt): (List[List[Boolean]], List[Boolean], List[Boolean]) = {
    require(len >= 5)
    require(i >= 0 && i < 2 * len)
    // require(cols != Nil[List[Boolean]]())
    require(cols.size == 2 * len - i)
    require(cols.head != Nil())
    // require(columns_next != Nil[List[Boolean]]())
    // require(columns_next.size == 2 * len - i)
    require(columns_update.size == i)
    require(toZ(cols.map(Sum(_))) * Pow2(i) + Sum(cout1) * Pow2(i) + Sum(cout2) * Pow2(i) + toZ(columns_update.map(Sum(_))) == Inv)

    decreases(2 * len - i)

    // val cols_head = cols.head
    val (s, c1, c2) = addOneColumn(cols.head, cout1)

    assert(Sum(s) + 2 * Sum(c1) + 2 * Sum(c2) == Sum(cols.head) + Sum(cout1))

    val columns_next_i = s ++ cout2
    val columns_update_next = columns_update :+ columns_next_i

    {
      Sum(cols.head) + Sum(cout1) + Sum(cout2)          ==:| trivial |:
      Sum(s) + 2 * Sum(c1) + 2 * Sum(c2) + Sum(cout2)   ==:| trivial |:
      Sum(s) + Sum(cout2) + 2 * Sum(c1) + 2 * Sum(c2)   ==:| lemma_Sum_take(columns_next_i, s, cout2) |:
      Sum(columns_next_i) + 2 * Sum(c1) + 2 * Sum(c2)
    }.qed

    // proof needs to be checked
    assert(toZ(cols.map(Sum(_))) == toZ(cols.tail.map(Sum(_))) * 2 + Sum(cols.head))
    assert(toZ(columns_update_next.map(Sum(_))) == Sum(columns_next_i) * Pow2(i) + toZ(columns_update.map(Sum(_))))
    
    {
      toZ(cols.map(Sum(_))) * Pow2(i) + Sum(cout1) * Pow2(i) + Sum(cout2) * Pow2(i) + toZ(columns_update.map(Sum(_))) ==:| trivial |:
      (toZ(cols.tail.map(Sum(_))) * 2 + Sum(cols.head) + Sum(cout1) + Sum(cout2)) * Pow2(i) + toZ(columns_update.map(Sum(_))) ==:| trivial |:
      toZ(cols.tail.map(Sum)) * Pow2(i + 1) + (Sum(columns_next_i) + 2 * Sum(c1) + 2 * Sum(c2)) * Pow2(i) + toZ(columns_update.map(Sum(_))) ==:| trivial |:
      toZ(cols.tail.map(Sum)) * Pow2(i + 1) + Sum(columns_next_i) * Pow2(i) + Sum(c1) * Pow2(i + 1) + Sum(c2) * Pow2(i + 1) + toZ(columns_update.map(Sum(_))) ==:| trivial |:
      toZ(cols.tail.map(Sum)) * Pow2(i + 1) + toZ(columns_update_next.map(Sum(_))) + Sum(c1) * Pow2(i + 1) + Sum(c2) * Pow2(i + 1)
    }.qed

    if (i + 1 < 2 * len) {
      assert(cols.size >= 2)
      lemmaListTailHead(cols)
      addAllWhile(len, i + 1, cols.tail, columns_update_next, c1, c2, Inv)
    } else {
      (columns_update_next, c1, c2)
    }
  }.ensuring(res => toZ(res._1.map(Sum(_))) + Sum(res._2) * Pow2(2 * len) + Sum(res._3) * Pow2(2 * len) == Inv && res._1.size == 2 * len && res._1 != Nil())

  def trans(inputs: ArrayMulDataModuleInputs, regs: ArrayMulDataModuleRegs): (ArrayMulDataModuleOutputs, ArrayMulDataModuleRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_result = UInt.empty((2 * len))

    // body
    def signExt(a: UInt, len: BigInt): UInt = {
      val aLen = a.width
      val signBit = a((aLen - 1))
      if ((aLen >= len)) a((len - 1), 0) else Cat(Fill((len - aLen), signBit), a)
    }
    val (a, b) = (inputs.io_a, inputs.io_b)
    var b_sext = UInt.empty((len + 1))
    var bx2 = UInt.empty((len + 1))
    var neg_b = UInt.empty((len + 1))
    var neg_bx2 = UInt.empty((len + 1))
    b_sext = b_sext := signExt(b, (len + 1))
    bx2 = bx2 := (b_sext << 1)
    neg_b = neg_b := ~b_sext.asUInt
    neg_bx2 = neg_bx2 := (neg_b << 1)

    assert(b_sext.value == b.value)
    assert(bx2.value == b.value * 2)
    // val neg_b = Pow2(len + 1) - 1 - b
    // val neg_bx2 = Pow2(len + 1) - 2 * (1 + b)
    assert(neg_b.value == Pow2(len + 1) - BigInt(1) * b.value)
    assert(neg_bx2.value == Pow2(len + 1) - BigInt(2) * b.value)

    val columns = List.fill((2 * len))(List())
    var last_x = Lit(0, 3).U

    // foreach function needs to be rewritten as a recursive function
    Range(0, len, 2).foreach((i: BigInt) => {
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

      val x = if ((i == 0)) Cat(a(1, 0), Lit(0, 1).U) else if (((i + 1) == len)) signExt(a(i, (i - 1)), 3) else a((i + 1), (i - 1))
      val pp_temp = MuxLookup(x, Lit(0).U, List((Lit(1).U -> b_sext), (Lit(2).U -> b_sext), (Lit(3).U -> bx2), (Lit(4).U -> neg_bx2), (Lit(5).U -> neg_b), (Lit(6).U -> neg_b)))
      val s = pp_temp(len)
      val t = MuxLookup(last_x, Lit(0, 2).U, List((Lit(4).U -> Lit(2, 2).U), (Lit(5).U -> Lit(1, 2).U), (Lit(6).U -> Lit(1, 2).U)))
      last_x = x
      val (pp, weight) = if ((i == 0)) (Cat(List(~s, s, s, pp_temp)), 0) else if (((i == (len - 1)) || (i == (len - 1)))) (Cat(List(~s, pp_temp, t)), (i - 2)) else (Cat(List(Lit(1, 1).U, ~s, pp_temp, t)), (i - 2))
      
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
      
      {
        asumUnsign_next ==:| lemma_asumUnsign_a(a, i, len, asumUnsign, asumUnsign_next) |:
        a - (a / Pow2(i + 2)) * Pow2(i + 2)
      }.qed

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
      
      // needs to be lifting
      (0 until columns.length).foreach((j: BigInt) => if (((j >= weight) && (j < (weight + pp.width)))) columns = columns.updated(j, (columns(j) :+ pp((j - weight)))))
      val columns_next: List[List[Boolean]] = columnsWhile(len, j, weight, pp, pp_width, columns, newColumns, BigInt(0), BigInt(0))    
    })ensuring(res => res._4 == res._2 * res._3)


    def addOneColumn(col: List[Bool], cin: List[Bool]): (List[Bool], List[Bool], List[Bool]) = {
      val sum = List()
      val cout1 = List()
      val cout2 = List()
      if ((col.size == 1)) sum = (col ++ cin) else if ((col.size == 2)) {
        val c22 = example.xiangshan.C22()
        inputs.c22_io_in = inputs.c22_io_in := col
        sum = {
          val rassoc$1 = c22_io_out(0).asBool
          (rassoc$1 +: cin)
        }
        cout2 = List(c22_io_out(1).asBool)
      } else if ((col.size == 3)) {
        val c32 = example.xiangshan.C32()
        inputs.c32_io_in = inputs.c32_io_in := col
        sum = {
          val rassoc$2 = c32_io_out(0).asBool
          (rassoc$2 +: cin)
        }
        cout2 = List(c32_io_out(1).asBool)
      } else if ((col.size == 4)) {
        val c53 = example.xiangshan.C53()
        inputs.c53_io_in = inputs.c53_io_in := (col.take(4) :+ (if (cin.nonEmpty) cin.head else Lit(0).U))
        sum = (List(c53_io_out(0).asBool) ++ (if (cin.nonEmpty) cin.drop(1) else Nil))
        cout1 = List(c53_io_out(1).asBool)
        cout2 = List(c53_io_out(2).asBool)
      } else {
        val cin_1 = if (cin.nonEmpty) List(cin.head) else Nil
        val cin_2 = if (cin.nonEmpty) cin.drop(1) else Nil
        val (s_1, c_1_1, c_1_2) = addOneColumn(col.take(4), cin_1)
        val (s_2, c_2_1, c_2_2) = addOneColumn(col.drop(4), cin_2)
        sum = (s_1 ++ s_2)
        cout1 = (c_1_1 ++ c_2_1)
        cout2 = (c_1_2 ++ c_2_2)
      }
      (sum, cout1, cout2)
    }

    @library
    def addAll(cols: List[List[Bool]], depth: BigInt): (UInt, UInt) = {
      require(len >= 5)
      require(cols.size == 2 * len)
      require(cols.head != Nil())
  

      if (cols.forall((x$9: List[Bool]) => (x$9.size <= 2))) {
        val sum = Cat(cols.map((x$10: List[Bool]) => x$10(0)).reverse)
        val k = 0
        
        // use rowWhile to represent
        (0 until cols.size).foreach((i: BigInt) => if ((cols(i).size == 1)) k = (i + 1))
        val (toZ_all, sum, carry) = rowWhile(cols, len, BigInt(0), BigInt(0), Nil[BigInt](), Nil[BigInt]())
     
        val carry = Cat(cols.drop(k).map((x$11: List[Bool]) => x$11(1)).reverse)
        (sum, Cat(carry, Lit(0, k).U))
      } else {
        val columns_next = List.fill((2 * len))(List())
        val cout1 = List()
        val cout2 = List()

        // addAllWhile
        (0 until cols.length).foreach((i: BigInt) => {
          val (s, c1, c2) = addOneColumn(cols(i), cout1)
          columns_next = columns_next.updated(i, (s ++ cout2))
          cout1 = c1
          cout2 = c2
        })
        val (columns_next: List[List[Boolean]], maxCarry1: List[Boolean], maxCarry2: List[Boolean]) = addAllWhile(len, BigInt(0), cols, columns_update, cout1, cout2, Inv)
      
        val toNextLayer = columns_next
        addAll(toNextLayer, (depth + 1))
      }
    }
    val (sum, carry) = addAll(columns, 0)
    io_result = io_result := (sum + carry)

    (
      ArrayMulDataModuleOutputs(io_result),
      ArrayMulDataModuleRegs()
    )
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }

  def arrayMulDataModuleRun(timeout: Int, inputs: ArrayMulDataModuleInputs, regInit: ArrayMulDataModuleRegs): (ArrayMulDataModuleOutputs, ArrayMulDataModuleRegs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      arrayMulDataModuleRun(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
  def run(inputs: ArrayMulDataModuleInputs, randomInitValue: ArrayMulDataModuleRegs): (ArrayMulDataModuleOutputs, ArrayMulDataModuleRegs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = ArrayMulDataModuleRegs()
    arrayMulDataModuleRun(100, inputs, regInit)
  } ensuring { case (outputs, regNexts) =>
    outputsRequire(outputs) && regsRequire(regNexts)
  }
}