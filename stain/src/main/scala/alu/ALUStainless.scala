package alu

import chisel3._
import chisel3.util._

import chiseltest._
import chiseltest.formal._
import org.scalatest.flatspec.AnyFlatSpec

import stainless.collection._
import stainless.lang._
import stainless.annotation._

import scala.collection.concurrent.TrieMap
import scala.collection.concurrent.TrieMap

import alu.Adder

case class ALUStainless(@extern dut: Adder) {
    @extern
    def adder(a: BigInt, b: BigInt): BigInt = {
        dut.io.in1.poke(a.U)
        dut.io.in2.poke(b.U)
        dut.io.out.peekInt()
    }

    def prop(a: BigInt, b: BigInt): BigInt = {
        require(0 <= a && a <= 1 && 0 <= b && b <= 1)
        // val sum = BigInt(0) + BigInt(5)
        // stainless.io.StdOut.println(sum)
        adder(a, b)
    } ensuring (res => res >= 0)
}