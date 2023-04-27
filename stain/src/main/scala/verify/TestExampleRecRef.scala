[ Debug  ] -------------Functions-------------
[ Debug  ] def main(args: Array[String]): Unit = ()
[ Debug  ] 
[ Debug  ] def foo(len: BigInt, a: BigInt, b: BigInt): (BigInt, BigInt) = {
[ Debug  ]   require(len >= BigInt("1"))
[ Debug  ]   require(a < Pow2(len) && a >= BigInt("0"))
[ Debug  ]   require(b < Pow2(len) && b > BigInt("0"))
[ Debug  ]   val cnt: BigInt = BigInt("0")
[ Debug  ]   val R: BigInt = a
[ Debug  ]   val Q: BigInt = BigInt("0")
[ Debug  ]   val shiftReg: BigInt = a * BigInt("2")
[ Debug  ]   val t: (Unit, BigInt, BigInt, BigInt) = if (cnt < len) {
[ Debug  ]     fooWhile(a, b, len, cnt, R, shiftReg)
[ Debug  ]   } else {
[ Debug  ]     ((), cnt, R, shiftReg)
[ Debug  ]   }
[ Debug  ]   val res: Unit = t._1
[ Debug  ]   val shiftReg: BigInt = t._4
[ Debug  ]   val R: BigInt = t._3
[ Debug  ]   val cnt: BigInt = t._2
[ Debug  ]   val tmp: Unit = res
[ Debug  ]   val hi: BigInt = {
[ Debug  ]     val d: BigInt = Pow2(len)
[ Debug  ]     assert(d != BigInt("0"), "Division by zero")
[ Debug  ]     shiftReg / d
[ Debug  ]   }
[ Debug  ]   val resR: BigInt = {
[ Debug  ]     assert(BigInt("2") != BigInt("0"), "Division by zero")
[ Debug  ]     hi / BigInt("2")
[ Debug  ]   }
[ Debug  ]   val resQ: BigInt = shiftReg - hi * Pow2(len)
[ Debug  ]   (resQ, resR)
[ Debug  ] }
[ Debug  ] 
[ Debug  ] @synthetic
[ Debug  ] def ObjectPrimitiveSize(x: Object): BigInt = {
[ Debug  ]   x match {
[ Debug  ]     case Open(value) =>
[ Debug  ]       BigInt("1") + BigIntAbs(value)
[ Debug  ]   }
[ Debug  ] } ensuring {
[ Debug  ]   (res: BigInt) => res >= BigInt("0")
[ Debug  ] }
[ Debug  ] 
[ Debug  ] @opaque
[ Debug  ] def Pow2Mul(x: BigInt, y: BigInt): Unit = {
[ Debug  ]   require(x >= BigInt("0"))
[ Debug  ]   require(y >= BigInt("0"))
[ Debug  ]   decreases(x)
[ Debug  ]   x match {
[ Debug  ]     case BigInt("0") =>
[ Debug  ]       ()
[ Debug  ]     case _ =>
[ Debug  ]       val prev$3: RAEqEvidence[BigInt, Boolean] = {
[ Debug  ]         val thiss: RAEqEvidence[BigInt, Unit] = {
[ Debug  ]           val x: () => BigInt = () => Pow2(x + y)
[ Debug  ]           (RAEqEvidence[BigInt, Unit](() => x(), () => x(), () => ())): @DropVCs 
[ Debug  ]         }
[ Debug  ]         val proof: () => Boolean = () => trivial
[ Debug  ]         (RAEqEvidence[BigInt, Boolean](thiss.x, thiss.y, () => proof())): @DropVCs 
[ Debug  ]       }
[ Debug  ]       val prev$2: RAEqEvidence[BigInt, Unit] = {
[ Debug  ]         val thiss: RAEqEvidence[BigInt, Unit] = {
[ Debug  ]           val x: () => BigInt = () => BigInt("2") * Pow2((x - BigInt("1")) + y)
[ Debug  ]           (RAEqEvidence[BigInt, Unit](() => x(), () => x(), () => ())): @DropVCs 
[ Debug  ]         }
[ Debug  ]         val proof: () => Unit = () => {
[ Debug  ]           val x: BigInt = x - BigInt("1")
[ Debug  ]           val y: BigInt = y
[ Debug  ]           assert(((x >= BigInt("0"))): @DropVCs , "Inlined precondition (1/2) of Pow2Mul")
[ Debug  ]           assert(((y >= BigInt("0"))): @DropVCs , "Inlined precondition (2/2) of Pow2Mul")
[ Debug  ]           val _$1: Unit = {
[ Debug  ]             val x: BigInt = x
[ Debug  ]             val y: BigInt = y
[ Debug  ]             assert(((x >= BigInt("0"))): @DropVCs , "Inlined precondition (1/2) of Pow2Mul")
[ Debug  ]             assert(((y >= BigInt("0"))): @DropVCs , "Inlined precondition (2/2) of Pow2Mul")
[ Debug  ]             val _$1: Unit = Pow2Mul(x, y)
[ Debug  ]             assume(((Pow2(x + y) == Pow2(x) * Pow2(y))): @DropVCs )
[ Debug  ]             _$1
[ Debug  ]           }
[ Debug  ]           assume(((Pow2(x + y) == Pow2(x) * Pow2(y))): @DropVCs )
[ Debug  ]           _$1
[ Debug  ]         }
[ Debug  ]         (RAEqEvidence[BigInt, Unit](thiss.x, thiss.y, () => proof())): @DropVCs 
[ Debug  ]       }
[ Debug  ]       val prev$1: RAEqEvidence[BigInt, Boolean] = {
[ Debug  ]         val thiss: RAEqEvidence[BigInt, Unit] = {
[ Debug  ]           val x: () => BigInt = () => (BigInt("2") * Pow2(x - BigInt("1"))) * Pow2(y)
[ Debug  ]           (RAEqEvidence[BigInt, Unit](() => x(), () => x(), () => ())): @DropVCs 
[ Debug  ]         }
[ Debug  ]         val proof: () => Boolean = () => trivial
[ Debug  ]         (RAEqEvidence[BigInt, Boolean](thiss.x, thiss.y, () => proof())): @DropVCs 
[ Debug  ]       }
[ Debug  ]       val thiss: RAEqEvidence[BigInt, Boolean] = {
[ Debug  ]         val thiss: RAEqEvidence[BigInt, Unit] = {
[ Debug  ]           val thiss: RAEqEvidence[BigInt, Boolean] = {
[ Debug  ]             val thiss: RAEqEvidence[BigInt, Unit] = {
[ Debug  ]               val x: () => BigInt = () => Pow2(x) * Pow2(y)
[ Debug  ]               (RAEqEvidence[BigInt, Unit](() => x(), () => x(), () => ())): @DropVCs 
[ Debug  ]             }
[ Debug  ]             val prev: RAEqEvidence[BigInt, Boolean] = prev$1
[ Debug  ]             assert(((keepEvidence[Boolean](prev.evidence()) ==> (prev.y() == thiss.x()))): @ghost  @DropVCs , "Inlined precondition of |:")
[ Debug  ]             (RAEqEvidence[BigInt, Boolean](prev.x, thiss.y, prev.evidence)): @DropVCs 
[ Debug  ]           }
[ Debug  ]           val prev: RAEqEvidence[BigInt, Unit] = prev$2
[ Debug  ]           assert(((keepEvidence[Unit](prev.evidence()) ==> (prev.y() == thiss.x()))): @ghost  @DropVCs , "Inlined precondition of |:")
[ Debug  ]           (RAEqEvidence[BigInt, Unit](prev.x, thiss.y, prev.evidence)): @DropVCs 
[ Debug  ]         }
[ Debug  ]         val prev: RAEqEvidence[BigInt, Boolean] = prev$3
[ Debug  ]         assert(((keepEvidence[Boolean](prev.evidence()) ==> (prev.y() == thiss.x()))): @ghost  @DropVCs , "Inlined precondition of |:")
[ Debug  ]         (RAEqEvidence[BigInt, Boolean](prev.x, thiss.y, prev.evidence)): @DropVCs 
[ Debug  ]       }
[ Debug  ]       val _$1: Unit = (()): @DropVCs 
[ Debug  ]       assume(((thiss.x() == thiss.y())): @ghost  @DropVCs )
[ Debug  ]       _$1
[ Debug  ]   }
[ Debug  ] } ensuring {
[ Debug  ]   (_$1: Unit) => Pow2(x + y) == Pow2(x) * Pow2(y)
[ Debug  ] }
[ Debug  ] 
[ Debug  ] @library
[ Debug  ] def ==:|[A, B, C](thiss: RAEqEvidence[A, B], proof: () => C): RAEqEvidence[A, C] = RAEqEvidence[A, C](thiss.x, thiss.y, () => proof())
[ Debug  ] 
[ Debug  ] @synthetic
[ Debug  ] def BigIntAbs(x: BigInt): BigInt = if (x >= BigInt("0")) {
[ Debug  ]   x
[ Debug  ] } else {
[ Debug  ]   -x
[ Debug  ] }
[ Debug  ] 
[ Debug  ] @synthetic
[ Debug  ] def RAEqEvidencePrimitiveSize[A, B](x: RAEqEvidence[A, B]): BigInt = {
[ Debug  ]   x match {
[ Debug  ]     case RAEqEvidence(x, y, evidence) =>
[ Debug  ]       ((BigInt("1") + BigInt("0")) + BigInt("0")) + BigInt("0")
[ Debug  ]   }
[ Debug  ] } ensuring {
[ Debug  ]   (res: BigInt) => res >= BigInt("0")
[ Debug  ] }
[ Debug  ] 
[ Debug  ] @library
[ Debug  ] def inv[A, B](thiss: RAEqEvidence[A, B]): Boolean = ((thiss.x() == thiss.y())): @ghost 
[ Debug  ] 
[ Debug  ] def Mux(x: Boolean, y: BigInt, z: BigInt): BigInt = x match {
[ Debug  ]   case true =>
[ Debug  ]     y
[ Debug  ]   case _ =>
[ Debug  ]     z
[ Debug  ] }
[ Debug  ] 
[ Debug  ] @library
[ Debug  ] def any2RAEqEvidence[A](x: () => A): RAEqEvidence[A, Unit] = RAEqEvidence[A, Unit](() => x(), () => x(), () => ())
[ Debug  ] 
[ Debug  ] @library
[ Debug  ] def trivial: Boolean = true
[ Debug  ] 
[ Debug  ] @derived(foo)
[ Debug  ] def fooWhile(a: BigInt, b: BigInt, len: BigInt, cnt: BigInt, R: BigInt, shiftReg: BigInt): (Unit, BigInt, BigInt, BigInt) = {
[ Debug  ]   require(((len >= BigInt("1"))): @dropConjunct  @DropVCs  &&& (((a < Pow2(len))): @dropConjunct  @DropVCs  &&& (((a >= BigInt("0"))): @dropConjunct  @DropVCs  &&& (((b < Pow2(len))): @dropConjunct  @DropVCs  &&& ((b > BigInt("0"))): @dropConjunct  @DropVCs ))))
[ Debug  ]   val R: BigInt = (a): @DropVCs 
[ Debug  ]   val shiftReg: BigInt = ((a * BigInt("2"))): @DropVCs 
[ Debug  ]   {
[ Debug  ]     require((((BigInt("0") <= cnt && cnt <= len) && shiftReg >= BigInt("0")) && {
[ Debug  ]       val d: BigInt = Pow2(cnt + BigInt("1"))
[ Debug  ]       assert(d != BigInt("0"), "Division by zero")
[ Debug  ]       shiftReg / d
[ Debug  ]     } == R) &&& (cnt < len))
[ Debug  ]     decreases(len - cnt)
[ Debug  ]     val shiftReg: BigInt = shiftReg
[ Debug  ]     val R: BigInt = R
[ Debug  ]     val cnt: BigInt = cnt
[ Debug  ]     val tmp: Unit = {
[ Debug  ]       val x: BigInt = cnt + BigInt("2")
[ Debug  ]       val y: BigInt = (len - cnt) - BigInt("1")
[ Debug  ]       assert(((x >= BigInt("0"))): @DropVCs , "Inlined precondition (1/2) of Pow2Mul")
[ Debug  ]       assert(((y >= BigInt("0"))): @DropVCs , "Inlined precondition (2/2) of Pow2Mul")
[ Debug  ]       val _$1: Unit = Pow2Mul(x, y)
[ Debug  ]       assume(((Pow2(x + y) == Pow2(x) * Pow2(y))): @DropVCs )
[ Debug  ]       _$1
[ Debug  ]     }
[ Debug  ]     val hi: BigInt = {
[ Debug  ]       val d: BigInt = Pow2(len)
[ Debug  ]       assert(d != BigInt("0"), "Division by zero")
[ Debug  ]       shiftReg / d
[ Debug  ]     }
[ Debug  ]     val lo: BigInt = shiftReg - hi * Pow2(len)
[ Debug  ]     val e: BigInt = Mux(hi >= b, BigInt("1"), BigInt("0"))
[ Debug  ]     assert(shiftReg >= (Pow2(len) * b) * e)
[ Debug  ]     val R: BigInt = R - (b * Pow2((len - cnt) - BigInt("1"))) * e
[ Debug  ]     val tmp: Unit = ()
[ Debug  ]     val shiftReg: BigInt = (BigInt("2") * shiftReg - (b * e) * Pow2(len + BigInt("1"))) + e
[ Debug  ]     val tmp: Unit = ()
[ Debug  ]     val cnt: BigInt = cnt + BigInt("1")
[ Debug  ]     val tmp: Unit = ()
[ Debug  ]     if (cnt < len) {
[ Debug  ]       fooWhile(a, b, len, cnt, R, shiftReg)
[ Debug  ]     } else {
[ Debug  ]       ((), cnt, R, shiftReg)
[ Debug  ]     }
[ Debug  ]   } ensuring {
[ Debug  ]     (_res: (Unit, BigInt, BigInt, BigInt)) => {
[ Debug  ]       val shiftReg: BigInt = _res._4
[ Debug  ]       val R: BigInt = _res._3
[ Debug  ]       val cnt: BigInt = _res._2
[ Debug  ]       (((BigInt("0") <= cnt && cnt <= len) && shiftReg >= BigInt("0")) && {
[ Debug  ]         val d: BigInt = Pow2(cnt + BigInt("1"))
[ Debug  ]         assert(d != BigInt("0"), "Division by zero")
[ Debug  ]         shiftReg / d
[ Debug  ]       } == R) &&& !(cnt < len)
[ Debug  ]     }
[ Debug  ]   }
[ Debug  ] }
