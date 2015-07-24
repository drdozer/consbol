package uk.co.turingatemyhamster.consbol


import uk.co.turingatemyhamster.consbol.util.FuncName
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._

case class RangeDeriveEnv[R, V, I](rules: DeriveDSL[R, V, I],
                                   derives_RangeAs: List[Derive[RangeAs[R, I], R, V, I]])
{
  import rules._

  implicit lazy final val `RangeAs(r, a, b) -| ?` = guard { derives_RangeAs.reduce(_ || _) }
}

trait RangeDeriveRules[R, V, I] {
 self : DeriveDSL[R, V, I] =>

  final lazy val `RangeAs(r, a, b) -| k(RangeAs(r, a, b))` = known2[RangeAs, R, I]

  final lazy val `a < b -| RangeAs(r, a, b)` = Derive[LT[I], R, V, I] { a =>
    (a.lhs, a.rhs).knowValue2[RangeAs[R, I]](
      lhsD => Disproof1(a, lhsD),
      lhsP => Proof1(a, lhsP)
    )
  }
}
