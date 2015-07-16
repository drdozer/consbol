package uk.co.turingatemyhamster.consbol

import Derive._
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._

trait IndexDeriveEnv[R, V, I] {
  self : DeriveEnvBase[R, V, I] =>

  import rules._

  implicit lazy final val `a @ i -| ?` = guard { derives_AT.reduce(_ || _) }
  def derives_AT: List[Derive[AT[I], R, V, I]]
}

trait IndexDeriveRules[R, V, I] {
  self : DeriveDSL[R, V, I] =>

  final lazy val `a @ i -| k(a @ i)` = known[AT, I]

  final lazy val `a < b -| a @ i, b @ j, i < j` = Derive[LT[I], R, V, I] { a =>
    a.lhs.knowLHS[AT] (
      lhsD => Disproof1(a, lhsD),
      lhsP => a.rhs.knowLHS[AT] (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => onlyIf(lhsP.goal.loc < rhsP.goal.loc) {
          Proof2(a, lhsP, rhsP)
        }
      )
    )
  } log

  final lazy val `a <= b -| a @ i, b @ j, i <= j` = Derive[LT_EQ[I], R, V, I] { a =>
    a.lhs.knowLHS[AT] (
      lhsD => Disproof1(a, lhsD),
      lhsP => a.rhs.knowLHS[AT] (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => onlyIf(lhsP.goal.loc <= rhsP.goal.loc) {
          Proof2(a, lhsP, rhsP)
        }
      )
    )
  } log

  final lazy val `a = b -| a @ i, b @ j, i = j` = Derive[EQ[I], R, V, I] { a =>
    a.lhs.knowLHS[AT] (
      lhsD => Disproof1(a, lhsD),
      lhsP => a.rhs.knowLHS[AT] (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => onlyIf(lhsP.goal.loc == rhsP.goal.loc) {
          Proof2(a, lhsP, rhsP)
        }
      )
    )
  } log

  final lazy val `a != b -| a @ i, b @ j, i != j` = Derive[NOT_EQ[I], R, V, I] { a =>
    a.lhs.knowLHS[AT] (
      lhsD => Disproof1(a, lhsD),
      lhsP => a.rhs.knowLHS[AT] (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => onlyIf(lhsP.goal.loc != rhsP.goal.loc) {
          Proof2(a, lhsP, rhsP)
        }
      )
    )
  } log

}
