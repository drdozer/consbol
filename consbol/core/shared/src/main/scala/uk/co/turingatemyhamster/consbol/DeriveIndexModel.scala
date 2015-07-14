package uk.co.turingatemyhamster.consbol

import Derive._
import uk.co.turingatemyhamster.consbol.util.Utils._

object DeriveIndexModel {

  def `a @ i -| ?`[R, V, I]: Derive[AT[I], Model[R, V, I]] = guard {
    known
  }

  def `a < b -| a @ i, b @ j, i < j`[R, V, I] = Derive[LT[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[AT] (
      lhsD => Disproof1(a, lhsD),
      lhsP => a.rhs.knowLHS[AT] (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => onlyIf(lhsP.goal.loc < rhsP.goal.loc) {
          Proof2(a, lhsP, rhsP)
        }
      )
    )
  }

  def `a <= b -| a @ i, b @ j, i <= j`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[AT] (
      lhsD => Disproof1(a, lhsD),
      lhsP => a.rhs.knowLHS[AT] (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => onlyIf(lhsP.goal.loc <= rhsP.goal.loc) {
          Proof2(a, lhsP, rhsP)
        }
      )
    )
  }

  def `a = b -| a @ i, b @ j, i = j`[R, V, I]
  (implicit
   t: Tell[EQ[I], Model[R, V, I]]) = Derive[EQ[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[AT] (
      lhsD => Disproof1(a, lhsD),
      lhsP => a.rhs.knowLHS[AT] (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => onlyIf(lhsP.goal.loc == rhsP.goal.loc) {
          Proof2(a, lhsP, rhsP)
        }
      )
    )
  }

  def `a != b -| a @ i, b @ j, i != j`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[AT] (
      lhsD => Disproof1(a, lhsD),
      lhsP => a.rhs.knowLHS[AT] (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => onlyIf(lhsP.goal.loc != rhsP.goal.loc) {
          Proof2(a, lhsP, rhsP)
        }
      )
    )
  }

}
