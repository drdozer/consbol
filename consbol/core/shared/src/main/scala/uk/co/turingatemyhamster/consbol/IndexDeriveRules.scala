package uk.co.turingatemyhamster.consbol

import Derive._
import uk.co.turingatemyhamster.consbol.util.FuncName
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._

trait IndexDeriveEnv[R, V, I] {
  self : DeriveEnvBase[R, V, I] =>

  import rules._

  implicit lazy final val `a @ i -| ?` = guard { derives_AT.reduce(_ || _) }
  def derives_AT: List[Derive[AT[I], R, V, I]]

  implicit lazy final val `a suc b -| ?` = guard { derives_Suc.reduce(_ || _) }
  def derives_Suc: List[Derive[Suc[I], R, V, I]]
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
  }

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
  }

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
  }

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
  }

  final lazy val `a suc b -| k(a suc b)` = known[Suc, I]

  final lazy val `a suc b -| a @ i, b @ j | i+1=j` = Derive[Suc[I], R, V, I] { a =>
    a.lhs.knowLHS[AT] (
      lhsD => Disproof1(a, lhsD),
      lhsP => a.rhs.knowRHS[AT] (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => onlyIf(lhsP.goal.loc + 1 == rhsP.goal.loc) {
          Proof2(a, lhsP, rhsP)
        }
      )
    )
  }

  def `a => ∃b: k(a suc b)`(l: I) = l.knowLHS[Suc]
  def `a => ∃b: k(b suc a)`(l: I) = l.knowRHS[Suc]
  def `a => ∃b: a suc b`(l: I) = l.deriveLHS[Suc]
  def `a => ∃b: b suc a`(l: I) = l.deriveRHS[Suc]

  final lazy val `a @ i -| ∃b: k(a suc b), b @ (i+1)` = withEnv[AT[I]] { env => a =>
    import env._
    `a => ∃b: k(a suc b)`(a.point) (
      lhsD => Disproof1(a, lhsD),
      lhsP => AT(lhsP.goal.rhs, a.loc + 1) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `a @ i -| ∃b: k(b suc a), b @ (i-1)` = withEnv[AT[I]] { env => a =>
    import env._
    `a => ∃b: k(b suc a)`(a.point) (
      lhsD => Disproof1(a, lhsD),
      lhsP => AT(lhsP.goal.lhs, a.loc - 1) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `a < b -| suc(a, b)` = withEnv[LT[I]] { env => a =>
    import env._
    Suc(a.lhs, a.rhs) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Proof1(a, lhsP)
    )
  }

  final lazy val `a <= b -| ∃c: b suc c. a < c` = withEnv[LT_EQ[I]] { env => a =>
    import env._
    `a => ∃b: a suc b`(a.rhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => LT(a.lhs, lhsP.goal.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `a = b -| ∃c: a suc c, b suc c` = withEnv[EQ[I]] { env => a =>
    import env._
    `a => ∃b: a suc b`(a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => Suc(a.rhs, lhsP.goal.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `a = b -| ∃c: c suc a, c suc b` = withEnv[EQ[I]] { env => a =>
    import env._
    `a => ∃b: b suc a`(a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => Suc(lhsP.goal.rhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }
}
