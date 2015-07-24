package uk.co.turingatemyhamster.consbol

import Derive._
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._

trait OrdDeriveEnv[R, V, I] {
  self : RangeDeriveEnv[R, V, I] with DeriveEnvBase[R, V, I] =>

  import rules._

  implicit lazy final val `a < b -| ?` = guard { derives_LT.reduce(_ || _) }
  def derives_LT: List[Derive[LT[I], R, V, I]]

  implicit lazy final val `a <= b -| ?` = guard { derives_LT_EQ.reduce(_ || _) }
  def derives_LT_EQ: List[Derive[LT_EQ[I], R, V, I]]

  implicit lazy final val `a = b -| ?` = guard { derives_EQ.reduce(_ || _) }
  def derives_EQ: List[Derive[EQ[I], R, V, I]]

  implicit lazy final val `a != b -| ?` = guard { derives_NOT_EQ.reduce(_ || _) }
  def derives_NOT_EQ: List[Derive[NOT_EQ[I], R, V, I]]
}

trait OrdDeriveRules[R, V, I] {
  self : DeriveDSL[R, V, I] =>

  final lazy val `a < b -| k(a < b)` = known[LT, I]

  final lazy val ltRecursion: List[Derive[LT[I], R, V, I]] =
    `a < c -| a < b, b <= c` ::
      `a < c -| a <= b, b < c` ::
      `a < c -| a < b, b < c` ::
      Nil

  final lazy val lteqRecursion: List[Derive[LT_EQ[I], R, V, I]] =
    `a <= c -| a <= b, b <= c` ::
      Nil


  final lazy val `a < c -| a < b, b <= c` = withEnv[LT[I]] { env =>
    import env._
    newEnvA(env without ltRecursion without lteqRecursion) { a =>
    a.lhs.deriveLHS[LT] (
      lhsD => Disproof1(a, lhsD),
      newEnvP(env) { lhsP =>
      LT_EQ(lhsP.goal.rhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
      }
    )
    }
  }

  final lazy val `a < c -| a <= b, b < c` = withEnv[LT[I]] { env =>
    import env._
    newEnvA(env without ltRecursion without lteqRecursion) { a =>
    a.lhs.knowLHS[LT_EQ] (
      lhsD => Disproof1(a, lhsD),
      newEnvP(env) { (lhsP: Proof[LT_EQ[I]]) =>
      LT(lhsP.goal.rhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
      }
    )
    }
  }


  final lazy val `a < c -| a < b, b < c` = withEnv[LT[I]] { env =>
    import env._
    newEnvA(env without ltRecursion without lteqRecursion) { a =>
    a.lhs.deriveLHS[LT] (
      lhsD => Disproof1(a, lhsD),
      newEnvP(env) {
      lhsP => LT(lhsP.goal.rhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
      }
    )
    }
  }

  final lazy val `a <= b -| k(a <= b)` = known[LT_EQ, I]

  final lazy val `a <= c -| a <= b, b <= c` = withEnv[LT_EQ[I]] { env =>
    import env._
    newEnvA(env without ltRecursion without lteqRecursion) { a =>
    a.lhs.knowLHS[LT_EQ] (
      lhsD => Disproof1(a, lhsD),
      newEnvP(env) {
      lhsP => LT_EQ(lhsP.goal.rhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
      }
    )
    }
  }

  final lazy val `a <= b -| a < b` = withEnv[LT_EQ[I]] { env => a =>
    import env._
    LT(a.lhs, a.rhs) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Proof1(a, lhsP)
    )
  }


  final lazy val `a = b -| a <=b, b <= a` = withEnv[EQ[I]] { env => a =>
    import env._
    LT_EQ(a.lhs, a.rhs) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => LT_EQ(a.rhs, a.lhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `a != b -| k(a != b)` = known[NOT_EQ, I]

  final lazy val `a != b -| a < b` = withEnv[NOT_EQ[I]] { env => a =>
    import env._
    LT(a.lhs, a.rhs) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Proof1(a, lhsP)
    )
  }

  final lazy val `a != b -| b < a` = withEnv[NOT_EQ[I]] { env => a =>
    import env._
    LT(a.rhs, a.lhs) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Proof1(a, lhsP)
    )
  }

}
