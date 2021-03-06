package uk.co.turingatemyhamster.consbol


import monocle.macros.Lenses
import uk.co.turingatemyhamster.consbol.util.FuncName
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._

@Lenses
case class StrandDeriveEnv[R, V, I](rules: DeriveDSL[R, V, I],
                                    derives_Strand: List[Derive[Strand[R], R, V, I]],
                                    derives_SameStrandAs: List[Derive[SameStrandAs[R], R, V, I]],
                                    derives_DifferentStrandTo: List[Derive[DifferentStrandTo[R], R, V, I]])
{
  import rules._

  implicit lazy final val `±r -| ?` = guard { derives_Strand.reduce(_ || _) }
  implicit lazy final val `r±s -| ?` = guard { derives_SameStrandAs.reduce(_ || _) }
  implicit lazy final val `r∓s -| ?` = guard { derives_DifferentStrandTo.reduce(_ || _) }
}

trait StrandDeriveRules[R, V, I] {
  self : DeriveDSL[R, V, I] =>

  final lazy val sameFromStrand = List(`r±s -| +r, +s`, `r±s -| -r, -s`)
  final lazy val differentFromStrand = List(`r∓s -| +r, -s`, `r∓s -| -r, +s`)

  def `± ⇒ ∃r: ±r`(o: Orientation) = o.knowValue[Strand[R]]
  def `r ⇒ ∃s: k(r±s)`(r: R) = r.knowLHS[SameStrandAs]
  def `r ⇒ ∃s: k(r∓s)`(r: R) = r.knowLHS[DifferentStrandTo]
  def `r ⇒ ∃s: k(s±r)`(r: R) = r.knowRHS[SameStrandAs]
  def `r ⇒ ∃s: k(s∓r)`(r: R) = r.knowRHS[DifferentStrandTo]

  final lazy val `±r -| k(±r)` = known[Strand, R]

  final lazy val `±r -| ∃s: ±s. r±s` = withEnv[Strand[R]] { env => a =>
    import env.strand._
    `± ⇒ ∃r: ±r`(a.orient) (
      lhsD => Disproof1(a, lhsD),
      newEnvP(env without sameFromStrand without differentFromStrand) {
        lhsP => SameStrandAs(a.range, lhsP.goal.range) derive (
          rhsD => Disproof2(a, lhsP, rhsD),
          rhsP => Proof2(a, lhsP, rhsP)
        )
      }
    )
  }

  final lazy val `±r -| ∃s: ∓s, r∓s` = withEnv[Strand[R]] { env => a =>
    import env.strand._
    `± ⇒ ∃r: ±r`(a.orient.inverse) (
      lhsD => Disproof1(a, lhsD),
      newEnvP(env without sameFromStrand without differentFromStrand) {
        lhsP => DifferentStrandTo(a.range, lhsP.goal.range) derive (
          rhsD => Disproof2(a, lhsP, rhsD),
          rhsP => resultP(Proof2(a, lhsP, rhsP))(Tell.tell_ds)
        )
      }
    )
  }


  final lazy val `r±s -| k(r±s) or k(s±r)` = `r±s -| k(r±s)`.sym

  final lazy val `r±s -| k(r±s)` = known[SameStrandAs, R]

  final lazy val `r±s -| +r, +s` = withEnv[SameStrandAs[R]] { env => a =>
    import env.strand._
    Strand(a.lhs, Orientation.+) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Strand(a.rhs, Orientation.+) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `r±s -| -r, -s` = withEnv[SameStrandAs[R]] { env => a =>
    import env.strand._
    Strand(a.lhs, Orientation.-) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Strand(a.rhs, Orientation.-) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }


  final lazy val `r±s -| ∃t: k(r±t). t±s` = withEnv[SameStrandAs[R]] { env => a =>
    import env.strand._
    `r ⇒ ∃s: k(r±s)`(a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => SameStrandAs(lhsP.goal.rhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `r±s -| ∃t: k(r∓t). t∓s` = withEnv[SameStrandAs[R]] { env => a =>
    import env.strand._
    `r ⇒ ∃s: k(r∓s)`(a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => DifferentStrandTo(lhsP.goal.rhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `r±s -| ∃t: k(t±r). t±s` = withEnv[SameStrandAs[R]] { env => a =>
    import env.strand._
    `r ⇒ ∃s: k(s±r)`(a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => SameStrandAs(lhsP.goal.lhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `r±s -| ∃t: k(t∓r). t∓s` = withEnv[SameStrandAs[R]] { env => a =>
    import env.strand._
    `r ⇒ ∃s: k(s∓r)`(a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => DifferentStrandTo(lhsP.goal.lhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }


  final lazy val `r∓s -| k(r∓s)` = known[DifferentStrandTo, R]

  final lazy val `r∓s -| k(r∓s) or k(s∓r)` = `r∓s -| k(r∓s)`.sym

  final lazy val `r∓s -| +r, -s` = withEnv[DifferentStrandTo[R]] { env => a =>
    import env.strand._
    Strand(a.lhs, Orientation.+) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Strand(a.rhs, Orientation.-) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `r∓s -| -r, +s` = withEnv[DifferentStrandTo[R]] { env => a =>
    import env.strand._
    Strand(a.lhs, Orientation.-) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Strand(a.rhs, Orientation.+) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `r∓s -| ∃t: k(r∓t). t±s` = withEnv[DifferentStrandTo[R]] { env => a =>
    import env.strand._
    `r ⇒ ∃s: k(r∓s)`(a.lhs) (
      lhsDisproof => Disproof1(a, lhsDisproof),
      lhsP => SameStrandAs(lhsP.goal.rhs, a.rhs) derive (
        rhsDisproof => Disproof2(a, lhsP, rhsDisproof),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `r∓s -| ∃t: k(r±t). t∓s` = withEnv[DifferentStrandTo[R]] { env => a =>
    import env.strand._
    `r ⇒ ∃s: k(r±s)`(a.lhs) (
      lhsDisproof => Disproof1(a, lhsDisproof),
      lhsP => DifferentStrandTo(lhsP.goal.rhs, a.rhs) derive (
        rhsDisproof => Disproof2(a, lhsP, rhsDisproof),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `r∓s -| ∃t: k(t∓r). t±s` = withEnv[DifferentStrandTo[R]] { env => a =>
    import env.strand._
    `r ⇒ ∃s: k(s∓r)`(a.lhs) (
      lhsDisproof => Disproof1(a, lhsDisproof),
      lhsP => SameStrandAs(lhsP.goal.lhs, a.rhs) derive (
        rhsDisproof => Disproof2(a, lhsP, rhsDisproof),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  final lazy val `r∓s -| ∃t: k(t±r). t∓s` = withEnv[DifferentStrandTo[R]] { env => a =>
    import env.strand._
    `r ⇒ ∃s: k(s±r)`(a.lhs) (
      lhsDisproof => resultD(Disproof1(a, lhsDisproof)),
      lhsP => DifferentStrandTo(lhsP.goal.lhs, a.rhs) derive (
        rhsDisproof => Disproof2(a, lhsP, rhsDisproof),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }
}

