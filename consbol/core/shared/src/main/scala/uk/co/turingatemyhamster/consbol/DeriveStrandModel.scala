package uk.co.turingatemyhamster.consbol


import Derive._
import uk.co.turingatemyhamster.consbol.util.Utils._

object DeriveStrandModel {

  def `±r -| ?`[R, V, I]
  : Derive[Strand[R], Model[R, V, I]] = guard {
    `±r -| k(±r)` ||
      `±r -| ∃s: ±s. r±s` ||
      `±r -| ∃s: ∓s, r∓s`
  }

  def `±r -| k(±r)`[R, V, I] = known[Strand, R, Model[R, V, I]]

  def `±r -| ∃s: ±s. r±s`[R, V, I] = Derive[Strand[R], Model[R, V, I]] { a =>
    `± ⇒ ∃r: ±r`[R, V, I](a.orient) (
      lhsD => Disproof1(a, lhsD),
      lhsP => SameStrandAs(a.range, lhsP.goal.range) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `± ⇒ ∃r: ±r`[R, V, I](o: Orientation) = o.knowValue[Strand[R]]

  def `±r -| ∃s: ∓s, r∓s`[R, V, I] = Derive[Strand[R], Model[R, V, I]] { a =>
    `± ⇒ ∃r: ±r`[R, V, I](a.orient.inverse) (
      lhsD => Disproof1(a, lhsD),
      lhsP => DifferentStrandTo(a.range, lhsP.goal.range) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }


  def `r±s -| ?`[R, V, I]
  : Derive[SameStrandAs[R], Model[R, V, I]] = guard {
    `r±s -| k(r±s) or k(s±r)` ||
      `r±s -| +r, +s` ||
      `r±s -| -r, -s` ||
      `r±s -| ∃t: k(r±t). t±s` ||
      `r±s -| ∃t: k(r∓t). t∓s` ||
      `r±s -| ∃t: k(t±r). t±s` ||
      `r±s -| ∃t: k(t∓r). t∓s`
  }

  def `r±s -| k(r±s) or k(s±r)`[R, V, I] = `r±s -| k(r±s)`[R, V, I].sym

  def `r±s -| k(r±s)`[R, V, I] = known[SameStrandAs, R, Model[R, V, I]]

  def `r±s -| +r, +s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    Strand(a.lhs, Orientation.+) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Strand(a.rhs, Orientation.+) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r±s -| -r, -s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    Strand(a.lhs, Orientation.-) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Strand(a.rhs, Orientation.-) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r ⇒ ∃s: k(r±s)`[R, V, I](r: R) = r.knowLHS[SameStrandAs]
  def `r ⇒ ∃s: k(r∓s)`[R, V, I](r: R) = r.knowLHS[DifferentStrandTo]
  def `r ⇒ ∃s: k(s±r)`[R, V, I](r: R) = r.knowRHS[SameStrandAs]
  def `r ⇒ ∃s: k(s∓r)`[R, V, I](r: R) = r.knowRHS[DifferentStrandTo]

  def `r±s -| ∃t: k(r±t). t±s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    `r ⇒ ∃s: k(r±s)`[R, V, I](a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => SameStrandAs(lhsP.goal.rhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r±s -| ∃t: k(r∓t). t∓s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    `r ⇒ ∃s: k(r∓s)`[R, V, I](a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => DifferentStrandTo(lhsP.goal.rhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r±s -| ∃t: k(t±r). t±s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    `r ⇒ ∃s: k(s±r)`[R, V, I](a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => SameStrandAs(lhsP.goal.lhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r±s -| ∃t: k(t∓r). t∓s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    `r ⇒ ∃s: k(s∓r)`[R, V, I](a.lhs) (
      lhsD => Disproof1(a, lhsD),
      lhsP => DifferentStrandTo(lhsP.goal.lhs, a.rhs) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }


  def `r∓s -| ?`[R, V, I]
  : Derive[DifferentStrandTo[R], Model[R, V, I]] = guard {
    `r∓s -| k(r∓s)` ||
      `r∓s -| +r, -s` ||
      `r∓s -| -r, +s` ||
      `r∓s -| ∃t: k(r∓t). t±s` ||
      `r∓s -| r∃t: k(r±t). t∓s` ||
      `r∓s -| ∃t: k(t∓r). t±s` ||
      `r∓s -| ∃t: k(t±r). t∓s`
  }

  def `r∓s -| k(r∓s)`[R, V, I] = known[DifferentStrandTo, R, Model[R, V, I]].sym

  def `r∓s -| +r, -s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    Strand(a.lhs, Orientation.+) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Strand(a.rhs, Orientation.-) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r∓s -| -r, +s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    Strand(a.lhs, Orientation.-) derive (
      lhsD => Disproof1(a, lhsD),
      lhsP => Strand(a.rhs, Orientation.+) derive (
        rhsD => Disproof2(a, lhsP, rhsD),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r∓s -| ∃t: k(r∓t). t±s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    `r ⇒ ∃s: k(r∓s)`[R, V, I](a.lhs) (
      lhsDisproof => Disproof1(a, lhsDisproof),
      lhsP => SameStrandAs(lhsP.goal.rhs, a.rhs) derive (
        rhsDisproof => Disproof2(a, lhsP, rhsDisproof),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r∓s -| r∃t: k(r±t). t∓s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    `r ⇒ ∃s: k(r±s)`[R, V, I](a.lhs) (
      lhsDisproof => Disproof1(a, lhsDisproof),
      lhsP => DifferentStrandTo(lhsP.goal.rhs, a.rhs) derive (
        rhsDisproof => Disproof2(a, lhsP, rhsDisproof),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r∓s -| ∃t: k(t∓r). t±s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    `r ⇒ ∃s: k(s∓r)`[R, V, I](a.lhs) (
      lhsDisproof => Disproof1(a, lhsDisproof),
      lhsP => SameStrandAs(lhsP.goal.lhs, a.rhs) derive (
        rhsDisproof => Disproof2(a, lhsP, rhsDisproof),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }

  def `r∓s -| ∃t: k(t±r). t∓s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    `r ⇒ ∃s: k(s±r)`[R, V, I](a.lhs) (
      lhsDisproof => Disproof1(a, lhsDisproof),
      lhsP => DifferentStrandTo(lhsP.goal.lhs, a.rhs) derive (
        rhsDisproof => Disproof2(a, lhsP, rhsDisproof),
        rhsP => Proof2(a, lhsP, rhsP)
      )
    )
  }
}

