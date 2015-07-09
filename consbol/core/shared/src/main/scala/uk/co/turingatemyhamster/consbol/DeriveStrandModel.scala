package uk.co.turingatemyhamster.consbol


import Derive._
import uk.co.turingatemyhamster.consbol.util.Utils._

object DeriveStrandModel {

  def `±r -| ?`[R, V, I]
  : Derive[Strand[R], Model[R, V, I]] = guard {
    known[Strand, R, Model[R, V, I]] ||
      `±r -| r±s, ±s` ||
      `±r -| r∓s, ∓s`
  }

  def `±r -| r±s, ±s`[R, V, I] = Derive[Strand[R], Model[R, V, I]] { a =>
    a.orient.knowValue[Strand[R]] { rsProof =>
      SameStrandAs(a.range, rsProof.goal.range) derive { sProof =>
        Proof(a, rsProof, sProof)
      }
    }
  }

  def `±r -| r∓s, ∓s`[R, V, I] = Derive[Strand[R], Model[R, V, I]] { a =>
    a.orient.inverse.knowValue[Strand[R]] { rsProof =>
      DifferentStrandTo(a.range, rsProof.goal.range) derive { sProof =>
        Proof(a, rsProof, sProof)
      }
    }
  }


  def `r±s -| ?`[R, V, I]
  : Derive[SameStrandAs[R], Model[R, V, I]] = guard {
    known[SameStrandAs, R, Model[R, V, I]].sym ||
      `r±s -| +r, +s` ||
      `r±s -| -r, -s` /* ||
      `r±s -| r±t, t±s` ||
      `r±s -| r∓t, t∓s` */
  }

  def `r±s -| +r, +s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    Strand(a.lhs, Orientation.+) derive { lhsProof =>
      Strand(a.rhs, Orientation.+) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `r±s -| -r, -s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    Strand(a.lhs, Orientation.-) derive { lhsProof =>
      Strand(a.rhs, Orientation.-) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `r±s -| r±t, t±s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    a.lhs.knowLHS[SameStrandAs] { lhsProof =>
      SameStrandAs(lhsProof.goal.rhs, a.rhs) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `r±s -| r∓t, t∓s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] { a =>
    a.lhs.knowLHS[DifferentStrandTo] { lhsProof =>
      DifferentStrandTo(lhsProof.goal.rhs, a.rhs) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }


  def `r∓s -| ?`[R, V, I]
  : Derive[DifferentStrandTo[R], Model[R, V, I]] = guard {
    known[DifferentStrandTo, R, Model[R, V, I]].sym ||
      `r∓s -| +r, -s` ||
      `r∓s -| -r, +s` /* ||
      `r∓s -| r∓t, t±s` ||
      `r∓s -| r±t, t∓s` */
  }

  def `r∓s -| +r, -s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    Strand(a.lhs, Orientation.+) derive { lhsProof =>
      Strand(a.rhs, Orientation.-) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `r∓s -| -r, +s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    Strand(a.lhs, Orientation.-) derive { lhsProof =>
      Strand(a.rhs, Orientation.+) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `r∓s -| r∓t, t±s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    a.lhs.knowLHS[DifferentStrandTo] { lhsProof =>
      SameStrandAs(lhsProof.goal.rhs, a.rhs) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `r∓s -| r±t, t∓s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] { a =>
    a.lhs.knowLHS[SameStrandAs] { lhsProof =>
      DifferentStrandTo(lhsProof.goal.rhs, a.rhs) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }
}

