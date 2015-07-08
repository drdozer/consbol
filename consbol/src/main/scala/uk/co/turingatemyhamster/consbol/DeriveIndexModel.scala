package uk.co.turingatemyhamster.consbol

import Derive._

object DeriveIndexModel {

  def `a @ i -| ?`[R, V, I]: Derive[AT[I], Model[R, V, I]] = guard {
    known
  }

  def `a < b -| a @ i, b @ j, i < j`[R, V, I] = Derive[LT[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[AT] { proofLHS =>
      a.rhs.knowLHS[AT] { proofRHS =>
        onlyIf(proofLHS.goal.loc < proofRHS.goal.loc) {
          Proof(a, proofLHS, proofRHS)
        }
      }
    }
  }

  def `a <= b -| a @ i, b @ j, i <= j`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[AT] { proofLHS =>
      a.rhs.knowLHS[AT] { proofRHS =>
        onlyIf(proofLHS.goal.loc <= proofRHS.goal.loc) {
          Proof(a, proofLHS, proofRHS)
        }
      }
    }
  }

  def `a = b -| a @ i, b @ j, i = j`[R, V, I]
  (implicit
   t: Tell[EQ[I], Model[R, V, I]]) = Derive[EQ[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[AT] { proofLHS =>
      a.rhs.knowLHS[AT] { proofRHS =>
        onlyIf(proofLHS.goal.loc == proofRHS.goal.loc) {
          Proof(a, proofLHS, proofRHS)
        }
      }
    }
  }

  def `a != b -| a @ i, b @ j, i != j`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[AT] { proofLHS =>
      a.rhs.knowLHS[AT] { proofRHS =>
        onlyIf(proofLHS.goal.loc != proofRHS.goal.loc) {
          Proof(a, proofLHS, proofRHS)
        }
      }
    }
  }

}
