package uk.co.turingatemyhamster.consbol

import Derive._

object DeriveOrdModel {

  def `a < b -| ?`[R, V, I]
  (implicit k: Know[LT, I, Model[R, V, I]])
  : Derive[LT[I], Model[R, V, I]] = guard {
    known ||
      DeriveIndexModel.`a < b -| a @ i, b @ j, i < j` ||
      `a < c -| a < b, b < c` ||
      `a <_c -| a < b, b <= c` ||
      `a < c -| a <= b, b < c`
  }

  def `a <_c -| a < b, b <= c`[R, V, I] = Derive[LT[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[LT] { lhsProof =>
      LT_EQ(lhsProof.goal.rhs, a.rhs) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `a < c -| a <= b, b < c`[R, V, I] = Derive[LT[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[LT_EQ] { lhsProof =>
      LT(lhsProof.goal.rhs, a.rhs) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `a < c -| a < b, b < c`[R, V, I] = Derive[LT[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[LT] { lhsProof =>
      LT(lhsProof.goal.rhs, a.rhs) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `a <= b -| ?`[R, V, I]
  (implicit kLtEq: Know[LT_EQ, I, Model[R, V, I]]) = guard {
    known ||
      DeriveIndexModel.`a <= b -| a @ i, b @ j, i <= j` ||
      `a <= b -| a < b` ||
      `a <= c -| a <= b, b <= c`
  }

  def `a <= c -| a <= b, b <= c`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] { a =>
    a.lhs.knowLHS[LT_EQ] { lhsProof =>
      LT_EQ(lhsProof.goal.rhs, a.rhs) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }

  def `a <= b -| a < b`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] { a =>
    LT(a.lhs, a.rhs) derive { ltProof =>
      Proof(a, ltProof)
    }
  }


  def `a = b -| ?`[R, V, I]
  (implicit t: Tell[EQ[I], Model[R, V, I]]) = guard {
    DeriveIndexModel.`a = b -| a @ i, b @ j, i = j` ||
      `a = b -| a <=b, b <= a`
  }


  def `a = b -| a <=b, b <= a`[R, V, I]
  (implicit t: Tell[EQ[I], Model[R, V, I]]) = Derive[EQ[I], Model[R, V, I]] { a =>
    LT_EQ(a.lhs, a.rhs) derive { lhsProof =>
      LT_EQ(a.rhs, a.lhs) derive { rhsProof =>
        Proof(a, lhsProof, rhsProof)
      }
    }
  }


  def `a != b -| ?`[R, V, I]
  (implicit k: Know[NOT_EQ, I, Model[R, V, I]]) = guard {
    known ||
      DeriveIndexModel.`a != b -| a @ i, b @ j, i != j` ||
      `a != b -| a < b` ||
      `a != b -| b < a`
  }

  def `a != b -| a < b`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] { a =>
    LT(a.lhs, a.rhs) derive { ltProof =>
      Proof(a, ltProof)
    }
  }

  def `a != b -| b < a`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] { a =>
    LT(a.rhs, a.lhs) derive { ltProof =>
      Proof(a, ltProof)
    }
  }

}
