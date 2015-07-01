package uk.co.turingatemyhamster.consbol

import scala.language.higherKinds
import scalaz.{Need, Name, StreamT}
import scalaz.StreamT.{Done}


trait Know[A, M] {
  def apply(a: A, m0: M): TrueStream[Proof[A]]
}

object Know extends KnowLowPriorityImplicits with KnowLowLowPriorityImplicits {

  implicit class KnowOps[M](val m: M) {
    def know[A](a: A)(implicit k: Know[A, M]) =
      k(a, m)
  }

  implicit def know_lt[I]: Know[LT[I], OrdModel[I]] = new Know[LT[I], OrdModel[I]] {
    override def apply(a: LT[I], m0: OrdModel[I]): TrueStream[Proof[LT[I]]] =
      StreamT apply Need {
        if(m0.lt(a.lhs -> a.rhs))
          singleton(Fact(a) : Proof[LT[I]])
        else
          Done
      }
  }

  implicit def know_lt_eq[I]: Know[LT_EQ[I], OrdModel[I]] = new Know[LT_EQ[I], OrdModel[I]] {
    override def apply(a: LT_EQ[I], m0: OrdModel[I]): TrueStream[Proof[LT_EQ[I]]] =
      StreamT apply Need {
        if(m0.lt_eq(a.lhs -> a.rhs))
          singleton(Fact(a))
        else
          Done
      }
  }

  implicit def know_not_eq[I]: Know[NOT_EQ[I], OrdModel[I]] = new Know[NOT_EQ[I], OrdModel[I]] {
    override def apply(a: NOT_EQ[I], m0: OrdModel[I]): TrueStream[Proof[NOT_EQ[I]]] = {
      StreamT apply Need {
        if(m0.not_eq(a.lhs -> a.rhs))
          singleton(Fact(a))
        else
          Done
      }
    }
  }

  implicit def know_eq[V, I]: Know[EQ[I], InterpModel[V, I]] = new Know[EQ[I], InterpModel[V, I]] {
    override def apply(a: EQ[I], m0: InterpModel[V, I]): TrueStream[Proof[EQ[I]]] =
      StreamT apply Need {
        if(a.lhs == a.rhs)
          singleton(Fact(a))
        else
          Done
      }
  }
}

trait KnowLowPriorityImplicits {
  
  import Know.KnowOps

  implicit def know_modelFromInterp[A[_], V, I]
  (implicit k: Know[A[I], InterpModel[V, I]])
  : Know[A[I], Model[V, I]] = new Know[A[I], Model[V, I]] {
    override def apply(a: A[I], m0: Model[V, I]): TrueStream[Proof[A[I]]] =
      m0.i know a
  }

  implicit def know_modelFromOrd[A[_], V, I]
  (implicit k: Know[A[I], OrdModel[I]])
  : Know[A[I], Model[V, I]] = new Know[A[I], Model[V, I]] {
    override def apply(a: A[I], m0: Model[V, I]): TrueStream[Proof[A[I]]] =
      m0.ord know a
  }

}

trait KnowLowLowPriorityImplicits {

  import Know.KnowOps
  import Interpretation.InterpretationOps

  implicit def know_usingInterpretation[A[_], V, I]
  (implicit in: Interpretation[A[V], A[I], Model[V, I]], k: Know[A[I], Model[V, I]])
  : Know[A[V], Model[V, I]] = new Know[A[V], Model[V, I]] {
    override def apply(a: A[V], m0: Model[V, I]): TrueStream[Proof[A[V]]] = {
      val (a1, m1) = m0 interpretation a
      m1 know a1 map (p => Interpreted(a, p))
    }

  }
}
