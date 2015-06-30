package uk.co.turingatemyhamster.consbol

import scala.language.higherKinds

/**
 * Created by nmrp3 on 27/06/15.
 */
object Know extends KnowLowPriorityImplicits with KnowLowLowPriorityImplicits {

  implicit class KnowOps[M](val m: M) {
    def know[A](a: A)(implicit k: Know[A, M]) =
      k(a, m)
  }

  implicit def know_lt[I]: Know[LT[I], OrdModel[I]] = new Know[LT[I], OrdModel[I]] {
    override def apply(a: LT[I], m0: OrdModel[I]): Stream[Proof[LT[I]]] =
      if(m0.lt(a.lhs -> a.rhs))
        Stream(Fact(a))
      else
        Stream()
  }

  implicit def know_lt_eq[I]: Know[LT_EQ[I], OrdModel[I]] = new Know[LT_EQ[I], OrdModel[I]] {
    override def apply(a: LT_EQ[I], m0: OrdModel[I]): Stream[Proof[LT_EQ[I]]] =
      if(m0.lt_eq(a.lhs -> a.rhs))
        Stream(Fact(a))
      else
        Stream()
  }

  implicit def know_not_eq[I]: Know[NOT_EQ[I], OrdModel[I]] = new Know[NOT_EQ[I], OrdModel[I]] {
    override def apply(a: NOT_EQ[I], m0: OrdModel[I]): Stream[Proof[NOT_EQ[I]]] = {
      if(m0.not_eq(a.lhs -> a.rhs))
        Stream(Fact(a))
      else
        Stream()
    }
  }

  implicit def know_eq[V, I]: Know[EQ[I], InterpModel[V, I]] = new Know[EQ[I], InterpModel[V, I]] {
    override def apply(a: EQ[I], m0: InterpModel[V, I]): Stream[Proof[EQ[I]]] =
      if(a.lhs == a.rhs)
        Stream(Fact(a))
      else
        Stream()
  }
}

trait KnowLowPriorityImplicits {
  
  import Know.KnowOps

  implicit def know_modelFromInterp[A[_], V, I]
  (implicit k: Know[A[I], InterpModel[V, I]])
  : Know[A[I], Model[V, I]] = new Know[A[I], Model[V, I]] {
    override def apply(a: A[I], m0: Model[V, I]): Stream[Proof[A[I]]] =
      m0.i know a
  }

  implicit def know_modelFromOrd[A[_], V, I]
  (implicit k: Know[A[I], OrdModel[I]])
  : Know[A[I], Model[V, I]] = new Know[A[I], Model[V, I]] {
    override def apply(a: A[I], m0: Model[V, I]): Stream[Proof[A[I]]] =
      m0.ord know a
  }

}

trait KnowLowLowPriorityImplicits {

  import Know.KnowOps
  import Interpretation.InterpretationOps

  implicit def know_usingInterpretation[A[_], V, I]
  (implicit in: Interpretation[A[V], A[I], Model[V, I]], k: Know[A[I], Model[V, I]])
  : Know[A[V], Model[V, I]] = new Know[A[V], Model[V, I]] {
    override def apply(a: A[V], m0: Model[V, I]): Stream[Proof[A[V]]] = {
      val (a1, m1) = m0 interpretation a
      m1 know a1 map (p => Interpreted(a, p))
    }

  }
}

trait Know[A, M] {
  def apply(a: A, m0: M): Stream[Proof[A]]
}