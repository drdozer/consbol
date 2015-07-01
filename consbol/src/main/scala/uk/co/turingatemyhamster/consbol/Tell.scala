package uk.co.turingatemyhamster.consbol

import Interpretation._

import scala.language.higherKinds


trait Tell[A, M] {
  def apply(a: A, m: M): M
}

object Tell extends TellLowPriorityImplicits {

  implicit class TellOps[M](val m: M) {
    def tell[A](a: A)(implicit t: Tell[A, M]): M = t(a, m)
  }

  implicit def tell_lt[I]: Tell[LT[I], OrdModel[I]] = new Tell[LT[I], OrdModel[I]] {
    override def apply(a: LT[I], m: OrdModel[I]): OrdModel[I] =
      m.copy(lt = m.lt + (a.lhs -> a.rhs))
  }

  implicit def tell_lt_eq[I]: Tell[LT_EQ[I], OrdModel[I]] = new Tell[LT_EQ[I], OrdModel[I]] {
    override def apply(a: LT_EQ[I], m: OrdModel[I]): OrdModel[I] =
      m.copy(lt_eq = m.lt_eq + (a.lhs -> a.rhs))
  }

  implicit def tell_not_eq[I]: Tell[NOT_EQ[I], OrdModel[I]] = new Tell[NOT_EQ[I], OrdModel[I]] {
    override def apply(a: NOT_EQ[I], m: OrdModel[I]): OrdModel[I] =
      m.copy(not_eq = m.not_eq + (a.lhs -> a.rhs))
  }

  implicit def tell_eq[V, I]
  (implicit vi: InterpretationSingleton[V, I], unify: UnifyI[I])
  : Tell[EQ[V], Model[V, I]] = new Tell[EQ[V], Model[V, I]] {
    override def apply(a: EQ[V], m: Model[V, I]): Model[V, I] =
      m merge (a.lhs, a.rhs)
  }
}

trait TellLowPriorityImplicits {
  import Tell.TellOps

  implicit def tell_usingOrdModel[A[_], V, I]
  (implicit t: Tell[A[I], OrdModel[I]]): Tell[A[I], Model[V, I]] = new Tell[A[I], Model[V, I]] {
    override def apply(a: A[I], m: Model[V, I]): Model[V, I] =
      m.copy(ord = m.ord tell a)
  }

  implicit def tell_viModel[A[_], V, I]
  (implicit t: Tell[A[I], Model[V, I]], avI: Interpretation[A[V], A[I], Model[V, I]])
  : Tell[A[V], Model[V, I]] = new Tell[A[V], Model[V, I]] {
    override def apply(a: A[V], m0: Model[V, I]): Model[V, I] = {
      val (a1, m1) = m0 interpretation a
      m1 tell a1
    }
  }

}
