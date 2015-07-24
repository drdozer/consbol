package uk.co.turingatemyhamster.consbol

import Interpretation._

import scala.language.higherKinds
import monocle.Lens


trait Tell[A, M] {
  def apply(a: A, m: M): M
}

object Tell
  extends TellOrdModel
  with TellIndexModel
  with TellStrandModel
  with TellLengthModel
  with TellRangeModel
  with TellLowPriorityImplicits
  with TellLowLowPriorityImplicits
{

  implicit class TellOps[M](val m: M) {
    def tell[A](a: A)(implicit t: Tell[A, M]): M = t(a, m)
  }

  def tell_on[A, M1, M2](φ: Lens[M1, M2])(implicit t: Tell[A, M2]) = new Tell[A, M1] {
    override def apply(a: A, m: M1): M1 = φ.modify(t(a, _))(m)
  }

  def tell_binops[A[_], T, M](φ: Lens[M, Set[(T, T)]])(implicit op: BinOp[A, T]): Tell[A[T], M] = new Tell[A[T], M] {
    override def apply(a: A[T], m: M): M =
      φ.modify(_ + op.decompose(a))(m)
  }

  def tell_monops[A[_], T, U, M](φ: Lens[M, Map[T, Set[U]]])(implicit op: MonOp[A, T, U]): Tell[A[T], M] = new Tell[A[T], M] {
    override def apply(a: A[T], m: M): M = {
      val (t, u) = op.decompose(a)
      φ.modify(m0 => m0 + (t -> (m0.getOrElse(t, Set()) + u)))(m)
    }
  }

  def tell_monops2[A[_, _], T, U, X, M](φ: Lens[M, Map[T, Set[X]]])
                                       (implicit op: MonOp2[A, T, U, X]): Tell[A[T, U], M] = new Tell[A[T, U], M]
  {
    override def apply(a: A[T, U], m: M): M = {
      val (t, x) = op.decompose(a)
      φ.modify(m0 => m0 + (t -> (m0.getOrElse(t, Set()) + x)))(m)
    }
  }
}

trait TellOrdModel {

  implicit def tell_lt[I] =
    Tell.tell_binops[LT, I, OrdModel[I]](OrdModel.lt)

  implicit def tell_lt_eq[I] =
    Tell.tell_binops[LT_EQ, I, OrdModel[I]](OrdModel.lt_eq)

  implicit def tell_not_eq[I] =
    Tell.tell_binops[NOT_EQ, I, OrdModel[I]](OrdModel.not_eq)

  // this one requires special handling
  implicit def tell_eq[R, V, I]
  (implicit vi: InterpretationSingleton[V, I], unify: UnifyI[I])
  : Tell[EQ[V], Model[R, V, I]] = new Tell[EQ[V], Model[R, V, I]] {
    override def apply(a: EQ[V], m: Model[R, V, I]): Model[R, V, I] =
      m merge (a.lhs, a.rhs)
  }

  // this one requires special handling
  implicit def tell_eq_inv[R, V, I]
  (implicit
   vi: InterpretationSingleton[V, I], unify: UnifyI[I],
   in: Interpretation[EQ[V], EQ[I], Model[R, V, I]])
  : Tell[EQ[I], Model[R, V, I]] = new Tell[EQ[I], Model[R, V, I]] {
    override def apply(a: EQ[I], m: Model[R, V, I]): Model[R, V, I] =
      tell_eq[R, V, I].apply(in.unapply(a, m).get, m)
  }

}

trait TellIndexModel {

  implicit def tell_at[I]: Tell[AT[I], IndexModel[I]] =
    Tell.tell_monops[AT, I, Int, IndexModel[I]](IndexModel.at)

  implicit def tell_suc[I] =
    Tell.tell_binops[Suc, I, IndexModel[I]](IndexModel.suc)
}

trait TellStrandModel {

  implicit def tell_strand[R]: Tell[Strand[R], StrandModel[R]] = new Tell[Strand[R], StrandModel[R]] {
    override def apply(a: Strand[R], m: StrandModel[R]): StrandModel[R] =
      m.copy(strand = m.strand + (a.range -> (m.strand.getOrElse(a.range, Set()) + a.orient)))
  }

  implicit def tell_same_strand_as[R] =
    Tell.tell_binops[SameStrandAs, R, StrandModel[R]](StrandModel.same_strand_as)

  implicit def tell_different_strand_to[R] =
    Tell.tell_binops[DifferentStrandTo, R, StrandModel[R]](StrandModel.different_strand_to)

}

trait TellLengthModel {

  implicit def tell_length[R]: Tell[Length[R], LengthModel[R]] =
    Tell.tell_monops[Length, R, Int, LengthModel[R]](LengthModel.length)

}

trait TellRangeModel {

  implicit def tell_rangeAs[R, I]: Tell[RangeAs[R, I], RangeModel[R, I]] =
    Tell.tell_monops2[RangeAs, R, I, (I, I), RangeModel[R, I]](RangeModel.rangeAs)

}

trait TellLowPriorityImplicits {
  import Tell.TellOps

  implicit def tell_usingOrdModel[A[_], R, V, I](implicit t: Tell[A[I], OrdModel[I]]) =
    Tell.tell_on[A[I], Model[R, V, I], OrdModel[I]](Model.ord)

  implicit def tell_usingIndexModel[A[_], R, V, I](implicit t: Tell[A[I], IndexModel[I]]) =
    Tell.tell_on[A[I], Model[R, V, I], IndexModel[I]](Model.index)

  implicit def tell_usingStrandModel[A[_], R, V, I](implicit t: Tell[A[R], StrandModel[R]]) =
    Tell.tell_on[A[R], Model[R, V, I], StrandModel[R]](Model.str)

  implicit def tell_usingLengthModel[A[_], R, V, I](implicit t: Tell[A[R], LengthModel[R]]) =
    Tell.tell_on[A[R], Model[R, V, I], LengthModel[R]](Model.length)

  implicit def tell_usingRangeModel[A[_, _], R, V, I](implicit t: Tell[A[R, I], RangeModel[R, I]]) =
    Tell.tell_on[A[R, I], Model[R, V, I], RangeModel[R, I]](Model.range)

}

trait TellLowLowPriorityImplicits {
  import Tell.TellOps

  implicit def tell_viModel[A[_], R, V, I]
  (implicit avI: Interpretation[A[V], A[I], Model[R, V, I]], t: Tell[A[I], Model[R, V, I]])
  : Tell[A[V], Model[R, V, I]] = new Tell[A[V], Model[R, V, I]]
  {
    override def apply(a: A[V], m0: Model[R, V, I]): Model[R, V, I] = {
      val (a1, m1) = m0 interpretation a
      m1 tell a1
    }
  }

  implicit def tell_viModel2[A[_, _], R, V, I]
  (implicit avI: Interpretation[A[R, V], A[R, I], Model[R, V, I]], t: Tell[A[R, I], Model[R, V, I]])
  : Tell[A[R, V], Model[R, V, I]] = new Tell[A[R, V], Model[R, V, I]]
  {
    override def apply(a: A[R, V], m0: Model[R, V, I]): Model[R, V, I] = {
      val (a1, m1) = avI(a, m0)
      m1 tell a1
    }
  }

  implicit def tell_ds[A, R, V, I]
  (implicit t: Tell[A, Model[R, V, I]]) =
    Tell.tell_on[A, DerivationState[R, V, I], Model[R, V, I]](DerivationState.m0)

}