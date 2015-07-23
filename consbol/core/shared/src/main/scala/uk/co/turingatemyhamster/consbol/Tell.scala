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

  def tell_binops[A[_], T, M](l: Lens[M, Set[(T, T)]])(implicit op: BinOp[A, T]): Tell[A[T], M] = new Tell[A[T], M] {
    override def apply(a: A[T], m: M): M =
      l.modify(_ + op.decompose(a))(m)
  }

  def tell_monops[A[_], T, U, M](l: Lens[M, Map[T, Set[U]]])(implicit op: MonOp[A, T, U]): Tell[A[T], M] = new Tell[A[T], M] {
    override def apply(a: A[T], m: M): M = {
      val (t, u) = op.decompose(a)
      l.modify(m0 => m0 + (t -> (m0.getOrElse(t, Set()) + u)))(m)
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

  implicit def tell_rangeAs[T]: Tell[RangeAs[T], RangeModel[T, T]] =
    Tell.tell_monops[RangeAs, T, (T, T), RangeModel[T, T]](RangeModel.rangeAs)

}

trait TellLowPriorityImplicits {
  import Tell.TellOps

  implicit def tell_usingOrdModel[A[_], R, V, I]
  (implicit t: Tell[A[I], OrdModel[I]]): Tell[A[I], Model[R, V, I]] = new Tell[A[I], Model[R, V, I]] {
    override def apply(a: A[I], m: Model[R, V, I]): Model[R, V, I] =
      m.copy(ord = m.ord tell a)
  }

  implicit def tell_usingIndexModel[A[_], R, V, I]
  (implicit t: Tell[A[I], IndexModel[I]]): Tell[A[I], Model[R, V, I]] = new Tell[A[I], Model[R, V, I]] {
    override def apply(a: A[I], m: Model[R, V, I]): Model[R, V, I] =
      m.copy(index = m.index tell a)
  }

  implicit def tell_usingStrandModel[A[_], R, V, I]
  (implicit t: Tell[A[R], StrandModel[R]]): Tell[A[R], Model[R, V, I]] = new Tell[A[R], Model[R, V, I]] {
    override def apply(a: A[R], m: Model[R, V, I]): Model[R, V, I] =
      m.copy(str = m.str tell a)
  }

  implicit def tell_usingLengthModel[A[_], R, V, I]
  (implicit t: Tell[A[R], LengthModel[R]]): Tell[A[R], Model[R, V, I]] = new Tell[A[R], Model[R, V, I]] {
    override def apply(a: A[R], m: Model[R, V, I]): Model[R, V, I] =
      m.copy(length = m.length tell a)
  }

  implicit def tell_usingRangeModel[A[_], T, I]
  (implicit t: Tell[A[T], RangeModel[T, T]]): Tell[A[T], Model[T, T, I]] = new Tell[A[T], Model[T, T, I]] {
    override def apply(a: A[T], m: Model[T, T, I]): Model[T, T, I] =
      m.copy(range = m.range tell a)
  }
}

trait TellLowLowPriorityImplicits {
  import Tell.TellOps

  implicit def tell_viModel[A[_], R, V, I]
  (implicit avI: Interpretation[A[V], A[I], Model[R, V, I]], t: Tell[A[I], Model[R, V, I]])
  : Tell[A[V], Model[R, V, I]] = new Tell[A[V], Model[R, V, I]] {
    override def apply(a: A[V], m0: Model[R, V, I]): Model[R, V, I] = {
      val (a1, m1) = m0 interpretation a
      m1 tell a1
    }
  }

  implicit def tell_ds[A, R, V, I]
  (implicit t: Tell[A, Model[R, V, I]])
  : Tell[A, DerivationState[R, V, I]] = new Tell[A, DerivationState[R, V, I]] {
    override def apply(a: A, ds0: DerivationState[R, V, I]): DerivationState[R, V, I] = {
      ds0 withModel (ds0.m0 tell a)
    }
  }

}