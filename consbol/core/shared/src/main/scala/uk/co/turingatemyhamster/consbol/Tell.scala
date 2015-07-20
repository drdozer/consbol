package uk.co.turingatemyhamster.consbol

import Interpretation._

import scala.language.higherKinds


trait Tell[A, M] {
  def apply(a: A, m: M): M
}

object Tell
  extends TellOrdModel
  with TellIndexModel
  with TellStrandModel
  with TellLengthModel
  with TellLowPriorityImplicits
  with TellLowLowPriorityImplicits
{

  implicit class TellOps[M](val m: M) {
    def tell[A](a: A)(implicit t: Tell[A, M]): M = t(a, m)
  }

}

trait TellOrdModel {

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

  implicit def tell_eq[R, V, I]
  (implicit vi: InterpretationSingleton[V, I], unify: UnifyI[I])
  : Tell[EQ[V], Model[R, V, I]] = new Tell[EQ[V], Model[R, V, I]] {
    override def apply(a: EQ[V], m: Model[R, V, I]): Model[R, V, I] =
      m merge (a.lhs, a.rhs)
  }

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

  implicit def tell_at[I]: Tell[AT[I], IndexModel[I]] = new Tell[AT[I], IndexModel[I]] {
    override def apply(a: AT[I], m: IndexModel[I]): IndexModel[I] =
      m.copy(at = m.at + (a.point -> (m.at.getOrElse(a.point, Set()) + a.loc)))
  }

  implicit def tell_suc[I]: Tell[Suc[I], IndexModel[I]] = new Tell[Suc[I], IndexModel[I]] {
    override def apply(a: Suc[I], m: IndexModel[I]): IndexModel[I] =
      m.copy(suc = m.suc + (a.lhs -> a.rhs))
  }
}

trait TellStrandModel {

  implicit def tell_strand[R]: Tell[Strand[R], StrandModel[R]] = new Tell[Strand[R], StrandModel[R]] {
    override def apply(a: Strand[R], m: StrandModel[R]): StrandModel[R] =
      m.copy(strand = m.strand + (a.range -> (m.strand.getOrElse(a.range, Set()) + a.orient)))
  }

  implicit def tell_same_strand_as[R]: Tell[SameStrandAs[R], StrandModel[R]] = new Tell[SameStrandAs[R], StrandModel[R]] {
    override def apply(a: SameStrandAs[R], m: StrandModel[R]): StrandModel[R] =
      m.copy(same_strand_as = m.same_strand_as + (a.lhs -> a.rhs))
  }

  implicit def tell_different_strand_to[R]: Tell[DifferentStrandTo[R], StrandModel[R]] = new Tell[DifferentStrandTo[R], StrandModel[R]] {
    override def apply(a: DifferentStrandTo[R], m: StrandModel[R]): StrandModel[R] =
      m.copy(different_strand_to = m.different_strand_to + (a.lhs -> a.rhs))
  }
}

trait TellLengthModel {

  implicit def tell_length[R]: Tell[Length[R], LengthModel[R]] = new Tell[Length[R], LengthModel[R]] {
    override def apply(a: Length[R], m: LengthModel[R]): LengthModel[R] =
      m.copy(length = m.length + (a.point -> (m.length.getOrElse(a.point, Set()) + a.length)))
  }

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