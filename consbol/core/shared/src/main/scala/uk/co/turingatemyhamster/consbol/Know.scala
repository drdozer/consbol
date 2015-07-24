package uk.co.turingatemyhamster.consbol

import monocle.Lens
import uk.co.turingatemyhamster.consbol.Derive.DProof
import uk.co.turingatemyhamster.consbol.util.FuncName

import scala.language.higherKinds
import scalaz.Scalaz._
import scalaz.{StreamT, Need}

trait KnowValue[A, T, M] {
  def apply(t: T, m0: M): TrueStream[A]
}

object KnowValue extends KnowValueLowPriorityImplicits {

  implicit def knowValue_strand[R]
  : KnowValue[Strand[R], Orientation, StrandModel[R]] = new KnowValue[Strand[R], Orientation, StrandModel[R]] {
    override def apply(v: Orientation, m0: StrandModel[R]): TrueStream[Strand[R]] =
      TrueStream(m0.strand.filter(_._2 contains v) map (ro => Strand(ro._1, v)))
  }

}

trait KnowValueLowPriorityImplicits {

  implicit def knowValue_fromModel[A, L, R, V, I](implicit k: KnowValue[A, L, StrandModel[R]])
  : KnowValue[A, L, Model[R, V, I]] = new KnowValue[A, L, Model[R, V, I]] {
    override def apply(v: L, m0: Model[R, V, I]): TrueStream[A] =
      k(v, m0.str)
  }

}

trait KnowValue2[A, U, M] {
  def apply(t: U, m0: M): TrueStream[A]
}

object KnowValue2 extends KnowValue2LowPriorityImplicits {

  implicit def knowValue_rangeAs[R, V]
  : KnowValue2[RangeAs[R, V], (V, V), RangeModel[R, V]] = new KnowValue2[RangeAs[R, V], (V, V), RangeModel[R, V]] {
    override def apply(vv: (V, V), m0: RangeModel[R, V]): TrueStream[RangeAs[R, V]] =
      TrueStream(m0.rangeAs.filter(_._2 contains vv) map (ro => RangeAs(ro._1, vv._1, vv._2)))
  }

}

trait KnowValue2LowPriorityImplicits {

  implicit def knowValue_fromModel[A, R, V, I](implicit k: KnowValue2[A, (I, I), RangeModel[R, I]])
  : KnowValue2[A, (I, I), Model[R, V, I]] = new KnowValue2[A, (I, I), Model[R, V, I]] {
    override def apply(ii: (I, I), m0: Model[R, V, I]): TrueStream[A] =
      k(ii, m0.range)
  }

}
trait Know[A[_], T, M] {
  def apply(a: A[T], m0: M): TrueStream[DProof[A[T]]]

  def byLHS(lhs: T, m0: M): TrueStream[DProof[A[T]]]

  def byRHS(rhs: T, m0: M): TrueStream[DProof[A[T]]]
}

object Know
  extends KnowOrdModel
  with KnowIndexModel
  with KnowStrandModel
  with KnowLengthModel
  with KnowLowPriorityImplicits
  with KnowLowLowPriorityImplicits
{

  implicit class KnowOps[M](val m: M) {
    def know[A[_], T](a: A[T])(implicit k: Know[A, T, M]) =
      k(a, m)

    def knowLHS[A[_], T](lhs: T)(implicit k: Know[A, T, M]) =
      k.byLHS(lhs, m)

    def knowRHS[A[_], T](rhs: T)(implicit k: Know[A, T, M]) =
      k.byRHS(rhs, m)
  }

  implicit class Know2Ops[M](val m: M) {
    def know[A[_, _], T, U](a: A[T, U])(implicit k: Know2[A, T, U, M]) =
      k(a, m)

    def knowLHS[A[_, _], T, U](lhs: T)(implicit k: Know2[A, T, U, M]) =
      k.byLHS(lhs, m)

    def knowRHS[A[_, _], T, U](rhs: T)(implicit k: Know2[A, T, U, M]) =
      k.byRHS(rhs, m)
  }

  def know_on[A[_], T, M1, M2](φ: Lens[M1, M2])(implicit k: Know[A, T, M2]) = new Know[A, T, M1] {
    override def apply(a: A[T], m0: M1): TrueStream[DProof[A[T]]] = k(a, φ.get(m0))

    override def byLHS(lhs: T, m0: M1): TrueStream[DProof[A[T]]] = k.byLHS(lhs, φ.get(m0))

    override def byRHS(rhs: T, m0: M1): TrueStream[DProof[A[T]]] = k.byRHS(rhs, φ.get(m0))
  }

  def know_binop[A[_], T, M](φ: Lens[M, Set[(T, T)]])(implicit op: BinOp[A, T], fn: FuncName) = new Know[A, T, M] {
    override def apply(a: A[T], m0: M): TrueStream[DProof[A[T]]] =
      StreamT apply Need {
        if(φ get m0 contains (op decompose a))
          singleton(DProof.fact(a))
        else
          singleton(Disproof.failure(a))
      }

    override def byLHS(lhs: T, m0: M): TrueStream[DProof[A[T]]] =
      TrueStream(φ get m0 filter (_._1 == lhs) map {
        case (_, r) => DProof.fact(op.recompose(lhs, r))
      })

    override def byRHS(rhs: T, m0: M): TrueStream[DProof[A[T]]] =
      TrueStream(φ get m0 filter (_._2 == rhs) map {
        case (l, _) => DProof.fact(op.recompose(l, rhs))
      })
  }

  def know_monop[A[_], T, U, M](φ: Lens[M, Map[T, Set[U]]])(implicit op: MonOp[A, T, U], fn: FuncName) = new Know[A, T, M] {
    override def apply(a: A[T], m0: M): TrueStream[DProof[A[T]]] =
      StreamT apply Need {
        val (t, u) = op.decompose(a)
        φ get m0 get t match {
          case Some(us) if us contains u =>
            singleton(DProof.fact(a))
          case _ =>
            singleton(Disproof.failure(a))
        }
      }

    override def byLHS(lhs: T, m0: M): TrueStream[DProof[A[T]]] =
      φ get m0 get lhs match {
        case Some(us) =>
        TrueStream(us map (u => DProof.fact(op.recompose(lhs, u))))
      case _ =>
        StreamT.empty
    }

    override def byRHS(rhs: T, m0: M): TrueStream[DProof[A[T]]] =
      StreamT.empty
  }
}

trait KnowOrdModel {

  implicit def know_lt[I](implicit fn: FuncName) =
    Know.know_binop[LT, I, OrdModel[I]](OrdModel.lt)

  implicit def know_lt_eq[I](implicit fn: FuncName) =
    Know.know_binop[LT_EQ, I, OrdModel[I]](OrdModel.lt_eq)

  implicit def know_not_eq[I](implicit fn: FuncName) =
    Know.know_binop[NOT_EQ, I, OrdModel[I]](OrdModel.not_eq)

  implicit def know_eq[V, I](implicit fn: FuncName) // needs to be custom
  : Know[EQ, I, InterpModel[V, I]] = new Know[EQ, I, InterpModel[V, I]] {
    override def apply(a: EQ[I], m0: InterpModel[V, I]): TrueStream[DProof[EQ[I]]] =
      StreamT apply Need {
        if(a.lhs == a.rhs)
          singleton(DProof.fact(a))
        else
          singleton(Disproof.failure(a))
      }

    override def byLHS(lhs: I, m0: InterpModel[V, I]): TrueStream[DProof[EQ[I]]] =
      StreamT apply Need {
        if(m0.eq.contains(lhs))
          singleton(DProof.fact(EQ(lhs, lhs)))
        else
          StreamT.Done
      }

    override def byRHS(rhs: I, m0: InterpModel[V, I]): TrueStream[DProof[EQ[I]]] =
      StreamT apply Need {
        if(m0.eq.contains(rhs))
          singleton(DProof.fact(EQ(rhs, rhs)))
        else
          StreamT.Done
      }
  }

}

trait KnowIndexModel {

  implicit def know_at[I](implicit fn: FuncName) =
    Know.know_monop[AT, I, Int, IndexModel[I]](IndexModel.at)

  implicit def know_suc[I](implicit fn: FuncName) =
    Know.know_binop[Suc, I, IndexModel[I]](IndexModel.suc)

}

trait KnowStrandModel {

  implicit def know_strand[R](implicit fn: FuncName) =
    Know.know_monop[Strand, R, Orientation, StrandModel[R]](StrandModel.strand)

  implicit def know_same_strand_as[R](implicit fn: FuncName) =
    Know.know_binop[SameStrandAs, R, StrandModel[R]](StrandModel.same_strand_as)

  implicit def know_different_strand_to[R](implicit fn: FuncName) =
    Know.know_binop[DifferentStrandTo, R, StrandModel[R]](StrandModel.different_strand_to)
}

trait KnowLengthModel {

  implicit def know_length[R](implicit fn: FuncName) =
    Know.know_monop[Length, R, Int, LengthModel[R]](LengthModel.length)

}

trait KnowLowPriorityImplicits {
  
  import Know.KnowOps

  implicit def know_dsFromModel[A[_], T, R, V, I](implicit k: Know[A, T, Model[R, V, I]]) =
    Know.know_on[A, T, DerivationState[R, V, I], Model[R, V, I]](DerivationState.m0)

  implicit def know_modelFromInterp[A[_], R, V, I](implicit k: Know[A, I, InterpModel[V, I]]) =
    Know.know_on[A, I, Model[R, V, I], InterpModel[V, I]](Model.i)

  implicit def know_modelFromOrd[A[_], R, V, I](implicit k: Know[A, I, OrdModel[I]]) =
    Know.know_on[A, I, Model[R, V, I], OrdModel[I]](Model.ord)

  implicit def know_modelFromIndex[A[_], R, V, I](implicit k: Know[A, I, IndexModel[I]]) =
    Know.know_on[A, I, Model[R, V, I], IndexModel[I]](Model.index)

  implicit def know_modelFromStrand[A[_], R, V, I](implicit k: Know[A, R, StrandModel[R]]) =
    Know.know_on[A, R, Model[R, V, I], StrandModel[R]](Model.str)

  implicit def know_modelFromLength[A[_], R, V, I](implicit k: Know[A, R, LengthModel[R]]) =
    Know.know_on[A, R, Model[R, V, I], LengthModel[R]](Model.length)

}

trait KnowLowLowPriorityImplicits {

  import Know.KnowOps
  import Interpretation.InterpretationOps

  implicit def know_usingInterpretation[A[_], R, V, I]
  (implicit
   inV: Interpretation[V, I, Model[R, V, I]],
   inA: Interpretation[A[V], A[I], Model[R, V, I]],
   k: Know[A, I, Model[R, V, I]])
  : Know[A, V, Model[R, V, I]] = new Know[A, V, Model[R, V, I]] {
    override def apply(a: A[V], m0: Model[R, V, I]): TrueStream[DProof[A[V]]] = {
      val (a1, m1) = m0 interpretation a
      m1 know a1 map (p => DProof.interpreted(a, p))
    }

    override def byLHS(lhs: V, m0: Model[R, V, I]): TrueStream[DProof[A[V]]] = {
      val (lhs1, m1) = m0 interpretation lhs
      m1 knowLHS lhs1 map (dp => dp.fold(
        d => DProof.interpreted((m1 coimage d.goal).get, d),
        p => DProof.interpreted((m1 coimage p.goal).get, p)))
    }

    override def byRHS(rhs: V, m0: Model[R, V, I]): TrueStream[DProof[A[V]]] = {
      val (rhs1, m1) = m0 interpretation rhs
      m1 knowRHS rhs1 map (dp => dp.fold(
        d => DProof.interpreted((m1 coimage d.goal).get, d),
        p => DProof.interpreted((m1 coimage p.goal).get, p)))
    }
  }

}


trait Know2[A[_, _], T, U, M] {
  def apply(a: A[T, U], m0: M): TrueStream[DProof[A[T, U]]]

  def byLHS(lhs: T, m0: M): TrueStream[DProof[A[T, U]]]

  def byRHS(rhs: T, m0: M): TrueStream[DProof[A[T, U]]]
}

object Know2
  extends Know2RangeModel
  with Know2LowPriorityImplicits
{

  def know_on[A[_, _], T, U, M1, M2](φ: Lens[M1, M2])(implicit k: Know2[A, T, U, M2]) = new Know2[A, T, U, M1] {
    override def apply(a: A[T, U], m0: M1): TrueStream[DProof[A[T, U]]] = k(a, φ.get(m0))

    override def byLHS(lhs: T, m0: M1): TrueStream[DProof[A[T, U]]] = k.byLHS(lhs, φ.get(m0))

    override def byRHS(rhs: T, m0: M1): TrueStream[DProof[A[T, U]]] = k.byRHS(rhs, φ.get(m0))
  }

  def know_monop[A[_, _], T, U, X, M](φ: Lens[M, Map[T, Set[X]]])
                                     (implicit op: MonOp2[A, T, U, X], fn: FuncName) = new Know2[A, T, U, M] {
    override def apply(a: A[T, U], m0: M): TrueStream[DProof[A[T, U]]] =
      StreamT apply Need {
        val (t, u) = op.decompose(a)
        φ get m0 get t match {
          case Some(us) if us contains u =>
            singleton(DProof.fact(a))
          case _ =>
            singleton(Disproof.failure(a))
        }
      }

    override def byLHS(lhs: T, m0: M): TrueStream[DProof[A[T, U]]] =
      φ get m0 get lhs match {
        case Some(us) =>
          TrueStream(us map (u => DProof.fact(op.recompose(lhs, u))))
        case _ =>
          StreamT.empty
      }

    override def byRHS(rhs: T, m0: M): TrueStream[DProof[A[T, U]]] =
      StreamT.empty
  }

}


trait Know2RangeModel {

  implicit def know_rangeAs[R, I](implicit fn: FuncName) =
    Know2.know_monop[RangeAs, R, I, (I, I), RangeModel[R, I]](RangeModel.rangeAs)

}

trait Know2LowPriorityImplicits {

  implicit def know_usingInterpretation[A[_, _], T, R, V, I]
  (implicit
   inV: Interpretation[V, I, Model[R, V, I]],
   inA: Interpretation[A[T, V], A[T, I], Model[R, V, I]],
   k: Know2[A, T, I, Model[R, V, I]]) = new Know2[A, T, V, Model[R, V, I]]
  {
    override def apply(a: A[T, V], m0: Model[R, V, I]): TrueStream[DProof[A[T, V]]] = {
      val (a1, m1) = inA.apply(a, m0)
      k(a1, m1) map (p => DProof.interpreted2(a, p))
    }

    override def byLHS(lhs: T, m0: Model[R, V, I]): TrueStream[DProof[A[T, V]]] = ???

    override def byRHS(rhs: T, m0: Model[R, V, I]): TrueStream[DProof[A[T, V]]] = ???
  }

  implicit def know_dsFromModel[A[_, _], T, U, R, V, I](implicit k: Know2[A, T, U, Model[R, V, I]]) =
    Know2.know_on[A, T, U, DerivationState[R, V, I], Model[R, V, I]](DerivationState.m0)

  implicit def know_modelFromRange[A[_, _], R, V, I](implicit k: Know2[A, R, I, RangeModel[R, I]]) =
    Know2.know_on[A, R, I, Model[R, V, I], RangeModel[R, I]](Model.range)

}