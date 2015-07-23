package uk.co.turingatemyhamster.consbol

import uk.co.turingatemyhamster.consbol.Derive.DProof
import uk.co.turingatemyhamster.consbol.util.FuncName

import scala.language.higherKinds
import scalaz.Scalaz._
import scalaz.{StreamT, Need}

trait KnowValue[A, V, M] {
  def apply(v: V, m0: M): TrueStream[A]
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
  with KnowRangeModel
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

}

trait KnowOrdModel {

  implicit def know_lt[I](implicit fn: FuncName)
  : Know[LT, I, OrdModel[I]] = new Know[LT, I, OrdModel[I]] {
    override def apply(a: LT[I], m0: OrdModel[I]): TrueStream[DProof[LT[I]]] =
      StreamT apply Need {
        if(m0.lt(a.lhs -> a.rhs))
          singleton(DProof.fact(a))
        else
          singleton(Disproof.failure(a))
      }

    override def byLHS(lhs: I, m0: OrdModel[I]): TrueStream[DProof[LT[I]]] =
      TrueStream(m0.lt.filter(_._1 == lhs).map {
        case (l, r) => DProof.fact(LT(l, r))
      })

    override def byRHS(rhs: I, m0: OrdModel[I]): TrueStream[DProof[LT[I]]] =
      TrueStream(m0.lt.filter(_._2 == rhs).map {
        case (l, r) => DProof.fact(LT(l, r))
      })
  }

  implicit def know_lt_eq[I](implicit fn: FuncName)
  : Know[LT_EQ, I, OrdModel[I]] = new Know[LT_EQ, I, OrdModel[I]] {
    override def apply(a: LT_EQ[I], m0: OrdModel[I]): TrueStream[DProof[LT_EQ[I]]] =
      StreamT apply Need {
        if(m0.lt_eq(a.lhs -> a.rhs))
          singleton(DProof.fact(a))
        else
          singleton(Disproof.failure(a))
      }

    override def byLHS(lhs: I, m0: OrdModel[I]): TrueStream[DProof[LT_EQ[I]]] =
      TrueStream(m0.lt_eq.filter(_._1 == lhs).map {
        case (l, r) => DProof.fact(LT_EQ(l, r))
      })

    override def byRHS(rhs: I, m0: OrdModel[I]): TrueStream[DProof[LT_EQ[I]]] =
      TrueStream(m0.lt_eq.filter(_._2 == rhs).map {
        case (l, r) => DProof.fact(LT_EQ(l, r))
      })
  }

  implicit def know_not_eq[I](implicit fn: FuncName)
  : Know[NOT_EQ, I, OrdModel[I]] = new Know[NOT_EQ, I, OrdModel[I]] {
    override def apply(a: NOT_EQ[I], m0: OrdModel[I]): TrueStream[DProof[NOT_EQ[I]]] = {
      StreamT apply Need {
        if(m0.not_eq(a.lhs -> a.rhs))
          singleton(DProof.fact(a))
        else
          singleton(Disproof.failure(a))
      }
    }

    override def byLHS(lhs: I, m0: OrdModel[I]): TrueStream[DProof[NOT_EQ[I]]] =
      TrueStream(m0.not_eq.filter(_._1 == lhs).map {
        case (l, r) => DProof.fact(NOT_EQ(l, r))
      })

    override def byRHS(rhs: I, m0: OrdModel[I]): TrueStream[DProof[NOT_EQ[I]]] =
      TrueStream(m0.not_eq.filter(_._2 == rhs).map {
        case (l, r) => DProof.fact(NOT_EQ(l, r))
      })
  }

  implicit def know_eq[V, I](implicit fn: FuncName)
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

  implicit def know_at[I](implicit fn: FuncName)
  : Know[AT, I, IndexModel[I]] = new Know[AT, I, IndexModel[I]] {
    override def byLHS(lhs: I, m0: IndexModel[I]): TrueStream[DProof[AT[I]]] =
      m0.at.get(lhs) match {
        case Some(is) =>
          TrueStream(is map (loc => DProof.fact(AT(lhs, loc))))
        case None =>
          StreamT.empty
      }

    override def apply(a: AT[I], m0: IndexModel[I]): TrueStream[DProof[AT[I]]] =
      StreamT apply Need {
        m0.at.get(a.point) match {
          case Some(is) if is contains a.loc =>
            singleton(DProof.fact(a))
          case _ =>
            singleton(Disproof.failure(a))
        }
      }

    override def byRHS(rhs: I, m0: IndexModel[I]): TrueStream[DProof[AT[I]]] =
      StreamT.empty
  }

  implicit def know_suc[I](implicit fn: FuncName)
  : Know[Suc, I, IndexModel[I]] = new Know[Suc, I, IndexModel[I]] {
    override def byLHS(lhs: I, m0: IndexModel[I]): TrueStream[DProof[Suc[I]]] =
      TrueStream(m0.suc.filter(_._1 == lhs) map (ii => DProof.fact(Suc(ii._1, ii._2))))

    override def byRHS(rhs: I, m0: IndexModel[I]): TrueStream[DProof[Suc[I]]] =
      TrueStream(m0.suc.filter(_._2 == rhs) map (ii => DProof.fact(Suc(ii._1, ii._2))))

    override def apply(a: Suc[I], m0: IndexModel[I]): TrueStream[DProof[Suc[I]]] =
      StreamT apply Need {
        if(m0.suc(a.lhs -> a.rhs))
          singleton(DProof.fact(a))
        else
          singleton(Disproof.failure(a))
      }
  }
}

trait KnowStrandModel {

  implicit def know_strand[R](implicit fn: FuncName)
  : Know[Strand, R, StrandModel[R]] = new Know[Strand, R, StrandModel[R]] {
    override def byLHS(lhs: R, m0: StrandModel[R]): TrueStream[DProof[Strand[R]]] =
      m0.strand.get(lhs) match {
        case Some(ss) =>
          TrueStream(ss map (s => DProof.fact(Strand(lhs, s))))
        case None =>
          StreamT.empty
      }

    override def apply(a: Strand[R], m0: StrandModel[R]): TrueStream[DProof[Strand[R]]] =
      StreamT apply Need {
        m0.strand.get(a.range) match {
          case Some(ss) if ss contains a.orient =>
            singleton(DProof.fact(a))
          case _ =>
            singleton(Disproof.failure(a))
        }
      }

    override def byRHS(rhs: R, m0: StrandModel[R]): TrueStream[DProof[Strand[R]]] =
      StreamT.empty
  }

  implicit def know_same_strand_as[R](implicit fn: FuncName)
  : Know[SameStrandAs, R, StrandModel[R]] = new Know[SameStrandAs, R, StrandModel[R]] {
    override def apply(a: SameStrandAs[R], m0: StrandModel[R]): TrueStream[DProof[SameStrandAs[R]]] =
      StreamT apply Need {
        if(m0.same_strand_as contains (a.lhs -> a.rhs))
          singleton(DProof.fact(a))
        else
          singleton(Disproof.failure(a))
      }

    override def byLHS(lhs: R, m0: StrandModel[R]): TrueStream[DProof[SameStrandAs[R]]] =
      TrueStream(
        m0.same_strand_as.find(_._1 == lhs) map {
          case (l, r) => DProof.fact(SameStrandAs(l, r))
        } orElse {
          Disproof.noValue[SameStrandAs[R], R](lhs).some
        })

    override def byRHS(rhs: R, m0: StrandModel[R]): TrueStream[DProof[SameStrandAs[R]]] =
      TrueStream(
        m0.same_strand_as.find(_._2 == rhs) map {
          case (l, r) => DProof.fact(SameStrandAs(l, r))
        } orElse {
          Disproof.noValue[SameStrandAs[R], R](rhs).some
        }
      )
  }

  implicit def know_different_strand_to[R](implicit fn: FuncName)
  : Know[DifferentStrandTo, R, StrandModel[R]] = new Know[DifferentStrandTo, R, StrandModel[R]] {
    override def apply(a: DifferentStrandTo[R], m0: StrandModel[R]): TrueStream[DProof[DifferentStrandTo[R]]] =
      StreamT apply Need {
        if(m0.different_strand_to contains (a.lhs -> a.rhs))
          singleton(DProof.fact(a))
        else
          singleton(Disproof.failure(a))
      }

    override def byLHS(lhs: R, m0: StrandModel[R]): TrueStream[DProof[DifferentStrandTo[R]]] =
      TrueStream(
        m0.different_strand_to.find(_._1 == lhs) map {
          case (l, r) => DProof.fact(DifferentStrandTo(l, r))
        } orElse {
          Disproof.noValue[DifferentStrandTo[R], R](lhs).some
        }
      )

    override def byRHS(rhs: R, m0: StrandModel[R]): TrueStream[DProof[DifferentStrandTo[R]]] =
      TrueStream(
        m0.different_strand_to.find(_._2 == rhs) map {
          case (l, r) => DProof.fact(DifferentStrandTo(l, r))
        } orElse {
          Disproof.noValue[DifferentStrandTo[R], R](rhs).some
        }
      )
  }
}

trait KnowRangeModel {

  implicit def know_rangeAs[T](implicit fn: FuncName)
  : Know[RangeAs, T, RangeModel[T, T]] = new Know[RangeAs, T, RangeModel[T, T]] {
    override def byLHS(lhs: T, m0: RangeModel[T, T]): TrueStream[DProof[RangeAs[T]]] =
      TrueStream(
        m0.rangeAs.filter(_._1 == lhs) flatMap {
          case(r, abs) => abs map { case (a, b) => DProof.fact(RangeAs(r, a, b)) }
        }
      )

    override def byRHS(rhs: T, m0: RangeModel[T, T]): TrueStream[DProof[RangeAs[T]]] =
      StreamT.empty

    override def apply(a: RangeAs[T], m0: RangeModel[T, T]): TrueStream[DProof[RangeAs[T]]] =
      TrueStream(
        for {
          r <- m0.rangeAs.keys
          (a, b) <- m0.rangeAs(r)
        } yield DProof.fact(RangeAs(r, a, b))
      )
  }
}

trait KnowLengthModel {

  implicit def know_length[R](implicit fn: FuncName)
  : Know[Length, R, LengthModel[R]] = new Know[Length, R, LengthModel[R]] {
    override def apply(a: Length[R], m0: LengthModel[R]): TrueStream[DProof[Length[R]]] =
      StreamT apply Need {
        m0.length.get(a.point) match {
          case Some(ls) if ls contains a.length =>
            singleton(DProof.fact(a))
          case _ =>
            singleton(Disproof.failure(a))
        }
      }

    override def byLHS(lhs: R, m0: LengthModel[R]): TrueStream[DProof[Length[R]]] =
      m0.length.get(lhs) match {
        case Some(ls) =>
          TrueStream(ls map (len => DProof.fact(Length(lhs, len))))
        case None =>
          StreamT.empty
      }

    override def byRHS(rhs: R, m0: LengthModel[R]): TrueStream[DProof[Length[R]]] =
      StreamT.empty
  }
}

trait KnowLowPriorityImplicits {
  
  import Know.KnowOps

  def knowFrom[A[_], T, M0, M1]
  (f: M0 => M1)
  (implicit k: Know[A, T, M1])
  : Know[A, T, M0] = new Know[A, T, M0] {
    override def byLHS(lhs: T, m0: M0): TrueStream[DProof[A[T]]] =
      k.byLHS(lhs, f(m0))

    override def byRHS(rhs: T, m0: M0): TrueStream[DProof[A[T]]] =
      k.byRHS(rhs, f(m0))

    override def apply(a: A[T], m0: M0): TrueStream[DProof[A[T]]] =
      k(a, f(m0))
  }

  implicit def know_dsFromModel[A[_], T, R, V, I]
  (implicit k: Know[A, T, Model[R, V, I]])
  : Know[A, T, DerivationState[R, V, I]] =
    knowFrom(_.m0)

  implicit def know_modelFromInterp[A[_], R, V, I]
  (implicit k: Know[A, I, InterpModel[V, I]])
  : Know[A, I, Model[R, V, I]] =
    knowFrom(_.i)

  implicit def know_modelFromOrd[A[_], R, V, I]
  (implicit k: Know[A, I, OrdModel[I]])
  : Know[A, I, Model[R, V, I]] =
    knowFrom(_.ord)

  implicit def know_modelFromIndex[A[_], R, V, I]
  (implicit k: Know[A, I, IndexModel[I]])
  : Know[A, I, Model[R, V, I]] =
    knowFrom(_.index)

  implicit def know_modelFromStrand[A[_], R, V, I]
  (implicit k: Know[A, R, StrandModel[R]])
  : Know[A, R, Model[R, V, I]] =
    knowFrom(_.str)

  implicit def know_modelFromLength[A[_], R, V, I]
  (implicit k: Know[A, R, LengthModel[R]])
  : Know[A, R, Model[R, V, I]] =
    knowFrom(_.length)

  implicit def know_modelFromRange[A[_], T, I]
  (implicit k: Know[A, T, RangeModel[T, T]])
  : Know[A, T, Model[T, T, I]] =
    knowFrom(_.range)
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
