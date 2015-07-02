package uk.co.turingatemyhamster.consbol

import scala.language.higherKinds
import scalaz.{Need, Name, StreamT}
import scalaz.StreamT.{Done}


trait Know[A[_], T, M] {
  def apply(a: A[T], m0: M): TrueStream[Proof[A[T]]]

  def byLHS(lhs: T, m0: M): TrueStream[Proof[A[T]]]
}

object Know
  extends KnowOrdModel
  with KnowIndexModel
  with KnowStrandModel
  with KnowLowPriorityImplicits
  with KnowLowLowPriorityImplicits
{

  implicit class KnowOps[M](val m: M) {
    def know[A[_], T](a: A[T])(implicit k: Know[A, T, M]) =
      k(a, m)

    def knowLHS[A[_], T](lhs: T)(implicit k: Know[A, T, M]) =
      k.byLHS(lhs, m)
  }

}

trait KnowOrdModel {

  implicit def know_lt[I]: Know[LT, I, OrdModel[I]] = new Know[LT, I, OrdModel[I]] {
    override def apply(a: LT[I], m0: OrdModel[I]): TrueStream[Proof[LT[I]]] =
      StreamT apply Need {
        if(m0.lt(a.lhs -> a.rhs))
          singleton(Fact(a) : Proof[LT[I]])
        else
          Done
      }

    override def byLHS(lhs: I, m0: OrdModel[I]): TrueStream[Proof[LT[I]]] =
      TrueStream(m0.lt.filter(_._1 == lhs).map {
        case (l, r) => Fact(LT(l, r))
      })
  }

  implicit def know_lt_eq[I]: Know[LT_EQ, I, OrdModel[I]] = new Know[LT_EQ, I, OrdModel[I]] {
    override def apply(a: LT_EQ[I], m0: OrdModel[I]): TrueStream[Proof[LT_EQ[I]]] =
      StreamT apply Need {
        if(m0.lt_eq(a.lhs -> a.rhs))
          singleton(Fact(a))
        else
          Done
      }

    override def byLHS(lhs: I, m0: OrdModel[I]): TrueStream[Proof[LT_EQ[I]]] =
      TrueStream(m0.lt_eq.filter(_._1 == lhs).map {
        case (l, r) => Fact(LT_EQ(l, r))
      })
  }

  implicit def know_not_eq[I]: Know[NOT_EQ, I, OrdModel[I]] = new Know[NOT_EQ, I, OrdModel[I]] {
    override def apply(a: NOT_EQ[I], m0: OrdModel[I]): TrueStream[Proof[NOT_EQ[I]]] = {
      StreamT apply Need {
        if(m0.not_eq(a.lhs -> a.rhs))
          singleton(Fact(a))
        else
          Done
      }
    }

    override def byLHS(lhs: I, m0: OrdModel[I]): TrueStream[Proof[NOT_EQ[I]]] =
      TrueStream(m0.not_eq.filter(_._1 == lhs).map {
        case (l, r) => Fact(NOT_EQ(l, r))
      })
  }

  implicit def know_eq[V, I]: Know[EQ, I, InterpModel[V, I]] = new Know[EQ, I, InterpModel[V, I]] {
    override def apply(a: EQ[I], m0: InterpModel[V, I]): TrueStream[Proof[EQ[I]]] =
      StreamT apply Need {
        if(a.lhs == a.rhs)
          singleton(Fact(a))
        else
          Done
      }

    override def byLHS(lhs: I, m0: InterpModel[V, I]): TrueStream[Proof[EQ[I]]] =
      StreamT apply Need {
        if(m0.eq.contains(lhs))
          singleton(Fact(EQ(lhs, lhs)))
        else
          Done
      }
  }

}

trait KnowIndexModel {

  implicit def know_at[I]: Know[AT, I, IndexModel[I]] = new Know[AT, I, IndexModel[I]] {
    override def byLHS(lhs: I, m0: IndexModel[I]): TrueStream[Proof[AT[I]]] =
      m0.at.get(lhs) match {
        case Some(is) =>
          TrueStream(is map (loc => Fact(AT(lhs, loc))))
        case None =>
          StreamT.empty
      }

    override def apply(a: AT[I], m0: IndexModel[I]): TrueStream[Proof[AT[I]]] =
      StreamT apply Need {
        m0.at.get(a.point) match {
          case Some(is) if is contains a.loc =>
            singleton(Fact(a))
          case _ =>
            Done
        }
      }
  }

}

trait KnowStrandModel {

  implicit def know_strand[R]: Know[Strand, R, StrandModel[R]] = new Know[Strand, R, StrandModel[R]] {
    override def byLHS(lhs: R, m0: StrandModel[R]): TrueStream[Proof[Strand[R]]] =
      m0.strand.get(lhs) match {
        case Some(ss) =>
          TrueStream(ss map (s => Fact(Strand(lhs, s))))
        case None =>
          StreamT.empty
      }

    override def apply(a: Strand[R], m0: StrandModel[R]): TrueStream[Proof[Strand[R]]] =
      StreamT apply Need {
        m0.strand.get(a.range) match {
          case Some(ss) if ss contains a.orient =>
            singleton(Fact(a))
          case _ =>
            Done
        }
      }
  }

  implicit def know_same_strand_as[R]: Know[SameStrandAs, R, StrandModel[R]] = new Know[SameStrandAs, R, StrandModel[R]] {
    override def byLHS(lhs: R, m0: StrandModel[R]): TrueStream[Proof[SameStrandAs[R]]] =
      TrueStream(m0.same_strand_as.filter(_._1 == lhs) map { case (l, r) => Fact(SameStrandAs(l, r)) })

    override def apply(a: SameStrandAs[R], m0: StrandModel[R]): TrueStream[Proof[SameStrandAs[R]]] =
      StreamT apply Need {
        if(m0.same_strand_as contains (a.lhs -> a.rhs))
          singleton(Fact(a))
        else
          Done
      }
  }
}

trait KnowLowPriorityImplicits {
  
  import Know.KnowOps

  implicit def know_modelFromInterp[A[_], R, V, I]
  (implicit k: Know[A, I, InterpModel[V, I]])
  : Know[A, I, Model[R, V, I]] = new Know[A, I, Model[R, V, I]] {
    override def apply(a: A[I], m0: Model[R, V, I]): TrueStream[Proof[A[I]]] =
      m0.i know a

    override def byLHS(lhs: I, m0: Model[R, V, I]): TrueStream[Proof[A[I]]] =
      m0.i knowLHS lhs
  }

  implicit def know_modelFromOrd[A[_], R, V, I]
  (implicit k: Know[A, I, OrdModel[I]])
  : Know[A, I, Model[R, V, I]] = new Know[A, I, Model[R, V, I]] {
    override def apply(a: A[I], m0: Model[R, V, I]): TrueStream[Proof[A[I]]] =
      m0.ord know a

    override def byLHS(lhs: I, m0: Model[R, V, I]): TrueStream[Proof[A[I]]] =
      m0.ord knowLHS lhs
  }

  implicit def know_modelFromIndex[A[_], R, V, I]
  (implicit k: Know[A, I, IndexModel[I]])
  : Know[A, I, Model[R, V, I]] = new Know[A, I, Model[R, V, I]] {
    override def apply(a: A[I], m0: Model[R, V, I]): TrueStream[Proof[A[I]]] =
      m0.index know a

    override def byLHS(lhs: I, m0: Model[R, V, I]): TrueStream[Proof[A[I]]] =
      m0.index knowLHS lhs
  }

  implicit def know_modelFromStrand[A[_], R, V, I]
  (implicit k: Know[A, R, StrandModel[R]])
  : Know[A, R, Model[R, V, I]] = new Know[A, R, Model[R, V, I]] {
    override def apply(a: A[R], m0: Model[R, V, I]): TrueStream[Proof[A[R]]] =
      m0.str know a

    override def byLHS(lhs: R, m0: Model[R, V, I]): TrueStream[Proof[A[R]]] =
      m0.str knowLHS lhs
  }

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
    override def apply(a: A[V], m0: Model[R, V, I]): TrueStream[Proof[A[V]]] = {
      val (a1, m1) = m0 interpretation a
      m1 know a1 map (p => Interpreted(a, p))
    }

    override def byLHS(lhs: V, m0: Model[R, V, I]): TrueStream[Proof[A[V]]] = {
      val (lhs1, m1) = m0 interpretation lhs
      m1 knowLHS lhs1 map (p => Interpreted(m1 coimage p.result get, p))
    }
  }

//  implicit def know_usingAtInterpretation[V, I]
//  (implicit
//   inV: Interpretation[V, I, Model[V, I]],
//   inA: Interpretation[AT[V], AT[I], Model[V, I]],
//   k: Know[AT, I, Model[V, I]])
//   : Know[AT, Symbol, Model[Symbol, String]] = new Know[AT, Symbol, Model[Symbol, String]] {
//    override def apply(a: AT[Symbol], m0: Model[Symbol, String]): TrueStream[Proof[AT[Symbol]]] = {
//      val (pointI, m1) = m0 interpretation a.point
//      m1 know AT(pointI, a.loc) map (p => Interpreted(a, p))
//    }
//
//    override def byLHS(lhs: Symbol, m0: Model[Symbol, String]): TrueStream[Proof[AT[Symbol]]] = {
//      val (pointI, m1) = m0 interpretation lhs
//      m1 knowLHS pointI map (p => Interpreted(AT(lhs, p)))
//    }
//  }
}
