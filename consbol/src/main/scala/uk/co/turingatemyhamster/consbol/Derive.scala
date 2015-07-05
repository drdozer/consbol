package uk.co.turingatemyhamster.consbol

import Know.KnowOps
import Tell._
import fastparse.FuncName
import uk.co.turingatemyhamster.consbol.Derive.DerivationResults

import scala.annotation.tailrec
import scala.language.higherKinds
import scalaz.Scalaz._
import scalaz.{Need, Name, StreamT}

case class DerivationState[M](cuts: Set[Any] = Set.empty,
                              refuted: Map[Set[Any], Set[Any]] = Map.empty,
                              m0: M)
{
  def withModel(m1: M): DerivationState[M] = copy(m0 = m1)
  def withCuts(cs: Set[Any]): DerivationState[M] = copy(cuts = cs)
  def withCut(c: Any): DerivationState[M] = copy(cuts = cuts + c)
}

trait DeriveLHS[A[_], T, M] {
  def apply(lhs: T, ds: DerivationState[M]): DerivationResults[A[T], M]
}

object DeriveLHS {
  import Ranges.RangesOps
  import Derive.DeriveOps

  implicit class DeriveLHSOps[M](_ds0: DerivationState[M]) {
    def deriveLHS[A[_], T](lhs: T)(implicit dlhs: DeriveLHS[A, T, M]) =
      dlhs(lhs, _ds0)
  }

  implicit def lhsFromRanges[A[_], R, V, I]
  (implicit
   ops: BinOp[A, R],
   d: Derive[A[R], Model[R, V, I]])
  : DeriveLHS[A, R, Model[R, V, I]] = new DeriveLHS[A, R, Model[R, V, I]] {

    override def apply(lhs: R, ds0: DerivationState[Model[R, V, I]])
    : DerivationResults[A[R], Model[R, V, I]] = {
      for {
        rhs <- ds0.allRanges
        dr1 <- ds0 derive ops.recompose(lhs, rhs)
      } yield dr1
    }
  }

}


trait Derive[A, M] {
  def apply(a: A, ds: DerivationState[M]): DerivationResults[A, M]
}

object Derive extends DeriveLowPriorityImpicits {

  type DerivationResult[A, M] = (Proof[A], DerivationState[M])
  type DerivationResults[A, M] = TrueStream[DerivationResult[A, M]]

  def apply[A, M](d: (A, DerivationState[M]) => DerivationResults[A, M]): Derive[A, M] = new Derive[A, M] {
    override def apply(a: A, ds0: DerivationState[M]): DerivationResults[A, M] =
      d(a, ds0)
  }

  implicit class TrueStreamOps[A, R, V, I](val _s: Derive[A, Model[R, V, I]]) {
    def ||(_t: Derive[A, Model[R, V, I]]) = Derive[A, Model[R, V, I]] {
      (a: A, ds0: DerivationState[Model[R, V, I]]) => {
        val k1 = _s(a, ds0)
        k1 mappend {
          val m1 = lastModel(k1, ds0.m0)
          _t(a, ds0 withModel m1)
        }
      }
    }

    def log(implicit fn: FuncName): Derive[A, Model[R, V, I]] = Derive[A, Model[R, V, I]] {
      (a: A,  ds0: DerivationState[Model[R, V, I]]) => {
        println(s"${" " * ds0.cuts.size}${fn.name} [$a] ${ds0.cuts contains a} ${ds0.cuts} ${ds0.refuted}")
        _s(a, ds0)
      }
    }
  }

  def guard[A, R, V, I](d: Derive[A, Model[R, V, I]]) = Derive[A, Model[R, V, I]] {
    (a: A, ds0: DerivationState[Model[R, V, I]]) =>
      if(ds0.cuts contains a)
        StreamT.empty
      else
        d(a, ds0 withCut a)
  }

  def known[A[_], T, R, V, I]
  (implicit k: Know[A, T, Model[R, V, I]]) = Derive[A[T], Model[R, V, I]] {
    (a: A[T], ds0: DerivationState[Model[R, V, I]]) =>
      ds0.m0 know a map (_ -> ds0)
  }

  implicit class DeriveOps[M](val _ds0: DerivationState[M]) {
    def derive[A](a: A)(implicit d: Derive[A, M]) =
      d(a, _ds0)
  }

  def lastModel[A, M](str: DerivationResults[A, M], m0: M): M =
    (str.foldLeft(m0) { case (_, (_, ds)) => ds.m0 }).value

  implicit def derive_lt[R, V, I]
  (implicit k: Know[LT, I, Model[R, V, I]])
  : Derive[LT[I], Model[R, V, I]] = DeriveOrdModel.`a < b -| ?`

  implicit def derive_lt_eq[R, V, I]
  (implicit kLtEq: Know[LT_EQ, I, Model[R, V, I]])
  : Derive[LT_EQ[I], Model[R, V, I]] = DeriveOrdModel.`a <= b -| ?`

  implicit def derive_eq[R, V, I]
  (implicit t: Tell[EQ[I], Model[R, V, I]]) // fixme: not sure why t is needed here but nowhere else
  : Derive[EQ[I], Model[R, V, I]] = DeriveOrdModel.`a = b -| ?`

  implicit def derive_not_eq[R, V, I]
  (implicit k: Know[NOT_EQ, I, Model[R, V, I]])
  : Derive[NOT_EQ[I], Model[R, V, I]] = DeriveOrdModel.`a != b -| ?`

  implicit def derive_at[R, V, I]: Derive[AT[I], Model[R, V, I]] = DeriveIndexModel.`a @ i -| ?`

  implicit def strand[R, V, I]
  : Derive[Strand[R], Model[R, V, I]] = DeriveStrandModel.`±r -| ?`

  implicit def derive_same_strand_as[R, V, I]
  : Derive[SameStrandAs[R], Model[R, V, I]] = DeriveStrandModel.`r±s -| ?`

  implicit def derive_different_strand_to[R, V, I]
  : Derive[DifferentStrandTo[R], Model[R, V, I]] = DeriveStrandModel.`r∓s -| ?`
}

trait DeriveLowPriorityImpicits {

  import Derive.DeriveOps
  import Interpretation.InterpretationOps

  implicit def derive_usingInterpretation[A[_], R, V, I]
  (implicit
   in: Interpretation[A[V], A[I], Model[R, V, I]],
   d: Derive[A[I], Model[R, V, I]])
  : Derive[A[V], Model[R, V, I]] = Derive[A[V], Model[R, V, I]] {
     (a: A[V], ds0: DerivationState[Model[R, V, I]]) => {
      val (a1, ds1) = ds0 interpretation a
      ds1 derive a1 map { case (p, ds) => Interpreted(a, p) -> ds }
    }
  }

}
