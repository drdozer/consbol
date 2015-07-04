package uk.co.turingatemyhamster.consbol

import Know.KnowOps
import Tell._

import scala.annotation.tailrec
import scala.language.higherKinds
import scalaz.Scalaz._
import scalaz.{Need, Name, StreamT}


trait DeriveLHS[A[_], T, M] {
  def apply(lhs: T, goals: Set[Any], m0: M): TrueStream[(Proof[A[T]], M)]
}

object DeriveLHS {
  import Ranges.RangesOps
  import Derive.DeriveOps

  trait Using[A[T], T, M] {
    def using(goals: Set[Any]): TrueStream[(Proof[A[T]], M)]
  }

  implicit class DeriveLHSOps[M](val _m: M) {
    def deriveLHS[A[_], T](lhs: T)(implicit d: DeriveLHS[A, T, M]) = new Using[A, T, M] {
      override def using(goals: Set[Any]): TrueStream[(Proof[A[T]], M)] =
        d(lhs, goals, _m)
    }
  }

  implicit def lhsFromRanges[A[_], R, V, I]
  (implicit
   ops: BinOp[A, R],
   d: Derive[A[R], Model[R, V, I]])
  : DeriveLHS[A, R, Model[R, V, I]] = new DeriveLHS[A, R, Model[R, V, I]] {

    override def apply(lhs: R, goals: Set[Any], m0: Model[R, V, I]): TrueStream[(Proof[A[R]], Model[R, V, I])] = {
      for {
        rhs <- m0.allRanges
        (d1, m1) <- m0 derive ops.recompose(lhs, rhs) using goals
      } yield (d1, m1)
    }
  }

}


trait Derive[A, M] {
  def apply(a: A, goals: Set[Any], m0: M): TrueStream[(Proof[A], M)]
}

object Derive extends DeriveLowPriorityImpicits {

  def apply[A, M](d: (A, Set[Any], M) => TrueStream[(Proof[A], M)]): Derive[A, M] = new Derive[A, M] {
    override def apply(a: A, goals: Set[Any], m0: M): TrueStream[(Proof[A], M)] =
      d(a, goals, m0)
  }

  implicit class TrueStreamOps[A, R, V, I](val _s: Derive[A, Model[R, V, I]]) {
    def ||(_t: Derive[A, Model[R, V, I]])
    : Derive[A, Model[R, V, I]] = new Derive[A, Model[R, V, I]] {
      override def apply(a: A, goals: Set[Any], m0: Model[R, V, I]): TrueStream[(Proof[A], Model[R, V, I])] = {
        val k1 = _s(a, goals, m0)
        k1 mappend {
          val m1 = lastModel(k1, m0)
          _t(a, goals, m1)
        }
      }
    }

    def log(msg: String): Derive[A, Model[R, V, I]] = new Derive[A, Model[R, V, I]] {
      override def apply(a: A, goals: Set[Any], m0: Model[R, V, I]): TrueStream[(Proof[A], Model[R, V, I])] = {
        println(s"${" " * goals.size}$msg [$a] ${goals contains a} $goals")
        _s(a, goals, m0)
      }
    }
  }

  def guard[A, R, V, I](d: Derive[A, Model[R, V, I]]): Derive[A, Model[R, V, I]] = new Derive[A, Model[R, V, I]] {
    override def apply(a: A, goals: Set[Any], m0: Model[R, V, I]): TrueStream[(Proof[A], Model[R, V, I])] =
      if(goals contains a)
        StreamT.empty
      else
        d(a, goals + a, m0)
  }

  def known[A[_], T, R, V, I]
  (implicit k: Know[A, T, Model[R, V, I]])
  : Derive[A[T], Model[R, V, I]] = new Derive[A[T], Model[R, V, I]] {
    override def apply(a: A[T], goals: Set[Any], m0: Model[R, V, I]): TrueStream[(Proof[A[T]], Model[R, V, I])] =
      m0 know a map (_ -> m0)
  }

  implicit class DeriveOps[M](val _m: M) {

    trait Using[A, M] {
      def using(goals: Set[Any]): TrueStream[(Proof[A], M)]
    }

    def derive[A](a: A)(implicit d: Derive[A, M]) = new Using[A, M] {
      def using(goals: Set[Any]) =
        d(a, goals, _m)
    }

    def derive0[A](a: A)(implicit d: Derive[A, M]): TrueStream[(Proof[A], M)] =
      d(a, Set(), _m)
  }

  def lastModel[A, M](str: TrueStream[(A, M)], m0: M): M =
    (str.foldLeft(m0) { case (_, (_, m1)) => m1 }).value

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
  : Derive[A[V], Model[R, V, I]] = new Derive[A[V], Model[R, V, I]] {

    override def apply(a: A[V], goals: Set[Any], m0: Model[R, V, I]): TrueStream[(Proof[A[V]], Model[R, V, I])] = {
      val (a1, m1) = m0 interpretation a
      m1 derive a1 using goals map { case (p, m) => Interpreted(a, p) -> m }
    }

  }


}
