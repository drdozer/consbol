package uk.co.turingatemyhamster.consbol

import Know.KnowOps
import Tell._

import scala.annotation.tailrec
import scala.language.higherKinds
import scalaz.Scalaz._
import scalaz.{Need, Name, StreamT}


trait Derive[A, M] {
  def apply(a: A, goals: Set[Any], m0: M): TrueStream[(Proof[A], M)]
}

object DeriveOrdModel {
  import Derive._

  def `? |- a < b`[R, V, I]
  (implicit k: Know[LT, I, Model[R, V, I]])
  : Derive[LT[I], Model[R, V, I]] = guard {
    known ||
      DeriveIndexModel.`a @ i, b @ j, i < j |- a < b` ||
      `a < b, b < c |- a < c` ||
      `a < b, b <= c |- a <_c` ||
      `a <= b, b < c |- a < c`
  }

  def `a < b, b <= c |- a <_c`[R, V, I] = Derive[LT[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        px <- m0.knowLHS[LT, I](a.lhs)
        x = px.result.rhs
        (p1, m1) <- m0 derive(LT_EQ(x, a.rhs), goals)
      } yield {
        Rule2("lt_<_<=", a, px, p1) -> (m1 tell a)
      }
  }

  def `a <= b, b < c |- a < c`[R, V, I] = Derive[LT[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        px <- m0.knowLHS[LT_EQ, I](a.lhs)
        x = px.result.rhs
        (p1, m1) <- m0 derive(LT(x, a.rhs), goals)
      } yield {
        Rule2("lt_<=_<", a, px, p1) -> (m1 tell a)
      }
  }

  def `a < b, b < c |- a < c`[R, V, I] = Derive[LT[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        px <- m0.knowLHS[LT, I](a.lhs)
        x = px.result.rhs
        (p1, m1) <- m0 derive(LT(x, a.rhs), goals)
      } yield {
        Rule2("lt_<_<", a, px, p1) -> (m1 tell a)
      }
    }


  def `? |- a <= b`[R, V, I]
  (implicit kLtEq: Know[LT_EQ, I, Model[R, V, I]]) = guard {
    known ||
      DeriveIndexModel.`a @ i, b @ j, i <= j |- a <= b` ||
      `a < b |- a <= b` ||
      `a <= b, b <= c |- a <= c`
  }

  def `a <= b, b <= c |- a <= c`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        px <- m0.knowLHS[LT_EQ, I](a.lhs)
        x = px.result.rhs
        (p1, m1) <- m0 derive (LT_EQ(x, a.rhs), goals)
      } yield Rule2("lt_eq_<=_<=", a, px, p1) -> (m1 tell a)
  }

  def `a < b |- a <= b`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (p, m1) <- m0 derive (LT(a.lhs, a.rhs), goals)
      } yield Rule1("lt_eq_<", a, p) -> (m1 tell a)
  }


  def `? |- a = b`[R, V, I]
  (implicit t: Tell[EQ[I], Model[R, V, I]]) = guard {
    DeriveIndexModel.`a @ i, b @ j, i = j |- a = b` ||
      `a <=b, b <= a |- a = b`
  }


  def `a <=b, b <= a |- a = b`[R, V, I]
  (implicit t: Tell[EQ[I], Model[R, V, I]]) = Derive[EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (p1, m1) <- m0 derive(LT_EQ(a.lhs, a.rhs), goals)
        (p2, m2) <- m1 derive(LT_EQ(a.rhs, a.lhs), goals)
      } yield Rule2("eq_<=_>=", a, p1, p2) -> (m2 tell a)
  }


  def `? |- a != b`[R, V, I]
  (implicit k: Know[NOT_EQ, I, Model[R, V, I]]) = guard {
    known ||
      DeriveIndexModel.`a @ i, b @ j, i != j |- a != b` ||
      `a < b |- a != b` ||
      `b < a |- a != b`
  }

  def `a < b |- a != b`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (p1, m1) <- m0 derive (LT(a.lhs, a.rhs), goals)
      } yield Rule1("not_eq_<_>", a, p1) -> (m1 tell a)
  }

  def `b < a |- a != b`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (p1, m1) <- m0 derive (LT(a.rhs, a.lhs), goals)
      } yield Rule1("not_eq_<_>", a, p1) -> (m1 tell a)
  }

}

object DeriveIndexModel {
  import Derive._

  def `? |- a @ i`[R, V, I]: Derive[AT[I], Model[R, V, I]] = guard {
    known
  }

  def `a @ i, b @ j, i < j |- a < b`[R, V, I] = Derive[LT[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc < atRHS.result.loc
      } yield
      Rule2("lt_at", a, atLHS, atRHS) -> (m0 tell a)
  }

  def `a @ i, b @ j, i <= j |- a <= b`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc <= atRHS.result.loc
      } yield
      Rule2("lt_eq_at", a, atLHS, atRHS) -> (m0 tell a)
  }

  def `a @ i, b @ j, i = j |- a = b`[R, V, I]
  (implicit
   t: Tell[EQ[I], Model[R, V, I]]) = Derive[EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc == atRHS.result.loc
      } yield
      Rule2("lt_eq_at", a, atLHS, atRHS) -> (m0 tell a)
  }

  def `a @ i, b @ j, i != j |- a != b`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc != atRHS.result.loc
      } yield
      Rule2("lt_eq_at", a, atLHS, atRHS) -> (m0 tell a)
  }

}

object DeriveStrandModel {
  import Derive._

  def `? |- ±r`[R, V, I]
  : Derive[Strand[R], Model[R, V, I]] = guard {
    known[Strand, R, R, V, I] ||
      `r±s, ±s |- ±r`
  } log "? |- ±r"

  def `? |- r±s`[R, V, I]
  : Derive[SameStrandAs[R], Model[R, V, I]] = guard {
    known[SameStrandAs, R, R, V, I] ||
    `+r, +s |- r+s` ||
    `-r, -s |- r-s` ||
    `s+r |- r+s`
  } log "? |- r±s"

  def `+r, +s |- r+s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] {
    (a, goals, m0) =>
      for {
        (s1, m1) <- m0 derive Strand(a.lhs, Orientation.+)
        (s2, m2) <- m1 derive Strand(a.rhs, Orientation.+)
        if s1.result.orient == s2.result.orient
      } yield Rule2("+r, +s |- r+s", a, s1, s2) -> (m2 tell a)
  } log "+r, +s |- r+s"

  def `-r, -s |- r-s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (s1, m1) <- m0 derive Strand(a.lhs, Orientation.-)
        (s2, m2) <- m1 derive Strand(a.rhs, Orientation.-)
        if s1.result.orient == s2.result.orient
      } yield Rule2("-r, -s |- r-s", a, s1, s2) -> (m2 tell a)
  } log "-r, -s |- r-s"

  def `s+r |- r+s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] {
    (a, goals, m0) =>
      for {
        (s1, m1) <- m0 derive SameStrandAs(a.rhs, a.lhs)
      } yield Rule1("s+r |- r+s", a, s1) -> (m1 tell a)
  } log "s+r |- r+s"

  def `r±s, ±s |- ±r`[R, V, I] = Derive[Strand[R], Model[R, V, I]] {
    (a, goal, m0) =>
      for {
        s1 <- m0.knowLHS[SameStrandAs, R](a.range)
        (s2, m1) <- m0 derive Strand(s1.result.rhs, a.orient)
      } yield Rule2("r+s, +s |- +r", a, s1, s2) -> (m1 tell a)
  } log "r±s, ±s |- ±r"
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
        println(s"${" " * goals.size}$msg $a")
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
    def derive[A](a: A, goals: Set[Any])(implicit d: Derive[A, M]): TrueStream[(Proof[A], M)] =
      d(a, goals, _m)

    def derive[A](a: A)(implicit d: Derive[A, M]): TrueStream[(Proof[A], M)] =
      d(a, Set(), _m)
  }

  def lastModel[A, M](str: TrueStream[(A, M)], m0: M): M =
    (str.foldLeft(m0) { case (_, (_, m1)) => m1 }).value

  implicit def derive_lt[R, V, I]
  (implicit k: Know[LT, I, Model[R, V, I]])
  : Derive[LT[I], Model[R, V, I]] = DeriveOrdModel.`? |- a < b`

  implicit def derive_lt_eq[R, V, I]
  (implicit kLtEq: Know[LT_EQ, I, Model[R, V, I]])
  : Derive[LT_EQ[I], Model[R, V, I]] = DeriveOrdModel.`? |- a <= b`

  implicit def derive_eq[R, V, I]
  (implicit t: Tell[EQ[I], Model[R, V, I]]) // fixme: not sure why t is needed here but nowhere else
  : Derive[EQ[I], Model[R, V, I]] = DeriveOrdModel.`? |- a = b`

  implicit def derive_not_eq[R, V, I]
  (implicit k: Know[NOT_EQ, I, Model[R, V, I]])
  : Derive[NOT_EQ[I], Model[R, V, I]] = DeriveOrdModel.`? |- a != b`

  implicit def derive_at[R, V, I]: Derive[AT[I], Model[R, V, I]] = DeriveIndexModel.`? |- a @ i`

  implicit def strand[R, V, I]
  : Derive[Strand[R], Model[R, V, I]] = DeriveStrandModel.`? |- ±r`

  implicit def derive_same_strand_as[R, V, I]
  : Derive[SameStrandAs[R], Model[R, V, I]] = DeriveStrandModel.`? |- r±s`
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
      m1 derive (a1, goals) map { case (p, m) => Interpreted(a, p) -> m }
    }

  }


}