package uk.co.turingatemyhamster.consbol

import Know.KnowOps
import Tell._

import scala.annotation.tailrec
import scala.language.higherKinds
import scalaz.Scalaz._
import scalaz.{Need, Name, StreamT}


trait Derive[A, M] {
  def apply(a: A, goals: Set[Object], m0: M): TrueStream[(Proof[A], M)]
}


object Derive extends DeriveLowPriorityImpicits {

//  private def log[consbol](msg: String) = System.err.println(msg)
  private[consbol] def log(msg: String) = {}
  
  implicit class DeriveOps[M](val _m: M) {
    def derive[A](a: A, goals: Set[Object])(implicit d: Derive[A, M]): TrueStream[(Proof[A], M)] =
      d(a, goals, _m)

    def derive[A](a: A)(implicit d: Derive[A, M]): TrueStream[(Proof[A], M)] =
      d(a, Set(), _m)
  }

  def lastModel[A, M](str: TrueStream[(A, M)], m0: M): M =
    (str.foldLeft(m0) { case (_, (_, m1)) => m1 }).value

  implicit def derive_lt[V, I]
  (implicit k: Know[LT, I, Model[V, I]])
  : Derive[LT[I], Model[V, I]] = new Derive[LT[I], Model[V, I]] {
    override def apply(a: LT[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[LT[I]], Model[V, I])] = {
      log(s"${" " * goals.size}lt $a $goals")

      if(goals contains a) {
        log(s"${" " * goals.size}lt $a - cut")
        StreamT.empty
      } else {
        val g = goals + a

        val k1 = m0 know a map (_ -> m0)
        log(s"${" " * goals.size}lt $a - know $k1")

        k1 mappend {
          val m1 = lastModel(k1, m0)
          val k2 = `lt_at` apply (a, g, m1)

          k2 mappend {
            val m2 = lastModel(k2, m1)
            val k3 = `lt_<_<` apply (a, g, m2)

            k3 mappend {
              log(s"${" " * goals.size}lt $a - < <=")

              val m3 = lastModel(k3, m2)
              val k4 = `lt_<_<=` apply (a, g, m3)

              k4 mappend {
                log(s"${" " * goals.size}lt $a - <= <")

                val m4 = lastModel(k4, m3)
                `lt_<=_<` apply (a, g, m4)
              }
            }
          }
        }
      }
    }
  }

  def `lt_<_<=`[V, I]
  : Derive[LT[I], Model[V, I]] = new Derive[LT[I], Model[V, I]] {
    override def apply(a: LT[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[LT[I]], Model[V, I])] = {
      log(s"${" " * goals.size}lt_<_<= $a $goals")

      for {
        px <- m0.knowLHS[LT, I](a.lhs)
        x = px.result.rhs
        _ = log(s"${" " * goals.size}lt_<_<= $a - trying $x")
        (p1, m1) <- m0 derive(LT_EQ(x, a.rhs), goals)
      } yield {
        log(s"${" " * goals.size}lt_<_<= $a - solution $x $p1")
        Rule2("lt_<_<=", a, px, p1) -> (m1 tell a)
      }
    }
  }

  def `lt_<=_<`[V, I]
  : Derive[LT[I], Model[V, I]] = new Derive[LT[I], Model[V, I]] {
    override def apply(a: LT[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[LT[I]], Model[V, I])] = {
      log(s"${" " * goals.size}lt_<=_< $a $goals")

      for {
        px <- m0.knowLHS[LT_EQ, I](a.lhs)
        x = px.result.rhs
        _ = log(s"${" " * goals.size}lt_<=_< $a - trying $x")
        (p1, m1) <- m0 derive(LT(x, a.rhs), goals)
      } yield {
        log(s"${" " * goals.size}lt_<=_< $a - solution $px $p1")
        Rule2("lt_<=_<", a, px, p1) -> (m1 tell a)
      }
    }
  }

  def `lt_<_<`[V, I]
  : Derive[LT[I], Model[V, I]] = new Derive[LT[I], Model[V, I]] {
    override def apply(a: LT[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[LT[I]], Model[V, I])] = {
      log(s"${" " * goals.size}lt_<_< $a $goals")
      for {
        px <- m0.knowLHS[LT, I](a.lhs)
        x = px.result.rhs
        _ = log(s"${" " * goals.size}lt_<_< $a - trying $x")
        (p1, m1) <- m0 derive(LT(x, a.rhs), goals)
      } yield {
        log(s"${" " * goals.size}lt_<_< $a - solution $px $p1")
        Rule2("lt_<_<", a, px, p1) -> (m1 tell a)
      }
    }
  }

  implicit def derive_lt_eq[V, I]
  (implicit kLtEq: Know[LT_EQ, I, Model[V, I]])
  : Derive[LT_EQ[I], Model[V, I]] = new Derive[LT_EQ[I], Model[V, I]] {
    override def apply(a: LT_EQ[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[LT_EQ[I]], Model[V, I])] = {
      log(s"${" " * goals.size}lt_eq $a $goals")

      if (goals contains a) {
        log(s"${" " * goals.size}lt_eq $a - cut")
        StreamT.empty
      } else {
        val g = goals + a
        val k1 = m0 know a map (_ -> m0)
        log(s"${" " * goals.size}lt_eq $a - know $k1")

        k1 mappend {
          val m1 = lastModel(k1, m0)
          val k2 = lt_eq_at apply (a, g, m1)

          k2 mappend {
            log(s"${" " * goals.size}lt_eq $a - <")
            val m2 = lastModel(k2, m1)
            val k3 = `lt_eq_<` apply(a, g, m2)

            k3 mappend {
              log(s"${" " * goals.size}lt_eq $a - <= =>")
              val m3 = lastModel(k3, m2)
              `lt_eq_<=_>=` apply(a, g, m3)
            }
          }
        }

      }
    }
  }

  def `lt_eq_<=_>=`[V, I]
  : Derive[LT_EQ[I], Model[V, I]] = new Derive[LT_EQ[I], Model[V, I]] {
    override def apply(a: LT_EQ[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[LT_EQ[I]], Model[V, I])] =
      for {
        px <- m0.knowLHS[LT_EQ, I](a.lhs)
        x = px.result.rhs
        (p1, m1) <- m0 derive (LT_EQ(x, a.rhs), goals)
      } yield Rule2("lt_eq_<=_<=", a, px, p1) -> (m1 tell a)
  }

  def `lt_eq_<`[V, I]
  : Derive[LT_EQ[I], Model[V, I]] = new Derive[LT_EQ[I], Model[V, I]] {
    override def apply(a: LT_EQ[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[LT_EQ[I]], Model[V, I])] =
      for {
        (p, m1) <- m0 derive (LT(a.lhs, a.rhs), goals)
      } yield Rule1("lt_eq_<", a, p) -> (m1 tell a)
  }

  implicit def derive_eq[V, I]
  (implicit t: Tell[EQ[I], Model[V, I]]) // fixme: not sure why t is needed here but nowhere else
  : Derive[EQ[I], Model[V, I]] = new Derive[EQ[I], Model[V, I]] {
    override def apply(a: EQ[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[EQ[I]], Model[V, I])] =
      if(goals contains a) {
        StreamT.empty
      } else for {
        (p1, m1) <- m0 derive (LT_EQ(a.lhs, a.rhs), goals)
        (p2, m2) <- m1 derive (LT_EQ(a.rhs, a.lhs), goals)
      } yield Rule2("eq_<=_>=", a, p1, p2) -> (m2 tell a)
  }

  implicit def derive_not_eq[V, I]
  (implicit k: Know[NOT_EQ, I, Model[V, I]])
  : Derive[NOT_EQ[I], Model[V, I]] = new Derive[NOT_EQ[I], Model[V, I]] {
    override def apply(a: NOT_EQ[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[NOT_EQ[I]], Model[V, I])] =
      if(goals contains a) {
        StreamT.empty
      } else {
        val g = goals + a
        val k1 = m0 know a map (_ -> m0)

        k1 mappend {
          val m1 = lastModel(k1, m0)
          val k2 = `not_eq_at` apply(a, g, m0)

          k2 mappend {
            val m2 = lastModel(k2, m1)
            `noteq_<_>` apply (a, g, m2)
          }
        }
      }
  }

  def `noteq_<_>`[V, I]
  : Derive[NOT_EQ[I], Model[V, I]] = new Derive[NOT_EQ[I], Model[V, I]] {
    override def apply(a: NOT_EQ[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[NOT_EQ[I]], Model[V, I])] =
      for {
        (p1, m1) <- m0 derive (LT(a.lhs, a.rhs), goals)
        (p2, m2) <- m1 derive (LT(a.rhs, a.lhs), goals)
      } yield Rule2("not_eq_<_>", a, p1, p2) -> (m2 tell a)
  }

  implicit def derive_at[V, I]: Derive[AT[I], Model[V, I]] = new Derive[AT[I], Model[V, I]] {
    override def apply(a: AT[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[AT[I]], Model[V, I])] =
      m0 know a map (_ -> m0)
  }

  def `lt_at`[V, I]
  : Derive[LT[I], Model[V, I]] = new Derive[LT[I], Model[V, I]] {
    override def apply(a: LT[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[LT[I]], Model[V, I])] =
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if(atLHS.result.loc < atRHS.result.loc)
      } yield
      Rule2("lt_at", a, atLHS, atRHS) -> (m0 tell a)
  }

  def `lt_eq_at`[V, I]
  : Derive[LT_EQ[I], Model[V, I]] = new Derive[LT_EQ[I], Model[V, I]] {
    override def apply(a: LT_EQ[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[LT_EQ[I]], Model[V, I])] =
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if(atLHS.result.loc <= atRHS.result.loc)
      } yield
      Rule2("lt_eq_at", a, atLHS, atRHS) -> (m0 tell a)
  }

  def `eq_at`[V, I]
  (implicit
   vi: InterpretationSingleton[V, I], unify: UnifyI[I],
   in: Interpretation[EQ[V], EQ[I], Model[V, I]])
  : Derive[EQ[I], Model[V, I]] = new Derive[EQ[I], Model[V, I]] {
    override def apply(a: EQ[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[EQ[I]], Model[V, I])] =
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if(atLHS.result.loc == atRHS.result.loc)
      } yield
      Rule2("lt_eq_at", a, atLHS, atRHS) -> (m0 tell a)
  }

  def `not_eq_at`[V, I]
  : Derive[NOT_EQ[I], Model[V, I]] = new Derive[NOT_EQ[I], Model[V, I]] {
    override def apply(a: NOT_EQ[I], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[NOT_EQ[I]], Model[V, I])] =
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if(atLHS.result.loc != atRHS.result.loc)
      } yield
      Rule2("lt_eq_at", a, atLHS, atRHS) -> (m0 tell a)
  }
}

trait DeriveLowPriorityImpicits {

  import Derive.DeriveOps
  import Interpretation.InterpretationOps

  implicit def derive_usingInterpretation[A[_], V, I]
  (implicit
   in: Interpretation[A[V], A[I], Model[V, I]],
   d: Derive[A[I], Model[V, I]])
  : Derive[A[V], Model[V, I]] = new Derive[A[V], Model[V, I]] {

    override def apply(a: A[V], goals: Set[Object], m0: Model[V, I]): TrueStream[(Proof[A[V]], Model[V, I])] = {
      val (a1, m1) = m0 interpretation a
      Derive.log(s"Deriving $a")
      m1 derive (a1, goals) map { case (p, m) => Interpreted(a, p) -> m }
    }

  }


}