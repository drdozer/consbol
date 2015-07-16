package uk.co.turingatemyhamster.consbol


import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._
import uk.co.turingatemyhamster.consbol.util.FuncName
import uk.co.turingatemyhamster.consbol.Derive.DProof

import scala.language.higherKinds
import scalaz._
import Scalaz._

/**
 * Created by nmrp3 on 27/06/15.
 */
sealed trait Proof[A] {
  def name: String
  def goal: A
  def cuts: Option[Set[Any]]
}

object Proof {

  def fact[A](goal: A, cuts: Option[Set[Any]] = None)(implicit fn: FuncName): Proof[A] =
    Fact(fn.name, goal, cuts)

}

object Proof1 {

  def apply[A, LHS](goal: A, lhs: Proof[LHS], cuts: Option[Set[Any]] = None)(implicit fn: FuncName): Proof[A] =
    Proof1(fn.name, goal, cuts, lhs)

}

object Proof2 {

  def apply[A, LHS, RHS](goal: A, lhs: Proof[LHS], rhs: Proof[RHS], cuts: Option[Set[Any]] = None)(implicit fn: FuncName): Proof[A] =
    Proof2(fn.name, goal, cuts, lhs, rhs)

}

case class InterpretedProof[A[_], V, I](goal: A[V],
                                        cuts: Option[Set[Any]],
                                        interpreted: Proof[A[I]]) extends Proof[A[V]] {
  def name = "interpreted"
}

case class InterpretedDisproof[A[_], V, I](goal: A[V],
                                           cuts: Option[Set[Any]],
                                           interpreted: Disproof[A[I]]) extends Disproof[A[V]] {
  def name = "interpreted"
}

case class Fact[A](name: String,
                   goal: A,
                   cuts: Option[Set[Any]]) extends Proof[A]

case class Proof1[A, LHS](name: String,
                          goal: A,
                          cuts: Option[Set[Any]],
                          lhs: Proof[LHS]) extends Proof[A]

case class Proof2[A, LHS, RHS](name: String,
                               goal: A,
                               cuts: Option[Set[Any]],
                               lhs: Proof[LHS],
                               rhs: Proof[RHS]) extends Proof[A]
sealed trait Disproof[A] {
  def name: String
  def goal: A
  def cuts: Option[Set[Any]]
}

object DProof1 {

  def apply[A, LHS](goal: A,
                    lhs: DProof[LHS],
                    cuts: Option[Set[Any]] = None)
                   (implicit fn: FuncName): DProof[A] = lhs match {
    case -\/(d) =>
      Disproof1(fn.name, goal, cuts, d).left
    case \/-(p) =>
      Proof1(fn.name, goal, cuts, p).right
  }

}

object DProof2 {

  def apply[A, LHS, RHS](goal: A,
                         lhs: Proof[LHS],
                         rhs: DProof[RHS],
                         cuts: Option[Set[Any]])
                        (implicit fn: FuncName): DProof[A] = rhs match {
    case -\/(d) =>
      Disproof2(fn.name, goal, cuts, lhs, d).left
    case \/-(p) =>
      Proof2(fn.name, goal, cuts, lhs, p).right
  }

}

object DProof {

  def fact[A](goal: A, cuts: Option[Set[Any]] = None)(implicit fn: FuncName): DProof[A] =
    Fact(fn.name, goal, cuts).right

  def cut[A](goal: A,
             cuts: Set[Any])(implicit fn: FuncName): DProof[A] =
    Cut(name = fn.name, goal = goal, cuts = cuts.some).left


  def interpreted[A[_], V, I](goal: A[V], interp: DProof[A[I]]): DProof[A[V]] =
    interp.fold(
      i => interpreted[A, V, I](goal, i),
      i => interpreted[A, V, I](goal, i)
    )

  def interpreted[A[_], V, I](goal: A[V], interp: Proof[A[I]]): DProof[A[V]] =
    InterpretedProof[A, V, I](goal, None, interp).right

  def interpreted[A[_], V, I](goal: A[V], interp: Disproof[A[I]]): DProof[A[V]] =
    InterpretedDisproof[A, V, I](goal, None, interp).left
}

object Disproof {

  def noValue[A, V](value: V, cuts: Option[Set[Any]] = None)(implicit fn: FuncName): DProof[A] =
    NoValue(name = fn.name, goal = null.asInstanceOf[A], cuts, value = value).left

  def failure[A](goal: A, cuts: Option[Set[Any]] = None)(implicit fn: FuncName): DProof[A] =
    FailureD[A](name = fn.name, cuts = cuts, goal = goal).left

  def cut[A](goal: A, cuts: Set[Any])(implicit fn: FuncName): Disproof[A] =
    Cut(name = fn.name, goal = goal, cuts = cuts.some)
}

object Disproof1 {

  def apply[A, LHS](goal: A, lhs: Disproof[LHS], cuts: Option[Set[Any]] = None)(implicit fn: FuncName): Disproof[A] =
    Disproof1(fn.name, goal, cuts, lhs)

}

object Disproof2 {

  def apply[A, LHS, RHS](goal: A, lhs: Proof[LHS], rhs: Disproof[RHS], cuts: Option[Set[Any]] = None)(implicit fn: FuncName): Disproof[A] =
    Disproof2(fn.name, goal, cuts, lhs, rhs)

}

case class NoValue[A, V](name: String,
                         goal: A,
                         cuts: Option[Set[Any]],
                         value: V) extends Disproof[A]
case class FailureD[A](name: String, goal: A, cuts: Option[Set[Any]]) extends Disproof[A]
case class Cut[A](name: String, goal: A, cuts: Option[Set[Any]]) extends Disproof[A]

case class Disproof1[A, LHS](name: String,
                             goal: A,
                             cuts: Option[Set[Any]],
                             lhs: Disproof[LHS]) extends Disproof[A]

case class Disproof2[A, LHS, RHS](name: String,
                                  goal: A,
                                  cuts: Option[Set[Any]],
                                  lhs: Proof[LHS],
                                  rhs: Disproof[RHS]) extends Disproof[A]