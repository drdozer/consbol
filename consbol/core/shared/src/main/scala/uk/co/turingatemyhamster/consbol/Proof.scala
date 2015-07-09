package uk.co.turingatemyhamster.consbol

import fastparse.FuncName
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
}

object Proof {

  def apply[A, LHS](result: A, lhs: Proof[LHS])(implicit fn: FuncName): Proof[A] =
    Proof1(fn.name, result, lhs)

  def apply[A, LHS, RHS](result: A, lhs: Proof[LHS], rhs: Proof[RHS])(implicit fn: FuncName): Proof[A] =
    Proof2(fn.name, result, lhs, rhs)
}

case class InterpretedProof[A[_], V, I](goal: A[V], interpreted: Proof[A[I]]) extends Proof[A[V]] {
  def name = "interpreted"
}

case class InterpretedDisproof[A[_], V, I](goal: A[V], interpreted: Disproof[A[I]]) extends Disproof[A[V]] {
  def name = "interpreted"
}

case class Fact[A](goal: A) extends Proof[A] {
  def name = "fact"
}

case class Proof1[A, LHS](name: String,
                          goal: A,
                          lhs: Proof[LHS]) extends Proof[A]

case class Proof2[A, LHS, RHS](name: String,
                               goal: A,
                               lhs: Proof[LHS],
                               rhs: Proof[RHS]) extends Proof[A]
sealed trait Disproof[A] {
  def name: String
  def goal: A
}

object DProof {
  def interpreted[A[_], V, I](goal: A[V], interpreted: Proof[A[I]]): DProof[A[V]] =
    InterpretedProof[A, V, I](goal, interpreted).right

  def interpreted[A[_], V, I](goal: A[V], interpreted: Disproof[A[I]]): DProof[A[V]] =
    InterpretedDisproof[A, V, I](goal, interpreted).left
}

object Disproof {
  def cut[A, LHS](lhs: Disproof[LHS]): DProof[A] = Cut[A, LHS](lhs = lhs).left
}

case class Cut[A, LHS](name: String = "cut", goal: A = ???, lhs: Disproof[LHS]) extends Disproof[A]

case class Disproof1[A, LHS](name: String,
                             goal: A,
                             lhs: DProof[A]) extends Disproof[A]

case class Disproof2[A, LHS, RHS](name: String,
                                  goal: A,
                                  lhs: DProof[A],
                                  rhs: DProof[A]) extends Disproof[A]