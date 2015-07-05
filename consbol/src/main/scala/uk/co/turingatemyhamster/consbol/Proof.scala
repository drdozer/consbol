package uk.co.turingatemyhamster.consbol

import fastparse.FuncName

/**
 * Created by nmrp3 on 27/06/15.
 */
trait Proof[A] {
  def name: String
  def result: A
}

case class Interpreted[A[_], V, I](result: A[V], interpreted: Proof[A[I]]) extends Proof[A[V]] {
  def name = "interpreted"
}

case class Fact[A](result: A) extends Proof[A] {
  def name = "fact"
}

case class Rule1[A, LHS](name: String,
                         result: A,
                         lhs: Proof[LHS]) extends Proof[A]

object Rule1 {
  def apply[A, LHS, RHS](result: A, lhs: Proof[LHS])(implicit fn: FuncName): Rule1[A, LHS] =
    Rule1(fn.name, result, lhs)
}

case class Rule2[A, LHS, RHS](name: String,
                              result: A,
                              lhs: Proof[LHS],
                              rhs: Proof[RHS]) extends Proof[A]

object Rule2 {
  def apply[A, LHS, RHS](result: A, lhs: Proof[LHS], rhs: Proof[RHS])(implicit fn: FuncName): Rule2[A, LHS, RHS] =
    Rule2(fn.name, result, lhs, rhs)
}