package uk.co.turingatemyhamster.consbol

import scalaz.Scalaz._
import scalaz.{Need, Name, StreamT}

import Tell._
import Know._
import Derive._
import DeriveLHS._

object DeriveOrdModel {

  def `a < b -| ?`[R, V, I]
  (implicit k: Know[LT, I, Model[R, V, I]])
  : Derive[LT[I], Model[R, V, I]] = guard {
    known ||
      DeriveIndexModel.`a < b -| a @ i, b @ j, i < j` ||
      `a < c -| a < b, b < c` ||
      `a <_c -| a < b, b <= c` ||
      `a < c -| a <= b, b < c`
  }

  def `a <_c -| a < b, b <= c`[R, V, I] = Derive[LT[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        px <- m0.knowLHS[LT, I](a.lhs)
        x = px.result.rhs
        (p1, m1) <- m0 derive LT_EQ(x, a.rhs) using goals
      } yield {
        Rule2("lt_<_<=", a, px, p1) -> (m1 tell a)
      }
  }

  def `a < c -| a <= b, b < c`[R, V, I] = Derive[LT[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        px <- m0.knowLHS[LT_EQ, I](a.lhs)
        x = px.result.rhs
        (p1, m1) <- m0 derive LT(x, a.rhs) using goals
      } yield {
        Rule2("lt_<=_<", a, px, p1) -> (m1 tell a)
      }
  }

  def `a < c -| a < b, b < c`[R, V, I] = Derive[LT[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        px <- m0.knowLHS[LT, I](a.lhs)
        x = px.result.rhs
        (p1, m1) <- m0 derive LT(x, a.rhs) using goals
      } yield {
        Rule2("lt_<_<", a, px, p1) -> (m1 tell a)
      }
    }


  def `a <= b -| ?`[R, V, I]
  (implicit kLtEq: Know[LT_EQ, I, Model[R, V, I]]) = guard {
    known ||
      DeriveIndexModel.`a <= b -| a @ i, b @ j, i <= j` ||
      `a <= b -| a < b` ||
      `a <= c -| a <= b, b <= c`
  }

  def `a <= c -| a <= b, b <= c`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        px <- m0.knowLHS[LT_EQ, I](a.lhs)
        x = px.result.rhs
        (p1, m1) <- m0 derive LT_EQ(x, a.rhs) using goals
      } yield Rule2("lt_eq_<=_<=", a, px, p1) -> (m1 tell a)
  }

  def `a <= b -| a < b`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (p, m1) <- m0 derive LT(a.lhs, a.rhs) using goals
      } yield Rule1("lt_eq_<", a, p) -> (m1 tell a)
  }


  def `a = b -| ?`[R, V, I]
  (implicit t: Tell[EQ[I], Model[R, V, I]]) = guard {
    DeriveIndexModel.`a = b -| a @ i, b @ j, i = j` ||
      `a = b -| a <=b, b <= a`
  }


  def `a = b -| a <=b, b <= a`[R, V, I]
  (implicit t: Tell[EQ[I], Model[R, V, I]]) = Derive[EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (p1, m1) <- m0 derive LT_EQ(a.lhs, a.rhs) using goals
        (p2, m2) <- m1 derive LT_EQ(a.rhs, a.lhs) using goals
      } yield Rule2("eq_<=_>=", a, p1, p2) -> (m2 tell a)
  }


  def `a != b -| ?`[R, V, I]
  (implicit k: Know[NOT_EQ, I, Model[R, V, I]]) = guard {
    known ||
      DeriveIndexModel.`a != b -| a @ i, b @ j, i != j` ||
      `a != b -| a < b` ||
      `a != b -| b < a`
  }

  def `a != b -| a < b`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (p1, m1) <- m0 derive LT(a.lhs, a.rhs) using goals
      } yield Rule1("not_eq_<_>", a, p1) -> (m1 tell a)
  }

  def `a != b -| b < a`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (p1, m1) <- m0 derive LT(a.rhs, a.lhs) using goals
      } yield Rule1("not_eq_<_>", a, p1) -> (m1 tell a)
  }

}
