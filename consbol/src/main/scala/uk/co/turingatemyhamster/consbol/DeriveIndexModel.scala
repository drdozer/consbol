package uk.co.turingatemyhamster.consbol

import scalaz.Scalaz._
import scalaz.{Need, Name, StreamT}

import Tell._
import Know._
import Derive._
import DeriveLHS._

object DeriveIndexModel {

  def `a @ i -| ?`[R, V, I]: Derive[AT[I], Model[R, V, I]] = guard {
    known
  }

  def `a < b -| a @ i, b @ j, i < j`[R, V, I] = Derive[LT[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc < atRHS.result.loc
      } yield
      Rule2("lt_at", a, atLHS, atRHS) -> (m0 tell a)
  }

  def `a <= b -| a @ i, b @ j, i <= j`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc <= atRHS.result.loc
      } yield
      Rule2("lt_eq_at", a, atLHS, atRHS) -> (m0 tell a)
  }

  def `a = b -| a @ i, b @ j, i = j`[R, V, I]
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

  def `a != b -| a @ i, b @ j, i != j`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        atLHS <- m0.knowLHS[AT, I](a.lhs)
        atRHS <- m0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc != atRHS.result.loc
      } yield
      Rule2("lt_eq_at", a, atLHS, atRHS) -> (m0 tell a)
  }

}
