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
   (a, ds0) =>
      for {
        atLHS <- ds0.knowLHS[AT, I](a.lhs)
        atRHS <- ds0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc < atRHS.result.loc
      } yield
      Rule2(a, atLHS, atRHS) -> (ds0 tell a)
  }

  def `a <= b -| a @ i, b @ j, i <= j`[R, V, I] = Derive[LT_EQ[I], Model[R, V, I]] {
   (a, ds0) =>
      for {
        atLHS <- ds0.knowLHS[AT, I](a.lhs)
        atRHS <- ds0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc <= atRHS.result.loc
      } yield
      Rule2(a, atLHS, atRHS) -> (ds0 tell a)
  }

  def `a = b -| a @ i, b @ j, i = j`[R, V, I]
  (implicit
   t: Tell[EQ[I], Model[R, V, I]]) = Derive[EQ[I], Model[R, V, I]] {
   (a, ds0) =>
      for {
        atLHS <- ds0.knowLHS[AT, I](a.lhs)
        atRHS <- ds0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc == atRHS.result.loc
      } yield
      Rule2(a, atLHS, atRHS) -> (ds0 tell a)
  }

  def `a != b -| a @ i, b @ j, i != j`[R, V, I] = Derive[NOT_EQ[I], Model[R, V, I]] {
   (a, ds0) =>
      for {
        atLHS <- ds0.knowLHS[AT, I](a.lhs)
        atRHS <- ds0.knowLHS[AT, I](a.rhs)
        if atLHS.result.loc != atRHS.result.loc
      } yield
      Rule2(a, atLHS, atRHS) -> (ds0 tell a)
  }

}
