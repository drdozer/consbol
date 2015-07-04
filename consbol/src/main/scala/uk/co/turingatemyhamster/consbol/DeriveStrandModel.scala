package uk.co.turingatemyhamster.consbol

import scalaz.Scalaz._
import scalaz.{Need, Name, StreamT}

import Tell._
import Know._
import Derive._
import DeriveLHS._


object DeriveStrandModel {

  def `±r -| ?`[R, V, I]
  : Derive[Strand[R], Model[R, V, I]] = guard {
    known[Strand, R, R, V, I] ||
      `±r -| r±s, ±s`
  } log "±r -| ?"

  def `r±s -| ?`[R, V, I]
  : Derive[SameStrandAs[R], Model[R, V, I]] = guard {
    known[SameStrandAs, R, R, V, I] ||
    `r+s -| +r, +s` ||
    `r-s -| -r, -s` ||
    `r±t -| r±s, s±t` /* ||
    `r±t -| r∓s, s∓t` || 
    `r±s -| s±r` */
  } log "r±s -| ?"

  def `r+s -| +r, +s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] {
    (a, goals, m0) =>
      for {
        (s1, m1) <- m0 derive Strand(a.lhs, Orientation.+) using goals
        (s2, m2) <- m1 derive Strand(a.rhs, Orientation.+) using goals
      } yield Rule2("+r, +s |- r+s", a, s1, s2) -> (m2 tell a)
  } log "r+s -| +r, +s"

  def `r-s -| -r, -s`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] {
   (a, goals, m0) =>
      for {
        (s1, m1) <- m0 derive Strand(a.lhs, Orientation.-) using goals
        (s2, m2) <- m1 derive Strand(a.rhs, Orientation.-) using goals
      } yield Rule2("-r, -s |- r-s", a, s1, s2) -> (m2 tell a)
  } log "r-s -| -r, -s"

  def `r±s -| s±r`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] {
    (a, goals, m0) =>
      if(a.lhs != a.rhs)
        for {
          (s1, m1) <- m0 derive SameStrandAs(a.rhs, a.lhs) using goals
        } yield Rule1("s±r |- r±s", a, s1) -> (m1 tell a)
      else
        StreamT.empty
  } log "r±s -| s±r"

  def `±r -| r±s, ±s`[R, V, I] = Derive[Strand[R], Model[R, V, I]] {
    (a, goals, m0) =>
      for {
        (s1, m1) <- m0 deriveLHS[SameStrandAs, R] a.range using goals
        (s2, m2) <- m0 derive Strand(s1.result.rhs, a.orient) using goals
      } yield Rule2("r+s, +s |- +r", a, s1, s2) -> (m2 tell a)
  } log "±r -| r±s, ±s"

  def `r±t -| r±s, s±t`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] {
    (a, goals, m0) =>
      for {
        (s1, m1) <- m0 deriveLHS[SameStrandAs, R] a.lhs using goals
        (s2, m2) <- m1 derive SameStrandAs(s1.result.rhs, a.rhs) using goals
      } yield Rule2("r±s, s±t |- r±t", a, s1, s2) -> (m2 tell a)
  } log "±t -| r±s, s±t"

  def `r±t -| r∓s, s∓t`[R, V, I] = Derive[SameStrandAs[R], Model[R, V, I]] {
    (a, goals, m0) =>
      for {
        (s1, m1) <- m0 deriveLHS[DifferentStrandTo, R] a.lhs using goals
        (s2, m2) <- m1 derive DifferentStrandTo(s1.result.rhs, a.rhs) using goals
      } yield Rule2("r±s, s±t |- r±t", a, s1, s2) -> (m2 tell a)
  } log "r±t -| r∓s, s∓t`"

  def `r∓s -| ?`[R, V, I]
  : Derive[DifferentStrandTo[R], Model[R, V, I]] = guard {
    known[DifferentStrandTo, R, R, V, I] /* ||
      `r∓s -| +r, -s` ||
      `r∓s -| -r, +s`  ||
      `r∓s -| s∓r` */
  } log "r∓s -| ?"

  def `r∓s -| s∓r`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] {
    (a, goals, m0) =>
      if(a.lhs != a.rhs)
        for {
          (s1, m1) <- m0 derive DifferentStrandTo(a.rhs, a.lhs) using goals
        } yield Rule1("s∓r |- r∓s", a, s1) -> (m1 tell a)
      else
        StreamT.empty
  } log "r∓s -| s∓r"

  def `r∓s -| +r, -s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] {
    (a, goals, m0) =>
      for {
        (s1, m1) <- m0 derive Strand(a.lhs, Orientation.+) using goals
        (s2, m2) <- m1 derive Strand(a.rhs, Orientation.-) using goals
      } yield Rule2("+r, -s |- r∓s", a, s1, s2) -> (m2 tell a)
  } log "r∓s -| +r, -s"

  def `r∓s -| -r, +s`[R, V, I] = Derive[DifferentStrandTo[R], Model[R, V, I]] {
    (a, goals, m0) =>
      for {
        (s1, m1) <- m0 derive Strand(a.lhs, Orientation.-) using goals
        (s2, m2) <- m1 derive Strand(a.rhs, Orientation.+) using goals
      } yield Rule2("-r, +s |- r∓s", a, s1, s2) -> (m2 tell a)
  } log "r∓s -| -r, +s"
}
