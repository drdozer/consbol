package uk.co.turingatemyhamster.consbol

import scala.language.higherKinds

case class LT[T](lhs: T, rhs: T)
case class LT_EQ[T](lhs: T, rhs: T)
case class EQ[T](lhs: T, rhs: T)
case class GT_EQ[T](lhs: T, rhs: T)
case class GT[T](lhs: T, rhs: T)
case class NOT_LT[T](lhs: T, rhs: T)
case class NOT_LT_EQ[T](lhs: T, rhs: T)
case class NOT_EQ[T](lhs: T, rhs: T)
case class NOT_GT_EQ[T](lhs: T, rhs: T)
case class NOT_GT[T](lhs: T, rhs: T)

case class AT[T](point: T, loc: Int)
case class Suc[T](lhs: T, rhs: T)
case class Pre[T](lhs: T, rhs: T)