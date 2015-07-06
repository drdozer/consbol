package uk.co.turingatemyhamster.consbol

import scala.language.higherKinds


trait Normalize[A[_], B[_], T] {
  def apply(a: A[T]): B[T]
}

object Normalize extends NormalizeLowPriority {

  implicit class NormalizeOps[A[_], T](_a: A[T]) {
    def normalize[B[_]](implicit n: Normalize[A, B, T]): B[T] =
      n(_a)
  }

  def translate[A[_], B[_], T]
  (implicit aOps: BinOp[A, T], bOps: BinOp[B, T]): Normalize[A, B, T] = new Normalize[A, B, T] {
    override def apply(a: A[T]): B[T] = {
      val (lhs, rhs) = aOps decompose a
      bOps recompose (lhs, rhs)
    }
  }

  def swap[A[_], B[_], T]
  (implicit aOps: BinOp[A, T], bOps: BinOp[B, T]): Normalize[A, B, T] = new Normalize[A, B, T] {
    override def apply(a: A[T]): B[T] = {
      val (lhs, rhs) = aOps decompose a
      bOps recompose (rhs, lhs)
    }
  }

  implicit def norm_gt_eq[T]: Normalize[GT_EQ, LT, T] =
    swap[GT_EQ, LT, T]

  implicit def norm_gt[T]: Normalize[GT, LT_EQ, T] =
    swap[GT, LT_EQ, T]

  implicit def norm_not_lt[T]: Normalize[NOT_LT, LT_EQ, T] =
    swap[NOT_LT, LT_EQ, T]

  implicit def norm_not_lt_eq[T]: Normalize[NOT_LT_EQ, LT, T] =
    swap[NOT_LT_EQ, LT, T]

  implicit def norm_not_gt_eq[T]: Normalize[NOT_GT_EQ, LT, T] =
    translate[NOT_GT_EQ, LT, T]

  implicit def norm_not_gt[T]: Normalize[NOT_GT, LT_EQ, T] =
    translate[NOT_GT, LT_EQ, T]


  implicit def norm_not_shorter_than[T]: Normalize[NotShorterThan, NotLongerThan, T] =
    swap[NotShorterThan, NotLongerThan, T]

  implicit def norm_longer_than[T]: Normalize[LongerThan, ShorterThan, T] =
    swap[LongerThan, ShorterThan, T]


  implicit def norm_within[T]: Normalize[Within, Contains, T] =
    swap[Within, Contains, T]

  implicit def norm_intersects53[T]: Normalize[Intersects53, Intersects35, T] =
    swap[Intersects53, Intersects35, T]

  implicit def norm_joinsDirectly53[T]: Normalize[JoinsDirectly53, JoinsDirectly35, T] =
    swap[JoinsDirectly53, JoinsDirectly35, T]

  implicit def norm_joinsWithGap53[T]: Normalize[JoinsWithGap53, JoinsWithGap35, T] =
    swap[JoinsWithGap53, JoinsWithGap35, T]

  implicit def norm_joins53[T]: Normalize[Joins53, Joins35, T] =
    swap[Joins53, Joins35, T]
}

trait NormalizeLowPriority {
  
  implicit def normalize_identity[A[_], T]: Normalize[A, A, T] = new Normalize[A, A, T] {
    override def apply(a: A[T]): A[T] = a
  }
  
}