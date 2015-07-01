package uk.co.turingatemyhamster.consbol

import scala.language.higherKinds


trait Normalize[A[_], B[_]] {
  def apply[V](a: A[V]): B[V]
}

object Normalize {

  def apply[A[_], B[_], V](a: A[V])(implicit n: Normalize[A, B]): B[V] = n(a)

  implicit val lt: Normalize[LT, LT] = new Normalize[LT, LT] {
    override def apply[V](a: LT[V]): LT[V] = a
  }

  implicit val lt_eq: Normalize[LT_EQ, LT_EQ] = new Normalize[LT_EQ, LT_EQ] {
    override def apply[V](a: LT_EQ[V]): LT_EQ[V] = a
  }

  implicit val eq: Normalize[EQ, EQ] = new Normalize[EQ, EQ] {
    override def apply[V](a: EQ[V]): EQ[V] = a
  }

  implicit val gt_eq: Normalize[GT_EQ, LT] = new Normalize[GT_EQ, LT] {
    override def apply[V](a: GT_EQ[V]): LT[V] = LT(a.rhs, a.lhs)
  }

  implicit val gt: Normalize[GT, LT_EQ] = new Normalize[GT, LT_EQ] {
    override def apply[V](a: GT[V]): LT_EQ[V] = LT_EQ(a.rhs, a.lhs)
  }

  implicit val not_lt: Normalize[NOT_LT, LT_EQ] = new Normalize[NOT_LT, LT_EQ] {
    override def apply[V](a: NOT_LT[V]): LT_EQ[V] = LT_EQ(a.rhs, a.lhs)
  }

  implicit val not_lt_eq: Normalize[NOT_LT_EQ, LT] = new Normalize[NOT_LT_EQ, LT] {
    override def apply[V](a: NOT_LT_EQ[V]): LT[V] = LT(a.rhs, a.lhs)
  }

  implicit val not_eq: Normalize[NOT_EQ, NOT_EQ] = new Normalize[NOT_EQ, NOT_EQ] {
    override def apply[V](a: NOT_EQ[V]): NOT_EQ[V] = a
  }

  implicit val not_gt_eq: Normalize[NOT_GT_EQ, LT] = new Normalize[NOT_GT_EQ, LT] {
    override def apply[V](a: NOT_GT_EQ[V]): LT[V] = LT(a.lhs, a.rhs)
  }

  implicit val not_gt: Normalize[NOT_GT, LT_EQ] = new Normalize[NOT_GT, LT_EQ] {
    override def apply[V](a: NOT_GT[V]): LT_EQ[V] = LT_EQ(a.lhs, a.rhs)
  }

}
