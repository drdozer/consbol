package uk.co.turingatemyhamster.consbol

import scala.language.higherKinds
import scalaz.std.option._

/**
 * Created by nmrp3 on 01/07/15.
 */
object BinOp {

  def apply[O[_], T](r: (T, T) => O[T], d: O[T] => Option[(T, T)]): BinOp[O, T] = new BinOp[O, T] {
    override def recompose(tt: (T, T)): O[T] = r.tupled(tt)

    override def decompose(o: O[T]): (T, T) = d(o).get
  }

  implicit def binop_lt[T] = BinOp[LT, T](LT.apply, LT.unapply)
  implicit def binop_ltEq[T] = BinOp[LT_EQ, T](LT_EQ.apply, LT_EQ.unapply)
  implicit def binop_eq[T] = BinOp[EQ, T](EQ.apply, EQ.unapply)
  implicit def binop_gtEq[T] = BinOp[GT_EQ, T](GT_EQ.apply, GT_EQ.unapply)
  implicit def binop_gt[T] = BinOp[GT, T](GT.apply, GT.unapply)
  implicit def binop_not[T] = BinOp[NOT_LT, T](NOT_LT.apply, NOT_LT.unapply)
  implicit def binop_notLtEq[T] = BinOp[NOT_LT_EQ, T](NOT_LT_EQ.apply, NOT_LT_EQ.unapply)
  implicit def binop_notEq[T] = BinOp[NOT_EQ, T](NOT_EQ.apply, NOT_EQ.unapply)
  implicit def binop_notGtEq[T] = BinOp[NOT_GT_EQ, T](NOT_GT_EQ.apply, NOT_GT_EQ.unapply)
  implicit def binop_notGt[T] = BinOp[NOT_GT, T](NOT_GT.apply, NOT_GT.unapply)

  implicit def binop_suc[T] = BinOp[Suc, T](Suc.apply, Suc.unapply)
  implicit def binop_pre[T] = BinOp[Pre, T](Pre.apply, Pre.unapply)

  implicit def binop_shorterThan[T] = BinOp[ShorterThan, T](ShorterThan.apply, ShorterThan.unapply)
  implicit def binop_notLongerThan[T] = BinOp[NotLongerThan, T](NotLongerThan.apply, NotLongerThan.unapply)
  implicit def binop_notShorterThan[T] = BinOp[NotShorterThan, T](NotShorterThan.apply, NotShorterThan.unapply)
  implicit def binop_longerThan[T] = BinOp[LongerThan, T](LongerThan.apply, LongerThan.unapply)

  implicit def binop_sameStrandAs[T] = BinOp[SameStrandAs, T](SameStrandAs.apply, SameStrandAs.unapply)
  implicit def binop_differentStrandTo[T] = BinOp[DifferentStrandTo, T](DifferentStrandTo.apply, DifferentStrandTo.unapply)

  implicit def binop_equals[T] = BinOp[Equals, T](Equals.apply, Equals.unapply)
  implicit def binop_contains[T] = BinOp[Contains, T](Contains.apply, Contains.unapply)
  implicit def binop_within[T] = BinOp[Within, T](Within.apply, Within.unapply)
  implicit def binop_endsWith[T] = BinOp[EndsWith, T](EndsWith.apply, EndsWith.unapply)
  implicit def binop_startsWith[T] = BinOp[StartsWith, T](StartsWith.apply, StartsWith.unapply)
  implicit def binop_touches[T] = BinOp[Touches, T](Touches.apply, Touches.unapply)
  implicit def binop_overlaps[T] = BinOp[Overlaps, T](Overlaps.apply, Overlaps.unapply)

  implicit def binop_intersects33[T] = BinOp[Intersects33, T](Intersects33.apply, Intersects33.unapply)
  implicit def binop_intersects35[T] = BinOp[Intersects35, T](Intersects35.apply, Intersects35.unapply)
  implicit def binop_intersects55[T] = BinOp[Intersects55, T](Intersects55.apply, Intersects55.unapply)
  implicit def binop_intersects53[T] = BinOp[Intersects53, T](Intersects53.apply, Intersects53.unapply)

  implicit def binop_containsPrefix5[T] = BinOp[ContainsPrefix5, T](ContainsPrefix5.apply, ContainsPrefix5.unapply)
  implicit def binop_containsPrefix3[T] = BinOp[ContainsPrefix3, T](ContainsPrefix3.apply, ContainsPrefix3.unapply)
  implicit def binop_containsSuffix5[T] = BinOp[ContainsSuffix5, T](ContainsSuffix5.apply, ContainsSuffix5.unapply)
  implicit def binop_containsSuffix3[T] = BinOp[ContainsSuffix3, T](ContainsSuffix3.apply, ContainsSuffix3.unapply)

  implicit def binop_joinsDirectly33[T] = BinOp[JoinsDirectly33, T](JoinsDirectly33.apply, JoinsDirectly33.unapply)
  implicit def binop_joinsDirectly35[T] = BinOp[JoinsDirectly35, T](JoinsDirectly35.apply, JoinsDirectly35.unapply)
  implicit def binop_joinsDirectly55[T] = BinOp[JoinsDirectly55, T](JoinsDirectly55.apply, JoinsDirectly55.unapply)
  implicit def binop_joinsDirectly53[T] = BinOp[JoinsDirectly53, T](JoinsDirectly53.apply, JoinsDirectly53.unapply)

  implicit def binop_joinsWithGap33[T] = BinOp[JoinsWithGap33, T](JoinsWithGap33.apply, JoinsWithGap33.unapply)
  implicit def binop_joinsWithGap35[T] = BinOp[JoinsWithGap35, T](JoinsWithGap35.apply, JoinsWithGap35.unapply)
  implicit def binop_joinsWithGap55[T] = BinOp[JoinsWithGap55, T](JoinsWithGap55.apply, JoinsWithGap55.unapply)
  implicit def binop_joinsWithGap53[T] = BinOp[JoinsWithGap53, T](JoinsWithGap53.apply, JoinsWithGap53.unapply)


  implicit def binop_joins33[T] = BinOp[Joins33, T](Joins33.apply, Joins33.unapply)
  implicit def binop_joins35[T] = BinOp[Joins35, T](Joins35.apply, Joins35.unapply)
  implicit def binop_joins55[T] = BinOp[Joins55, T](Joins55.apply, Joins55.unapply)
  implicit def binop_joins53[T] = BinOp[Joins53, T](Joins53.apply, Joins53.unapply)

}

trait BinOp[O[_], T] {
  def decompose(o: O[T]): (T, T)
  def recompose(tt: (T, T)): O[T]
}

object MonOp {

  def apply[O[_], T, X](r: (T, X) => O[T], d: O[T] => Option[(T, X)]): MonOp[O, T, X] = new MonOp[O, T, X] {
    override def recompose(tx: (T, X)): O[T] = r.tupled(tx)

    override def decompose(o: O[T]): (T, X) = d(o).get
  }

  implicit def monop_strand[T]: MonOp[Strand, T, Orientation] = MonOp[Strand, T, Orientation](Strand.apply, Strand.unapply)
  implicit def monop_at[T]: MonOp[AT, T, Int] = MonOp[AT, T, Int](AT.apply, AT.unapply)
  implicit def monop_length[T]: MonOp[Length, T, Int] = MonOp[Length, T, Int](Length.apply, Length.unapply)
}

trait MonOp[O[_], T, X] {
  def decompose(o: O[T]): (T, X)
  def recompose(tx: (T, X)): O[T]
}

object MonOp2 {

  def apply[O[_, _], T, U, X](r: (T, X) => O[T, U], d: O[T, U] => Option[(T, X)]) = new MonOp2[O, T, U, X] {
    override def decompose(o: O[T, U]): (T, X) = d(o).get

    override def recompose(tx: (T, X)): O[T, U] = r.tupled(tx)
  }

  implicit def monop_rangeAt[T, U]: MonOp2[RangeAs, T, U, (U, U)] = MonOp2[RangeAs, T, U, (U, U)](
    {case(r, (a, b)) => RangeAs(r, a, b)},
    {case RangeAs(r, l, u) => some(r, (l, u))})
}

trait MonOp2[O[_, _], T, U, X] {
  def decompose(o: O[T, U]): (T, X)
  def recompose(tx: (T, X)): O[T, U]
}