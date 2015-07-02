package uk.co.turingatemyhamster.consbol


sealed trait Orientation

object Orientation {
  object + extends Orientation
  object - extends Orientation
}


case class RangeAs[R, V](range: R, lower: V, upper: V)


case class Strand[R](range: R, orient: Orientation)

case class SameStrandAs[R](lhs: R, rhs: R)

case class DifferentStrandTo[R](lhs: R, rhs: R)


case class ShorterThan[R](lhs: R, rhs: R)

case class NotLongerThan[R](lhs: R, rhs: R)

case class SameLengthAs[R](lhs: R, rhs: R)

case class NotShorterThan[R](lhs: R, rhs: R)

case class LongerThan[R](lhs: R, rhs: R)


case class Equals[R](lhs: R, rhs: R)

case class Contains[R](lhs: R, rhs: R)

case class Within[R](lhs: R, rhs: R)

case class EndsWith[R](lhs: R, rhs: R)

case class StartsWith[R](lhs: R, rhs: R)

case class Touches[R](lhs: R, rhs: R)

case class Overlaps[R](lhs: R, rhs: R)


case class Intersects33[R](lhs: R, rhs: R)

case class Intersects35[R](lhs: R, rhs: R)

case class Intersects55[R](lhs: R, rhs: R)

case class Intersects53[R](lhs: R, rhs: R)


case class ContainsPrefix5[R](lhs: R, rhs: R)

case class ContainsPrefix3[R](lhs: R, rhs: R)

case class ContainsSuffix5[R](lhs: R, rhs: R)

case class ContainsSuffix3[R](lhs: R, rhs: R)


case class JoinsDirectly33[R](lhs: R, rhs: R)

case class JoinsDirectly35[R](lhs: R, rhs: R)

case class JoinsDirectly55[R](lhs: R, rhs: R)

case class JoinsDirectly53[R](lhs: R, rhs: R)


case class JoinsWithGap33[R](lhs: R, rhs: R)

case class JoinsWithGap35[R](lhs: R, rhs: R)

case class JoinsWithGap55[R](lhs: R, rhs: R)

case class JoinsWithGap53[R](lhs: R, rhs: R)


case class Joins33[R](lhs: R, rhs: R)

case class Joins35[R](lhs: R, rhs: R)

case class Joins55[R](lhs: R, rhs: R)

case class Joins53[R](lhs: R, rhs: R)
