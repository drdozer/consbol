package uk.co.turingatemyhamster.consbol

import utest._

object NormalizeTestSuite extends TestSuite {

  import Normalize.NormalizeOps

  val tests = TestSuite {
    'ord - {

      'lt - assert(LT('a, 'b).normalize == LT('a, 'b))
      'lt_eq - assert(LT_EQ('a, 'b).normalize == LT_EQ('a, 'b))
      'eq - assert(EQ('a, 'b).normalize == EQ('a, 'b))
      'gt_eq - assert(GT_EQ('a, 'b).normalize == LT('b, 'a))
      'gt - assert(GT('a, 'b).normalize == LT_EQ('b, 'a))
      'not_lt - assert(NOT_LT('a, 'b).normalize == LT_EQ('b, 'a))
      'not_lt_eq - assert(NOT_LT_EQ('a, 'b).normalize == LT('b, 'a))
      'not_eq - assert(NOT_EQ('a, 'b).normalize == NOT_EQ('a, 'b))
      'not_gt_eq - assert(NOT_GT_EQ('a, 'b).normalize == LT('a, 'b))
      'not_gt - assert(NOT_GT('a, 'b).normalize == LT_EQ('a, 'b))
    }

    'strand - {

      'same_strand_as - assert(SameStrandAs('r, 's).normalize == SameStrandAs('r, 's))
      'different_strand_to - assert(DifferentStrandTo('r, 's).normalize == DifferentStrandTo('r, 's))

    }

    'length - {

      'shorter_than - assert(ShorterThan('r, 's).normalize == ShorterThan('r, 's))
      'not_longer_than - assert(NotLongerThan('r, 's).normalize == NotLongerThan('r, 's))
      'same_length_as - assert(SameLengthAs('r, 's).normalize == SameLengthAs('r, 's))
      'not_shorter_than - assert(NotShorterThan('r, 's).normalize == NotLongerThan('s, 'r))
      'longer_than - assert(LongerThan('r, 's).normalize == ShorterThan('s, 'r))

    }

    'range - {
      'equals - assert(Equals('r, 's).normalize == Equals('r, 's))
      'contains - assert(Contains('r, 's).normalize == Contains('r, 's))
      'within - assert(Within('r, 's).normalize == Contains('s, 'r))
      'ends_with - assert(EndsWith('r, 's).normalize == EndsWith('r, 's))
      'starts_with - assert(StartsWith('r, 's).normalize == StartsWith('r, 's))
      'touches - assert(Touches('r, 's).normalize == Touches('r, 's))
      'overlaps - assert(Overlaps('r, 's).normalize == Overlaps('r, 's))

    }

    'topological - {
      'intersect_3_to_3 - assert(Intersects33('r, 's).normalize == Intersects33('r, 's))
      'intersect_3_to_5 - assert(Intersects35('r, 's).normalize == Intersects35('r, 's))
      'intersect_5_to_5 - assert(Intersects55('r, 's).normalize == Intersects55('r, 's))
      'intersect_5_to_3 - assert(Intersects53('r, 's).normalize == Intersects35('s, 'r))

      'contains_prefix_5 - assert(ContainsPrefix5('r, 's).normalize == ContainsPrefix5('r, 's))
      'contains_prefix_3 - assert(ContainsPrefix3('r, 's).normalize == ContainsPrefix3('r, 's))
      'contains_suffix_5 - assert(ContainsSuffix5('r, 's).normalize == ContainsSuffix5('r, 's))
      'contains_suffix_3 - assert(ContainsSuffix3('r, 's).normalize == ContainsSuffix3('r, 's))

      'joins_directly_3_to_3 - assert(JoinsDirectly33('r, 's).normalize == JoinsDirectly33('r, 's))
      'joins_directly_3_to_5 - assert(JoinsDirectly35('r, 's).normalize == JoinsDirectly35('r, 's))
      'joins_directly_5_to_5 - assert(JoinsDirectly55('r, 's).normalize == JoinsDirectly55('r, 's))
      'joins_directly_5_to_3 - assert(JoinsDirectly53('r, 's).normalize == JoinsDirectly35('s, 'r))

      'joins_with_gap_3_to_3 - assert(JoinsWithGap33('r, 's).normalize == JoinsWithGap33('r, 's))
      'joins_with_gap_3_to_5 - assert(JoinsWithGap35('r, 's).normalize == JoinsWithGap35('r, 's))
      'joins_with_gap_5_to_5 - assert(JoinsWithGap55('r, 's).normalize == JoinsWithGap55('r, 's))
      'joins_with_gap_5_to_3 - assert(JoinsWithGap53('r, 's).normalize == JoinsWithGap35('s, 'r))

      'joins_3_to_3 - assert(Joins33('r, 's).normalize == Joins33('r, 's))
      'joins_3_to_5 - assert(Joins35('r, 's).normalize == Joins35('r, 's))
      'joins_5_to_5 - assert(Joins55('r, 's).normalize == Joins55('r, 's))
      'joins_5_to_3 - assert(Joins53('r, 's).normalize == Joins35('s, 'r))
    }
  }

}
