package uk.co.turingatemyhamster.consbol

import utest._

object TellTestSuite extends TestSuite {

  val tests = TestSuite {

    import Tell._

    'tell - {
      val m0 = Model.empty[Symbol, Symbol, String]

      'ord - {
        'lt - {

          'implicits - {
            implicitly[Tell[LT[String], OrdModel[String]]]
            implicitly[Tell[LT[String], Model[Symbol, Symbol, String]]]
            implicitly[InterpretationSingleton[Symbol, String]]
            implicitly[Interpretation[Symbol, String, Model[Symbol, Symbol, String]]]
            implicitly[Interpretation[LT[Symbol], LT[String], Model[Symbol, Symbol, String]]]
            implicitly[Tell[LT[Symbol], Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell LT('a, 'b)

          'contains_a - assert(m1.i.v2i.contains('a))
          'contains_b - assert(m1.i.v2i.contains('b))

          val aI = m1.i.v2i('a)
          val bI = m1.i.v2i('b)

          'distinct_interpretations - assert(aI != bI)

          'lt_recorded - assert(m1.ord.lt.contains(aI -> bI))
        }

        'lt_eq - {
          val m1 = m0 tell LT_EQ('a, 'b)

          'contains_a - assert(m1.i.v2i.contains('a))
          'contains_b - assert(m1.i.v2i.contains('b))

          val aI = m1.i.v2i('a)
          val bI = m1.i.v2i('b)

          'distinct_interpretations - assert(aI != bI)

          'lteq_recorded - assert(m1.ord.lt_eq.contains(aI -> bI))
        }

        'not_eq - {
          val m1 = m0 tell NOT_EQ('a, 'b)

          'contains_a - assert(m1.i.v2i.contains('a))
          'contains_b - assert(m1.i.v2i.contains('b))

          val aI = m1.i.v2i('a)
          val bI = m1.i.v2i('b)

          'distinct_interpretations - assert(aI != bI)

          'noteq_recorded - assert(m1.ord.not_eq.contains(aI -> bI))
        }

        'eq - {
          'implicits - {
            implicitly[InterpretationSingleton[Symbol, String]]
            implicitly[Tell[EQ[Symbol], Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell EQ('a, 'b)

          'contains_a - assert(m1.i.v2i.contains('a))
          'contains_b - assert(m1.i.v2i.contains('b))

          val aI = m1.i.v2i('a)
          val bI = m1.i.v2i('b)

          'identical_interpretations - assert(aI == bI)
        }
      }

      'index - {

        'at - {
          'implicits - {
            implicitly[Tell[AT[String], IndexModel[String]]]
            implicitly[Tell[AT[String], Model[Symbol, Symbol, String]]]
            implicitly[Interpretation[AT[Symbol], AT[String], Model[Symbol, Symbol, String]]]
            implicitly[Tell[AT[Symbol], Model[Symbol, Symbol, String]]]
            implicitly[Tell[AT[Symbol], DerivationState[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell AT('a, 10) tell AT('b, 21) tell AT('b, 13)

          'contains_a - assert(m1.i.v2i.contains('a))
          'contains_b - assert(m1.i.v2i.contains('b))

          val aI = m1.i.v2i('a)
          val bI = m1.i.v2i('b)

          assert(m1.index.at(aI) contains 10)
          assert(m1.index.at(bI) contains 21)
          assert(m1.index.at(bI) contains 13)
        }

        'suc - {
          'implicits - {
            implicitly[Tell[Suc[String], IndexModel[String]]]
            implicitly[Tell[Suc[String], Model[Symbol, Symbol, String]]]
            implicitly[Tell[Suc[Symbol], Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell Suc('a, 'b)

          val aI = m1.i.v2i('a)
          val bI = m1.i.v2i('b)

          assert(m1.index.suc contains (aI -> bI))
        }
      }

      'strand - {
        'orientation - {

          'implicits - {
            implicitly[Tell[Strand[Symbol], StrandModel[Symbol]]]
            implicitly[Tell[Strand[Symbol], Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell Strand('r, Orientation.+) tell Strand('s, Orientation.+) tell Strand('s, Orientation.-)

          'strand_r - assert(m1.str.strand.contains('r))
          'strand_r_pos - assert(m1.str.strand('r) contains Orientation.+)

          'strand_s - assert(m1.str.strand.contains('s))
          'strand_s_pos - assert(m1.str.strand('s) contains Orientation.+)
          'strand_s_neg - assert(m1.str.strand('s) contains Orientation.-)
        }

        'same_strand_as {
          'implicits - {
            implicitly[Tell[SameStrandAs[Symbol], StrandModel[Symbol]]]
            implicitly[Tell[SameStrandAs[Symbol], Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell SameStrandAs('r, 's)

          assert(m1.str.same_strand_as contains ('r -> 's))
        }

        'different_strand_to - {

          'implicits - {
            implicitly[Tell[DifferentStrandTo[Symbol], StrandModel[Symbol]]]
            implicitly[Tell[DifferentStrandTo[Symbol], Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell DifferentStrandTo('r, 's)

          assert(m1.str.different_strand_to contains ('r -> 's))
        }
      }

      'length - {

        'length - {
          'implicits - {
            implicitly[Tell[Length[Symbol], LengthModel[Symbol]]]
            implicitly[Tell[Length[Symbol], Model[Symbol, Symbol, String]]]
            implicitly[Tell[Length[Symbol], DerivationState[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell Length('a, 100)

          assert(m1.length.length('a) contains 100)
        }

      }
    }

  }
  
}
