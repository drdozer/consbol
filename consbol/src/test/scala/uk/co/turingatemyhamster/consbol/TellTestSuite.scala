package uk.co.turingatemyhamster.consbol

import utest._

object TellTestSuite extends TestSuite {

  val tests = TestSuite {

    import Tell._

    'tell - {
      val m0 = Model.empty[Symbol, String]

      'lt - {

        'implicits - {
          implicitly[Tell[LT[String], OrdModel[String]]]
          implicitly[Tell[LT[String], Model[Symbol, String]]]
          implicitly[InterpretationSingleton[Symbol, String]]
          implicitly[Interpretation[Symbol, String, Model[Symbol, String]]]
          implicitly[Interpretation[LT[Symbol], LT[String], Model[Symbol, String]]]
          implicitly[Tell[LT[Symbol], Model[Symbol, String]]]
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
          implicitly[Tell[EQ[Symbol], Model[Symbol, String]]]
        }

        val m1 = m0 tell EQ('a, 'b)

        'contains_a - assert(m1.i.v2i.contains('a))
        'contains_b - assert(m1.i.v2i.contains('b))

        val aI = m1.i.v2i('a)
        val bI = m1.i.v2i('b)

        'identical_interpretations - assert(aI == bI)
      }

      'at - {
        'implicits - {
          implicitly[Tell[AT[String], IndexModel[String]]]
          implicitly[Tell[AT[String], Model[Symbol, String]]]
          implicitly[Interpretation[AT[Symbol], AT[String], Model[Symbol, String]]]
          implicitly[Tell[AT[Symbol], Model[Symbol, String]]]
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
    }

  }
  
}
