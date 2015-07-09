package uk.co.turingatemyhamster.consbol


import utest._


object KnowTestSuite extends TestSuite {

  val tests = TestSuite {

    import Tell._
    import Know._

    'tell - {
      val m0 = Model.empty[Symbol, Symbol, String]

      'lt - {
        'implicits - {
          implicitly[Know[LT, String, OrdModel[String]]]
          implicitly[Know[LT, String, Model[Symbol, Symbol, String]]]
          implicitly[Know[LT, Symbol, Model[Symbol, Symbol, String]]]
        }

        val m1 = m0 tell LT('a, 'b)
        val k = m1 know LT('a, 'b)

        'got_result - assert(!k.isEmpty.value)
        'got_right_result - assert(k.head.value.goal == LT('a, 'b))
        'got_only_one_result - assert(k.tail.isEmpty.value)
      }

      'lt_eq - {
        'implicits - {
          implicitly[Know[LT_EQ, String, OrdModel[String]]]
          implicitly[Know[LT_EQ, String, Model[Symbol, Symbol, String]]]
          implicitly[Know[LT_EQ, Symbol, Model[Symbol, Symbol, String]]]
        }

        val m1 = m0 tell LT_EQ('a, 'b)
        val k = m1 know LT_EQ('a, 'b)

        'got_result - assert(!k.isEmpty.value)
        'got_right_result - assert(k.head.value.goal == LT_EQ('a, 'b))
        'got_only_one_result - assert(k.tail.isEmpty.value)
      }

      'not_eq - {
        'implicits - {
          implicitly[Know[NOT_EQ, String, OrdModel[String]]]
          implicitly[Know[NOT_EQ, String, Model[Symbol, Symbol, String]]]
          implicitly[Know[NOT_EQ, Symbol, Model[Symbol, Symbol, String]]]
        }

        val m1 = m0 tell NOT_EQ('a, 'b)
        val k = m1 know NOT_EQ('a, 'b)

        'got_result - assert(!k.isEmpty.value)
        'got_right_result - assert(k.head.value.goal == NOT_EQ('a, 'b))
        'got_only_one_result - assert(k.tail.isEmpty.value)
      }

      'eq - {
        'implicits - {
          implicitly[Know[EQ, String, InterpModel[Symbol, String]]]
          implicitly[Interpretation[EQ[Symbol], EQ[String], Model[Symbol, Symbol, String]]]
          implicitly[Know[EQ, String, Model[Symbol, Symbol, String]]]
          implicitly[Know[EQ, Symbol, Model[Symbol, Symbol, String]]]
        }

        val m1 = m0 tell EQ('a, 'b)
        val k = m1 know EQ('a, 'b)

        'got_result - assert(!k.isEmpty.value)
        'got_right_result - assert(k.head.value.goal == EQ('a, 'b))
        'got_only_one_result - assert(k.tail.isEmpty.value)
      }

      'at - {

        'implicits - {
          implicitly[Know[AT, String, IndexModel[String]]]
          implicitly[Know[AT, String, Model[Symbol, Symbol, String]]]
          implicitly[Interpretation[AT[Symbol], AT[String], Model[Symbol, Symbol, String]]]
          implicitly[Know[AT, Symbol, Model[Symbol, Symbol, String]]]
        }

        val m1 = m0 tell AT('a, 11)

        val ka_11 = m1 know AT('a, 11)
        val ka_12 = m1 know AT('a, 12)

        'got_result_11 - assert(!ka_11.isEmpty.value)
        'got_right_result_11 - assert(ka_11.head.value.goal == AT('a, 11))
        'got_only_one_result_11 - assert(ka_11.tail.isEmpty.value)

        'got_no_result_12 - assert(ka_12.isEmpty.value)
      }

      'strand - {

        'implicits - {
          implicitly[Know[Strand, Symbol, StrandModel[Symbol]]]
          implicitly[Know[Strand, Symbol, Model[Symbol, Symbol, String]]]
        }

        val m1 = m0 tell Strand('r, Orientation.+)

        val k = m1 know Strand('r, Orientation.+)

        'got_result - assert(!k.isEmpty.value)
        'got_right_result - assert(k.head.value.goal == Strand('r, Orientation.+))
      }

      'same_strand_as - {

        'implicits - {
          implicitly[Know[SameStrandAs, Symbol, StrandModel[Symbol]]]
          implicitly[Know[SameStrandAs, Symbol, Model[Symbol, Symbol, String]]]
        }

        val m1 = m0 tell SameStrandAs('r, 's)
        val k = m1 know SameStrandAs('r, 's)

        'got_result - assert(!k.isEmpty.value)
        'got_right_result - assert(k.head.value.goal == SameStrandAs('r, 's))
      }

      'different_strand_to - {

        'implicits - {
          implicitly[Know[DifferentStrandTo, Symbol, StrandModel[Symbol]]]
          implicitly[Know[DifferentStrandTo, Symbol, Model[Symbol, Symbol, String]]]
        }

        val m1 = m0 tell DifferentStrandTo('r, 's)
        val k = m1 know DifferentStrandTo('r, 's)

        'got_result - assert(!k.isEmpty.value)
        'got_right_result - assert(k.head.value.goal == DifferentStrandTo('r, 's))

      }
    }
  }

}
