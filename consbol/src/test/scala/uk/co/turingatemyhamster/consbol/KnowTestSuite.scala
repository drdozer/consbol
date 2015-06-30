package uk.co.turingatemyhamster.consbol


import utest._


object KnowTestSuite extends TestSuite {

  val tests = TestSuite {

    import Tell._
    import Know._

    'tell - {
      val m0 = Model.empty[Symbol, String]

      'lt - {
        'implicits - {
          implicitly[Know[LT[String], OrdModel[String]]]
          implicitly[Know[LT[String], Model[Symbol, String]]]
          implicitly[Know[LT[Symbol], Model[Symbol, String]]]
        }

        val m1 = m0 tell LT('a, 'b)
        val k = m1 know LT('a, 'b)

        'got_result - assert(k.nonEmpty)
        'got_right_result - assert(k.head.result == LT('a, 'b))
        'got_only_one_result - assert(k.tail.isEmpty)
      }

      'lt_eq - {
        'implicits - {
          implicitly[Know[LT_EQ[String], OrdModel[String]]]
          implicitly[Know[LT_EQ[String], Model[Symbol, String]]]
          implicitly[Know[LT_EQ[Symbol], Model[Symbol, String]]]
        }

        val m1 = m0 tell LT_EQ('a, 'b)
        val k = m1 know LT_EQ('a, 'b)

        'got_result - assert(k.nonEmpty)
        'got_right_result - assert(k.head.result == LT_EQ('a, 'b))
        'got_only_one_result - assert(k.tail.isEmpty)
      }

      'not_eq - {
        'implicits - {
          implicitly[Know[NOT_EQ[String], OrdModel[String]]]
          implicitly[Know[NOT_EQ[String], Model[Symbol, String]]]
          implicitly[Know[NOT_EQ[Symbol], Model[Symbol, String]]]
        }

        val m1 = m0 tell NOT_EQ('a, 'b)
        val k = m1 know NOT_EQ('a, 'b)

        'got_result - assert(k.nonEmpty)
        'got_right_result - assert(k.head.result == NOT_EQ('a, 'b))
        'got_only_one_result - assert(k.tail.isEmpty)
      }

      'eq - {
        'implicits - {
          implicitly[Know[EQ[String], InterpModel[Symbol, String]]]
          implicitly[Interpretation[EQ[Symbol], EQ[String], Model[Symbol, String]]]
          implicitly[Know[EQ[String], Model[Symbol, String]]]
          implicitly[Know[EQ[Symbol], Model[Symbol, String]]]
        }

        val m1 = m0 tell EQ('a, 'b)
        val k = m1 know EQ('a, 'b)

        'got_result - assert(k.nonEmpty)
        'got_right_result - assert(k.head.result == EQ('a, 'b))
        'got_only_one_result - assert(k.tail.isEmpty)
      }
    }
  }

}
