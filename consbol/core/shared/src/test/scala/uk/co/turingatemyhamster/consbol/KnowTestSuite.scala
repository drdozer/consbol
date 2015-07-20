package uk.co.turingatemyhamster.consbol


import uk.co.turingatemyhamster.consbol.Derive.DProof
import utest._
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._

object KnowTestSuite extends TestSuite {

  val tests = TestSuite {

    import Tell._
    import Know._

    'tell - {
      val m0 = Model.empty[Symbol, Symbol, String]

      'ord - {

        'lt - {
          'implicits - {
            implicitly[Know[LT, String, OrdModel[String]]]
            implicitly[Know[LT, String, Model[Symbol, Symbol, String]]]
            implicitly[Know[LT, Symbol, Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell LT('a, 'b)
          val k = m1 know LT('a, 'b)

          'got_result - assert(!k.isEmpty.value)
          'got_right_result - assert(checkResult(k, LT('a, 'b)))
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
          'got_right_result - assert(checkResult(k, LT_EQ('a, 'b)))
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
          'got_right_result - assert(checkResult(k, NOT_EQ('a, 'b)))
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
          'got_right_result - assert(checkResult(k, EQ('a, 'b)))
          'got_only_one_result - assert(k.tail.isEmpty.value)
        }
      }

      'index - {
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
          'got_right_result_11 - assert(checkResult(ka_11, AT('a, 11)))
          'got_only_one_result_11 - assert(ka_11.tail.isEmpty.value)

          'got_no_result_12 - assert(ka_12.filter(_.isRight).isEmpty.value)
        }

        'suc - {

          'implicits - {
            implicitly[Know[Suc, String, IndexModel[String]]]
            implicitly[Know[Suc, String, Model[Symbol, Symbol, String]]]
            implicitly[Know[Suc, Symbol, Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell Suc('a, 'b)

          val k = m1 know Suc('a, 'b)

          'got_result - assert(!k.isEmpty.value)
          'got_right_result - assert(checkResult(k, Suc('a, 'b)))

        }
      }

      'strand - {
        'strand - {

          'implicits - {
            implicitly[Know[Strand, Symbol, StrandModel[Symbol]]]
            implicitly[Know[Strand, Symbol, Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell Strand('r, Orientation.+)

          val k = m1 know Strand('r, Orientation.+)

          'got_result - assert(!k.isEmpty.value)
          'got_right_result - assert(checkResult(k, Strand('r, Orientation.+)))
        }

        'same_strand_as - {

          'implicits - {
            implicitly[Know[SameStrandAs, Symbol, StrandModel[Symbol]]]
            implicitly[Know[SameStrandAs, Symbol, Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell SameStrandAs('r, 's)
          val k = m1 know SameStrandAs('r, 's)

          'got_result - assert(!k.isEmpty.value)
          'got_right_result - assert(checkResult(k, SameStrandAs('r, 's)))
        }

        'different_strand_to - {

          'implicits - {
            implicitly[Know[DifferentStrandTo, Symbol, StrandModel[Symbol]]]
            implicitly[Know[DifferentStrandTo, Symbol, Model[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell DifferentStrandTo('r, 's)
          val k = m1 know DifferentStrandTo('r, 's)

          'got_result - assert(!k.isEmpty.value)
          'got_right_result - assert(checkResult(k, DifferentStrandTo('r, 's)))

        }
      }

      'length - {

        'length - {

          'implicits - {
            implicitly[Know[Length, Symbol, LengthModel[Symbol]]]
            implicitly[Know[Length, Symbol, Model[Symbol, Symbol, String]]]
            implicitly[Know[Length, Symbol, DerivationState[Symbol, Symbol, String]]]
          }

          val m1 = m0 tell Length('a, 100)

          val k = m1 know Length('a, 100)

          'got_result - assert(!k.isEmpty.value)
          'got_right_result - assert(checkResult(k, Length('a, 100)))

        }

      }
    }
  }

  def checkResult[A](k: TrueStream[DProof[A]], a: A): Boolean =
    k.head.value.fold(_ => false, _.goal == a)
}
