package uk.co.turingatemyhamster.consbol


import utest._


object DeriveTestSuite extends TestSuite {

  val tests = TestSuite {
    import Tell._
    import Know._
    import Derive._

    val m0 = Model.empty[Symbol, String]

    'derive - {
      'lt - {

        'implicits - {
          implicitly[Interpretations[String, InterpModel[Symbol, String]]]
          implicitly[Interpretations[String, Model[Symbol, String]]]
          implicitly[Derive[LT[String], Model[Symbol, String]]]
          implicitly[Derive[LT[Symbol], Model[Symbol, String]]]
        }

        'derive_told - {

          val m1 = m0 tell LT('a, 'b)
          val d = m1 derive LT('a, 'b)

          'got_result - assert(!d.isEmpty.value)
          'result_is_correct - assert(d.head.value._1.result == LT('a, 'b))
          'one_result - assert(d.tail.isEmpty.value)
        }

        'derive_lt_lt - {

          val m1 = m0 tell LT('a, 'b) tell LT('b, 'c)

          val k_before = m1 know LT('a, 'c)

          val d_ab = m1 derive LT('a, 'b) map (_._1)
          val d_bc = m1 derive LT('b, 'c) map (_._1)
          val d_ac = m1 derive LT('a, 'c) map (_._1)

          val d_ba = m1 derive LT('b, 'a) map (_._1)
          val d_cb = m1 derive LT('c, 'b) map (_._1)
          val d_ca = m1 derive LT('c, 'a) map (_._1)

          'ac_unknown_before - assert(k_before.isEmpty.value)

          'ab_1 - assert(d_ab.length.value == 1)
          'ab_correct - assert(d_ab.head.value.result == LT('a, 'b))
          'bc_1 - assert(d_bc.length.value == 1)
          'bc_correct - assert(d_bc.head.value.result == LT('b, 'c))
          'ac_correct - assert(d_ac.head.value.result == LT('a, 'c))

          'ba - assert(d_ba.isEmpty.value)
          'cb - assert(d_cb.isEmpty.value)
          'ca - assert(d_ca.isEmpty.value)

          val k_after = (m1 derive LT('a, 'c)).head.value._2 know LT('a, 'c)

          'ac_known_after - assert(!k_after.isEmpty.value)
        }
//
//        'derive_lt_lt_eq - {
//
//          val m1 = m0 tell LT('a, 'b) tell LT_EQ('b, 'c)
//
//          val k_before = m1 know LT('a, 'c)
//
//          val d_ab = m1 derive LT('a, 'b) map (_._1)
//          val d_bc = m1 derive LT_EQ('b, 'c) map (_._1)
//          val d_ac = m1 derive LT('a, 'c) map (_._1)
//
//          val d_ba = m1 derive LT('b, 'a) map (_._1)
//          val d_cb = m1 derive LT('c, 'b) map (_._1)
//          val d_ca = m1 derive LT('c, 'a) map (_._1)
//
//          'ac_unknown_before - assert(k_before.isEmpty.value)
//
//          'ab_1 - assert(d_ab.length.value == 1)
//          'ab_correct - assert(d_ab.head.value.result == LT('a, 'b))
//          'bc_1 - assert(d_bc.length.value == 1)
//          'bc_correct - assert(d_bc.head.value.result == LT_EQ('b, 'c))
//          'ac_correct - assert(d_ac.head.value.result == LT('a, 'c))
//
//          'ba - assert(d_ba.isEmpty.value)
//          'cb - assert(d_cb.isEmpty.value)
//          'ca - assert(d_ca.isEmpty.value)
//
//          val k_after = (m1 derive LT('a, 'c)).head.value._2 know LT('a, 'c)
//
//          'ac_known_after - assert(!k_after.isEmpty.value)
//        }
//
//        'derive_lt_eq_lt - {
//
//          val m1 = m0 tell LT_EQ('a, 'b) tell LT('b, 'c)
//
//          val k_before = m1 know LT('a, 'c)
//
//          val d_ab = m1 derive LT_EQ('a, 'b) map (_._1)
//          val d_bc = m1 derive LT('b, 'c) map (_._1)
//          val d_ac = m1 derive LT('a, 'c) map (_._1)
//
//          val d_ba = m1 derive LT('b, 'a) map (_._1)
//          val d_cb = m1 derive LT('c, 'b) map (_._1)
//          val d_ca = m1 derive LT('c, 'a) map (_._1)
//
//          'ac_unknown_before - assert(k_before.isEmpty.value)
//
//          'ab_1 - assert(d_ab.length.value == 1)
//          'ab_correct - assert(d_ab.head.value.result == LT_EQ('a, 'b))
//          'bc_1 - assert(d_bc.length.value == 1)
//          'bc_correct - assert(d_bc.head.value.result == LT('b, 'c))
//          'ac_correct - assert(d_ac.head.value.result == LT('a, 'c))
//
//          'ba - assert(d_ba.isEmpty.value)
//          'cb - assert(d_cb.isEmpty.value)
//          'ca - assert(d_ca.isEmpty.value)
//
//          val k_after = (m1 derive LT('a, 'c)).head.value._2 know LT('a, 'c)
//
//          'ac_known_after - assert(!k_after.isEmpty.value)
//        }
//
//        'derive_lt_eq_lt_eq - {
//
//          val m1 = m0 tell LT_EQ('a, 'b) tell LT_EQ('b, 'c)
//
//          val k_before = m1 know LT('a, 'c)
//
//          val d_ab = m1 derive LT_EQ('a, 'b) map (_._1)
//          val d_bc = m1 derive LT_EQ('b, 'c) map (_._1)
//          val d_ac = m1 derive LT('a, 'c) map (_._1)
//
//          val d_ba = m1 derive LT('b, 'a) map (_._1)
//          val d_cb = m1 derive LT('c, 'b) map (_._1)
//          val d_ca = m1 derive LT('c, 'a) map (_._1)
//
//          'ac_unknown_before - assert(k_before.isEmpty.value)
//
//          'ab_1 - assert(d_ab.length.value == 1)
//          'ab_correct - assert(d_ab.head.value.result == LT_EQ('a, 'b))
//          'bc_1 - assert(d_bc.length.value == 1)
//          'bc_correct - assert(d_bc.head.value.result == LT_EQ('b, 'c))
////          'ac_correct - assert(d_ac.head.result == LT('a, 'c))
//
//          'ba - assert(d_ba.isEmpty.value)
//          'cb - assert(d_cb.isEmpty.value)
//          'ca - assert(d_ca.isEmpty.value)
//
//          val m2 = (m1 derive LT('a, 'c)) map (_._2)
////          val k_after = m2.head know LT('a, 'c)
//
////          'ac_known_after - assert(k_after.nonEmpty)
//        }
//
      }
    }
  }
}
