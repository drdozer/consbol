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

          'got_result - assert(d.nonEmpty)
          'result_is_correct - assert(d.head._1.result == LT('a, 'b))
          'one_result - assert(d.tail.isEmpty)
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

          'ac_unknown_before - assert(k_before.isEmpty)

          'ab_1 - assert(d_ab.length == 1)
          'ab_correct - assert(d_ab.head.result == LT('a, 'b))
          'bc_1 - assert(d_bc.length == 1)
          'bc_correct - assert(d_bc.head.result == LT('b, 'c))
          'ac_correct - assert(d_ac.head.result == LT('a, 'c))

          'ba - assert(d_ba.isEmpty)
          'cb - assert(d_cb.isEmpty)
          'ca - assert(d_ca.isEmpty)

          val k_after = (m1 derive LT('a, 'c)).head._2 know LT('a, 'c)

          'ac_known_after - assert(k_after.nonEmpty)
        }

        'derive_lt_lt_eq - {

          val m1 = m0 tell LT('a, 'b) tell LT_EQ('b, 'c)

          val k_before = m1 know LT('a, 'c)

          val d_ab = m1 derive LT('a, 'b) map (_._1)
          val d_bc = m1 derive LT_EQ('b, 'c) map (_._1)
          val d_ac = m1 derive LT('a, 'c) map (_._1)

          val d_ba = m1 derive LT('b, 'a) map (_._1)
          val d_cb = m1 derive LT('c, 'b) map (_._1)
          val d_ca = m1 derive LT('c, 'a) map (_._1)

          'ac_unknown_before - assert(k_before.isEmpty)

          'ab_1 - assert(d_ab.length == 1)
          'ab_correct - assert(d_ab.head.result == LT('a, 'b))
          'bc_1 - assert(d_bc.length == 1)
          'bc_correct - assert(d_bc.head.result == LT_EQ('b, 'c))
          'ac_correct - assert(d_ac.head.result == LT('a, 'c))

          'ba - assert(d_ba.isEmpty)
          'cb - assert(d_cb.isEmpty)
          'ca - assert(d_ca.isEmpty)

          val k_after = (m1 derive LT('a, 'c)).head._2 know LT('a, 'c)

          'ac_known_after - assert(k_after.nonEmpty)
        }

        'derive_lt_eq_lt - {

          val m1 = m0 tell LT_EQ('a, 'b) tell LT('b, 'c)

          val k_before = m1 know LT('a, 'c)

          val d_ab = m1 derive LT_EQ('a, 'b) map (_._1)
          val d_bc = m1 derive LT('b, 'c) map (_._1)
          val d_ac = m1 derive LT('a, 'c) map (_._1)

          val d_ba = m1 derive LT('b, 'a) map (_._1)
          val d_cb = m1 derive LT('c, 'b) map (_._1)
          val d_ca = m1 derive LT('c, 'a) map (_._1)

          'ac_unknown_before - assert(k_before.isEmpty)

          'ab_1 - assert(d_ab.length == 1)
          'ab_correct - assert(d_ab.head.result == LT_EQ('a, 'b))
          'bc_1 - assert(d_bc.length == 1)
          'bc_correct - assert(d_bc.head.result == LT('b, 'c))
          'ac_correct - assert(d_ac.head.result == LT('a, 'c))

          'ba - assert(d_ba.isEmpty)
          'cb - assert(d_cb.isEmpty)
          'ca - assert(d_ca.isEmpty)

          val k_after = (m1 derive LT('a, 'c)).head._2 know LT('a, 'c)

          'ac_known_after - assert(k_after.nonEmpty)
        }

        'derive_lt_eq_lt_eq - {

          val m1 = m0 tell LT_EQ('a, 'b) tell LT_EQ('b, 'c)

          val k_before = m1 know LT('a, 'c)

          val d_ab = m1 derive LT_EQ('a, 'b) map (_._1)
          val d_bc = m1 derive LT_EQ('b, 'c) map (_._1)
          val d_ac = m1 derive LT('a, 'c) map (_._1)

          val d_ba = m1 derive LT('b, 'a) map (_._1)
          val d_cb = m1 derive LT('c, 'b) map (_._1)
          val d_ca = m1 derive LT('c, 'a) map (_._1)

          'ac_unknown_before - assert(k_before.isEmpty)

          'ab_1 - assert(d_ab.length == 1)
          'ab_correct - assert(d_ab.head.result == LT_EQ('a, 'b))
          'bc_1 - assert(d_bc.length == 1)
          'bc_correct - assert(d_bc.head.result == LT_EQ('b, 'c))
//          'ac_correct - assert(d_ac.head.result == LT('a, 'c))

          'ba - assert(d_ba.isEmpty)
          'cb - assert(d_cb.isEmpty)
          'ca - assert(d_ca.isEmpty)

          val m2 = (m1 derive LT('a, 'c)) map (_._2)
//          val k_after = m2.head know LT('a, 'c)

//          'ac_known_after - assert(k_after.nonEmpty)
        }

      }
    }
  }
}
