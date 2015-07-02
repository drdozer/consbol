package uk.co.turingatemyhamster.consbol


import utest._


object DeriveTestSuite extends TestSuite {

  val tests = TestSuite {
    import Tell._
    import Know._
    import Derive._

    val m0 = Model.empty[Symbol, Symbol, String]

    'derive_relative - {
      'lt - {

        'implicits - {
          implicitly[Interpretation[Symbol, String, InterpModel[Symbol, String]]]
          implicitly[Interpretation[LT[Symbol], LT[String], Model[Symbol, Symbol, String]]]
          implicitly[Derive[LT[String], Model[Symbol, Symbol, String]]]
          implicitly[Derive[LT[Symbol], Model[Symbol, Symbol, String]]]
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

        'derive_lt_lt_eq - {

          val m1 = m0 tell LT('a, 'b) tell LT_EQ('b, 'c)

          val k_before = m1 know LT('a, 'c)

          val d_ab = m1 derive LT('a, 'b) map (_._1)
          val d_bc = m1 derive LT_EQ('b, 'c) map (_._1)
          val d_ac = m1 derive LT('a, 'c) map (_._1)

          val d_ba = m1 derive LT('b, 'a) map (_._1)
          val d_cb = m1 derive LT('c, 'b) map (_._1)
          val d_ca = m1 derive LT('c, 'a) map (_._1)

          'ac_unknown_before - assert(k_before.isEmpty.value)

          'ab_1 - assert(d_ab.length.value == 1)
          'ab_correct - assert(d_ab.head.value.result == LT('a, 'b))
          'bc_1 - assert(d_bc.length.value == 1)
          'bc_correct - assert(d_bc.head.value.result == LT_EQ('b, 'c))
          'ac_correct - assert(d_ac.head.value.result == LT('a, 'c))

          'ba - assert(d_ba.isEmpty.value)
          'cb - assert(d_cb.isEmpty.value)
          'ca - assert(d_ca.isEmpty.value)

          val k_after = (m1 derive LT('a, 'c)).head.value._2 know LT('a, 'c)

          'ac_known_after - assert(!k_after.isEmpty.value)
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

          'ac_unknown_before - assert(k_before.isEmpty.value)

          'ab_1 - assert(d_ab.length.value == 1)
          'ab_correct - assert(d_ab.head.value.result == LT_EQ('a, 'b))
          'bc_1 - assert(d_bc.length.value == 1)
          'bc_correct - assert(d_bc.head.value.result == LT('b, 'c))
          'ac_correct - assert(d_ac.head.value.result == LT('a, 'c))

          'ba - assert(d_ba.isEmpty.value)
          'cb - assert(d_cb.isEmpty.value)
          'ca - assert(d_ca.isEmpty.value)

          val k_after = (m1 derive LT('a, 'c)).head.value._2 know LT('a, 'c)

          'ac_known_after - assert(!k_after.isEmpty.value)
        }

      }

      'lt_eq - {

        'derive_told - {

          val m1 = m0 tell LT_EQ('a, 'b)
          val d = m1 derive LT_EQ('a, 'b)

          'got_result - assert(!d.isEmpty.value)
          'result_is_correct - assert(d.head.value._1.result == LT_EQ('a, 'b))
          'one_result - assert(d.tail.isEmpty.value)
        }

        'derive_lt_eq_lt_eq - {

          val m1 = m0 tell LT_EQ('a, 'b) tell LT_EQ('b, 'c)

          val k_ab = m1 know LT_EQ('a, 'b)
          val k_bc = m1 know LT_EQ('b, 'c)

          'kab - assert(k_ab.head.value.result == LT_EQ('a, 'b))
          'kbc - assert(k_bc.head.value.result == LT_EQ('b, 'c))

          val k_before = m1 know LT_EQ('a, 'c)

          val d_ab = m1 derive LT_EQ('a, 'b) map (_._1)
          val d_bc = m1 derive LT_EQ('b, 'c) map (_._1)
          val d_ac = m1 derive LT_EQ('a, 'c) map (_._1)

          val d_ba = m1 derive LT_EQ('b, 'a) map (_._1)
          val d_cb = m1 derive LT_EQ('c, 'b) map (_._1)
          val d_ca = m1 derive LT_EQ('c, 'a) map (_._1)

          'ac_unknown_before - assert(k_before.isEmpty.value)

          'ab_1 - assert(!d_ab.isEmpty.value)
          'ab_correct - assert(d_ab.head.value.result == LT_EQ('a, 'b))
          'bc_1 - assert(!d_bc.isEmpty.value)
          'bc_correct - assert(d_bc.head.value.result == LT_EQ('b, 'c))
          'ac_1 - assert(!d_bc.isEmpty.value)
          'ac_correct - assert(d_ac.head.value.result == LT_EQ('a, 'c))

          'ba - assert(d_ba.isEmpty.value)
          'cb - assert(d_cb.isEmpty.value)
          'ca - assert(d_ca.isEmpty.value)

          val k_after = (m1 derive LT_EQ('a, 'c)).head.value._2 know LT_EQ('a, 'c)

          'ac_known_after - assert(!k_after.isEmpty.value)
        }
      }
    }

    'derive_at - {
      'lt - {

        'implicits - {
          implicitly[Derive[AT[String], Model[Symbol, Symbol, String]]]
          implicitly[Derive[AT[Symbol], Model[Symbol, Symbol, String]]]
        }

        'derive_told {
          val m1 = m0 tell AT('a, 10) tell AT('b, 20)

          val d_a = m1 derive AT('a, 10)
          val d_b = m1 derive AT('b, 20)

          'got_result_a - assert(!d_a.isEmpty.value)
          'result_is_correct_a - assert(d_a.head.value._1.result == AT('a, 10))
          'one_result_b - assert(d_a.tail.isEmpty.value)

          'got_result_b - assert(!d_b.isEmpty.value)
          'result_is_correct_b - assert(d_b.head.value._1.result == AT('b, 20))
          'one_result_b - assert(d_b.tail.isEmpty.value)
        }

        'derive_lt - {

          val m1 = m0 tell AT('a, 10) tell AT('b, 20)

          val d = m1 derive LT('a, 'b)

          'got_result - assert(!d.isEmpty.value)
          'result_is_correct - assert(d.head.value._1.result == LT('a, 'b))
        }
      }

      'lt_eq - {

        'when_lt - {

          val m1 = m0 tell AT('a, 10) tell AT('b, 20)

          val d = m1 derive LT_EQ('a, 'b)

          'got_result - assert(!d.isEmpty.value)
          'result_is_correct - assert(d.head.value._1.result == LT_EQ('a, 'b))

          val k = d.head.value._2 know LT_EQ('a, 'b)

          'known_after - assert(!k.isEmpty.value)
        }

        'when_eq - {

          val m1 = m0 tell AT('a, 10) tell AT('b, 10)

          val d = m1 derive LT_EQ('a, 'b)

          'got_result - assert(!d.isEmpty.value)
          'result_is_correct - assert(d.head.value._1.result == LT_EQ('a, 'b))

          val k = d.head.value._2 know LT_EQ('a, 'b)

          'known_after - assert(!k.isEmpty.value)
        }

      }

      'eq - {

        val m1 = m0 tell AT('a, 10) tell AT('b, 10)

        val d = m1 derive EQ('a, 'b)

        'got_result - assert(!d.isEmpty.value)
        'result_is_correct - assert(d.head.value._1.result == EQ('a, 'b))

        val k = d.head.value._2 know EQ('a, 'b)

        'known_after - assert(!k.isEmpty.value)

      }

      'not_eq - {
        val m1 = m0 tell AT('a, 10) tell AT('b, 20)

        val d = m1 derive NOT_EQ('a, 'b)

        'got_result - assert(!d.isEmpty.value)
        'result_is_correct - assert(d.head.value._1.result == NOT_EQ('a, 'b))

        val k = d.head.value._2 know NOT_EQ('a, 'b)

        'known_after - assert(!k.isEmpty.value)
      }
    }

    'derive_strand - {
      'implicits {
        implicitly[Derive[Strand[Symbol], Model[Symbol, Symbol, String]]]
      }

      val m1 = m0 tell Strand('r, Orientation.+) tell Strand('s, Orientation.-) tell Strand('t, Orientation.+)

      val dr = m1 derive Strand('r, Orientation.+)
      val ds = m1 derive Strand('s, Orientation.-)
      val dt = m1 derive Strand('t, Orientation.+)

      'got_result_r - assert(!dr.isEmpty.value)
      'got_corret_result_r - assert(dr.head.value._1.result == Strand('r, Orientation.+))

      'got_result_s - assert(!ds.isEmpty.value)
      'got_corret_result_s - assert(ds.head.value._1.result == Strand('s, Orientation.-))

      'got_result_t - assert(!dt.isEmpty.value)
      'got_corret_result_t - assert(dt.head.value._1.result == Strand('t, Orientation.+))

    }

    'derive_same_strand_as - {
//      'implicits {
//        implicitly[Derive[SameStrandAs[Symbol], Model[Symbol, Symbol, String]]]
//      }
//
//      'from_tell - {
//        val m1 = m0 tell SameStrandAs('r, 's)
//        val d = m1 derive SameStrandAs('r, 's)
//
//        'got_result - assert(!d.isEmpty.value)
//        'result_is_correct - assert(d.head.value._1.result == SameStrandAs('r, 's))
//
//      }
//
//      'from_strand - {
//        val m1 = m0 tell Strand('r, Orientation.-) tell Strand('s, Orientation.-)
//        val d = m1 derive SameStrandAs('r, 's)
//
//        'got_result - assert(!d.isEmpty.value)
//        'result_is_correct - assert(d.head.value._1.result == SameStrandAs('r, 's))
//
//      }
//
//      'same_strand_implies_strand_lr - {
//        val m1 = m0 tell Strand('s, Orientation.+) tell SameStrandAs('r, 's)
//        val d = m1 derive Strand('r, Orientation.+)
//
//        'got_result - assert(!d.isEmpty.value)
//        'result_is_correct - assert(d.head.value._1.result == Strand('r, Orientation.+))
//      }

      'same_strand_implies_strand_rl - {
        val m1 = m0 tell Strand('s, Orientation.+) tell SameStrandAs('s, 'r)
        val d = m1 derive Strand('r, Orientation.+)

        'got_result - assert(!d.isEmpty.value)
        'result_is_correct - assert(d.head.value._1.result == Strand('r, Orientation.+))
      }
    }
  }
}
