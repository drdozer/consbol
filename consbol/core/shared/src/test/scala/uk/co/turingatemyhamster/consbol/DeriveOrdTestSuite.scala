package uk.co.turingatemyhamster.consbol


import utest._
import scalaz._
import scalaz.Scalaz._
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._

object DeriveOrdTestSuite extends TestSuite with DeriveTestSuite {

  val tests = TestSuite {
    import Tell._
    import Know._
    import Derive._
    import ds0.env._

    'lt - {

      'implicits - {
        implicitly[Interpretation[Symbol, String, InterpModel[Symbol, String]]]
        implicitly[Interpretation[LT[Symbol], LT[String], Model[Symbol, Symbol, String]]]
        implicitly[Derive[LT[String], Symbol, Symbol, String]]
        implicitly[Derive[LT[Symbol], Symbol, Symbol, String]]
      }

      'derive_told - {

        val ds1 = ds0 tell LT('a, 'b)
        val d = ds1 |- LT('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT('a, 'b))
        'one_goal - assert(d.tail.isEmpty.value)
      }

      'derive_lt_lt - {

        val ds1 = ds0 tell LT('a, 'b) tell LT('b, 'c)

        val k_before = ds1 know LT('a, 'c)

        val d_ab = ds1 |- LT('a, 'b)
        val d_bc = ds1 |- LT('b, 'c)
        val d_ac = ds1 |- LT('a, 'c)

        val d_ba = ds1 |- LT('b, 'a)
        val d_cb = ds1 |- LT('c, 'b)
        val d_ca = ds1 |- LT('c, 'a)

        'ac_unknown_before - assert(k_before.filter(_.isRight).isEmpty.value)

        'ab_1 - assert(d_ab.length.value == 1)
        'ab_correct - assert(d_ab.head.value.goal == LT('a, 'b))
        'bc_1 - assert(d_bc.length.value == 1)
        'bc_correct - assert(d_bc.head.value.goal == LT('b, 'c))
        'ac_correct - assert(d_ac.head.value.goal == LT('a, 'c))

        'ba - assert(d_ba.isEmpty.value)
        'cb - assert(d_cb.isEmpty.value)
        'ca - assert(d_ca.isEmpty.value)

        val k_after = (ds1 |-- LT('a, 'c)).head.value know LT('a, 'c)

        'ac_known_after - assert(!k_after.isEmpty.value)
      }

      'derive_lt_lt_eq - {

        val ds1 = ds0 tell LT('a, 'b) tell LT_EQ('b, 'c)

        val k_before = ds1 know LT('a, 'c)

        val d_ab = ds1 |- LT('a, 'b)
        val d_bc = ds1 |- LT_EQ('b, 'c)
        val d_ac = ds1 |- LT('a, 'c)

        val d_ba = ds1 |- LT('b, 'a)
        val d_cb = ds1 |- LT('c, 'b)
        val d_ca = ds1 |- LT('c, 'a)

        'ac_unknown_before - assert(k_before.filter(_.isRight).isEmpty.value)

        'ab_1 - assert(d_ab.length.value == 1)
        'ab_correct - assert(d_ab.head.value.goal == LT('a, 'b))
        'bc_1 - assert(d_bc.length.value == 1)
        'bc_correct - assert(d_bc.head.value.goal == LT_EQ('b, 'c))
        'ac_correct - assert(d_ac.head.value.goal == LT('a, 'c))

        'ba - assert(d_ba.isEmpty.value)
        'cb - assert(d_cb.isEmpty.value)
        'ca - assert(d_ca.isEmpty.value)

        val k_after = (ds1 |-- LT('a, 'c)).head.value know LT('a, 'c)

        'ac_known_after - assert(!k_after.isEmpty.value)
      }

      'derive_lt_eq_lt - {

        val ds1 = ds0 tell LT_EQ('a, 'b) tell LT('b, 'c)

        val k_before = ds1 know LT('a, 'c)

        val d_ab = ds1 |- LT_EQ('a, 'b)
        val d_bc = ds1 |- LT('b, 'c)
        val d_ac = ds1 |- LT('a, 'c)

        val d_ba = ds1 |- LT('b, 'a)
        val d_cb = ds1 |- LT('c, 'b)
        val d_ca = ds1 |- LT('c, 'a)

        'ac_unknown_before - assert(k_before.filter(_.isRight).isEmpty.value)

        'ab_1 - assert(d_ab.length.value == 1)
        'ab_correct - assert(d_ab.head.value.goal == LT_EQ('a, 'b))
        'bc_1 - assert(d_bc.length.value == 1)
        'bc_correct - assert(d_bc.head.value.goal == LT('b, 'c))
        'ac_correct - assert(d_ac.head.value.goal == LT('a, 'c))

        'ba - assert(d_ba.isEmpty.value)
        'cb - assert(d_cb.isEmpty.value)
        'ca - assert(d_ca.isEmpty.value)

        val k_after = (ds1 |-- LT('a, 'c)).head.value know LT('a, 'c)

        'ac_known_after - assert(!k_after.isEmpty.value)
      }

    }

    'lt_eq - {

      'derive_told - {

        val ds1 = ds0 tell LT_EQ('a, 'b)
        val d = ds1 |- LT_EQ('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT_EQ('a, 'b))
        'one_goal - assert(d.tail.isEmpty.value)
      }

      'derive_lt_eq_lt_eq - {

        val ds1 = ds0 tell LT_EQ('a, 'b) tell LT_EQ('b, 'c)

        val k_ab = ds1 know LT_EQ('a, 'b)
        val k_bc = ds1 know LT_EQ('b, 'c)

        'kab - assert(k_ab.head.value.fold(_ => false, _.goal == LT_EQ('a, 'b)))
        'kbc - assert(k_bc.head.value.fold(_ => false, _.goal == LT_EQ('b, 'c)))

        val k_before = ds1 know LT_EQ('a, 'c)

        val d_ab = ds1 |- LT_EQ('a, 'b)
        val d_bc = ds1 |- LT_EQ('b, 'c)
        val d_ac = ds1 |- LT_EQ('a, 'c)

        val d_ba = ds1 |- LT_EQ('b, 'a)
        val d_cb = ds1 |- LT_EQ('c, 'b)
        val d_ca = ds1 |- LT_EQ('c, 'a)

        'ac_unknown_before - assert(k_before.filter(_.isRight).isEmpty.value)

        'ab_1 - assert(!d_ab.isEmpty.value)
        'ab_correct - assert(d_ab.head.value.goal == LT_EQ('a, 'b))
        'bc_1 - assert(!d_bc.isEmpty.value)
        'bc_correct - assert(d_bc.head.value.goal == LT_EQ('b, 'c))
        'ac_1 - assert(!d_bc.isEmpty.value)
        'ac_correct - assert(d_ac.head.value.goal == LT_EQ('a, 'c))

        'ba - assert(d_ba.isEmpty.value)
        'cb - assert(d_cb.isEmpty.value)
        'ca - assert(d_ca.isEmpty.value)

        val k_after = (ds1 |-- LT_EQ('a, 'c)).head.value know LT_EQ('a, 'c)

        'ac_known_after - assert(!k_after.isEmpty.value)
      }
    }
  }

}
