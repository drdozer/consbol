package uk.co.turingatemyhamster.consbol


import utest._
import scalaz._
import scalaz.Scalaz._
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._

object DeriveIndexTestSuite extends TestSuite with DeriveTestSuite {
  val tests = TestSuite {
    import Tell._
    import Know._
    import Derive._
    import ds0.env._

    'lt - {

      'implicits - {
        implicitly[Derive[AT[String], Symbol, Symbol, String]]
        implicitly[Derive[AT[Symbol], Symbol, Symbol, String]]
      }

      'derive_told - {
        val ds1 = ds0 tell AT('a, 10) tell AT('b, 20)

        val d_a = ds1 |- AT('a, 10)
        val d_b = ds1 |- AT('b, 20)

        'got_goal_a - assert(!d_a.isEmpty.value)
        'goal_is_correct_a - assert(d_a.head.value.goal == AT('a, 10))
        'one_goal_b - assert(d_a.tail.isEmpty.value)

        'got_goal_b - assert(!d_b.isEmpty.value)
        'goal_is_correct_b - assert(d_b.head.value.goal == AT('b, 20))
        'one_goal_b - assert(d_b.tail.isEmpty.value)
      }

      'derive_lt - {

        val ds1 = ds0 tell AT('a, 10) tell AT('b, 20)

        val d = ds1 |- LT('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT('a, 'b))
      }
    }

    'derive_suc - {

      'implicits - {
        implicitly[Derive[Suc[String], Symbol, Symbol, String]]
        implicitly[Derive[Suc[Symbol], Symbol, Symbol, String]]
      }

      'derive_told - {
        val ds1 = ds0 tell Suc('a, 'b)

        val d = ds1 |- Suc('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == Suc('a, 'b))
      }

      'derive_lt - {
        val ds1 = ds0 tell Suc('a, 'b)

        val d = ds1 |- LT('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT('a, 'b))
      }

      'derive_bAt - {
        val ds1 = ds0 tell Suc('a, 'b) tell AT('a, 10)

        val d = ds1 |- AT('b, 11)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == AT('b, 11))
      }

      'derive_aAt - {
        val ds1 = ds0 tell Suc('a, 'b) tell AT('b, 11)

        val d = ds1 |- AT('a, 10)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == AT('a, 10))
      }

      'deriveLtEq - {
        val ds1 = ds0 tell LT('a, 'c) tell Suc('b, 'c)

        val d = ds1 |- LT_EQ('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT_EQ('a, 'b))
      }

      'deriveNotEq - {
        val ds1 = ds0 tell Suc('a, 'b)

        val d = ds1 |- NOT_EQ('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == NOT_EQ('a, 'b))
      }
    }

    'lt_eq - {

      'when_lt - {

        val ds1 = ds0 tell AT('a, 10) tell AT('b, 20)

        val d = ds1 |- LT_EQ('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT_EQ('a, 'b))

        val dd = ds1 |-- LT_EQ('a, 'b)
        val k =  dd.head.value know LT_EQ('a, 'b)

        'known_after - assert(!k.isEmpty.value)
      }

      'when_eq - {

        val ds1 = ds0 tell AT('a, 10) tell AT('b, 10)

        val d = ds1 |- LT_EQ('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT_EQ('a, 'b))

        val dd = ds1 |-- LT_EQ('a, 'b)
        val k = dd.head.value know LT_EQ('a, 'b)

        'known_after - assert(!k.isEmpty.value)
      }

    }

    'eq - {

      val ds1 = ds0 tell AT('a, 10) tell AT('b, 10)

      val d = ds1 |- EQ('a, 'b)

      'got_goal - assert(!d.isEmpty.value)
      'goal_is_correct - assert(d.head.value.goal == EQ('a, 'b))

      val dd = ds1 |-- EQ('a, 'b)
      val k = dd.head.value know EQ('a, 'b)

      'known_after - assert(!k.isEmpty.value)

    }

    'not_eq - {
      val ds1 = ds0 tell AT('a, 10) tell AT('b, 20)

      val d = ds1 |- NOT_EQ('a, 'b)

      'got_goal - assert(!d.isEmpty.value)
      'goal_is_correct - assert(d.head.value.goal == NOT_EQ('a, 'b))

      val dd = ds1 |-- NOT_EQ('a, 'b)
      val k = dd.head.value know NOT_EQ('a, 'b)

      'known_after - assert(!k.isEmpty.value)
    }
  }
}
