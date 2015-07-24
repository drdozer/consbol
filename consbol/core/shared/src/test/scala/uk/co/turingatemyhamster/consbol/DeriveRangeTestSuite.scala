package uk.co.turingatemyhamster.consbol

import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._
import utest._

/**
 * Created by nmrp3 on 24/07/15.
 */
object DeriveRangeTestSuite extends TestSuite with DeriveTestSuiteBase {

  val tests = TestSuite {
    import Tell._
    import Know._
    import Derive._
    import ds0.env._

    'derive_RangeAs - {
      'implicits - {
        implicitly[Derive[RangeAs[Symbol, String], Symbol, Symbol, String]]
        Derive.derive_usingInterpretation2[RangeAs, Symbol, Symbol, String]
        implicitly[Derive[RangeAs[Symbol, Symbol], Symbol, Symbol, String]]
      }

      'from_tell - {
        val ds1 = ds0 tell RangeAs('r, 'a, 'b)
        val d = ds1 |- RangeAs('r, 'a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == RangeAs('r, 'a, 'b))
      }

      'ord - {
        val ds1 = ds0 tell RangeAs('r, 'a, 'b)
        val d = ds1 |- LT('a, 'b)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT('a, 'b))
      }

      'ord2 - {
        val ds1 = ds0 tell RangeAs('r, 'a, 'b) tell RangeAs('s, 'c, 'd) tell LT('b, 'c)
        val d = ds1 |- LT('a, 'd)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT('a, 'd))
      }

      'ord3 - {
        val ds1 = ds0 tell
          RangeAs('r, 'a, 'b) tell
          RangeAs('s, 'c, 'd) tell
          RangeAs('t, 'e, 'f) tell
          LT('b, 'c) tell
        LT('d, 'e)
        val d = ds1 |- LT('a, 'f)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == LT('a, 'f))
      }
    }
  }
}
