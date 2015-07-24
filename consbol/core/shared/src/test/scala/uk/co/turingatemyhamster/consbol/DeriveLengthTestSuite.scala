package uk.co.turingatemyhamster.consbol

import utest._

/**
 * Created by nmrp3 on 20/07/15.
 */
object DeriveLengthTestSuite extends TestSuite with DeriveTestSuiteBase {
  val tests = TestSuite {
    import Tell._
    import Know._
    import Derive._
    import ds0.env.length._

    'length {
      'implicits {
        implicitly[Derive[Length[Symbol], Symbol, Symbol, String]]
      }

      'from_tell - {
        val ds1 = ds0 tell Length('r, 100)
        val d = ds1 |- Length('r, 100)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == Length('r, 100))
      }
    }
  }
}
