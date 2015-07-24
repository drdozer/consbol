package uk.co.turingatemyhamster.consbol


import utest._
import scalaz._
import scalaz.Scalaz._
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._



object DeriveStrandTestSuite extends TestSuite with DeriveTestSuiteBase {

  val tests = TestSuite {
    import Tell._
    import Know._
    import Derive._
    import ds0.env.strand._


    'derive_strand - {
      'implicits {
        implicitly[Derive[Strand[Symbol], Symbol, Symbol, String]]
      }

      val ds1 = ds0 tell Strand('r, Orientation.+) tell Strand('s, Orientation.-) tell Strand('t, Orientation.+)

      val dr = ds1 |- Strand('r, Orientation.+)
      val ds = ds1 |- Strand('s, Orientation.-)
      val dt = ds1 |- Strand('t, Orientation.+)

      'got_goal_r - assert(!dr.isEmpty.value)
      'got_corret_goal_r - assert(dr.head.value.goal == Strand('r, Orientation.+))

      'got_goal_s - assert(!ds.isEmpty.value)
      'got_corret_goal_s - assert(ds.head.value.goal == Strand('s, Orientation.-))

      'got_goal_t - assert(!dt.isEmpty.value)
      'got_corret_goal_t - assert(dt.head.value.goal == Strand('t, Orientation.+))

    }

    'derive_same_strand_as - {
      'implicits {
        implicitly[Derive[SameStrandAs[Symbol], Symbol, Symbol, String]]
      }

      'from_tell - {
        val ds1 = ds0 tell SameStrandAs('r, 's)
        val d = ds1 |- SameStrandAs('r, 's)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == SameStrandAs('r, 's))

      }

      'from_strand - {
        val ds1 = ds0 tell Strand('r, Orientation.-) tell Strand('s, Orientation.-)
        val d = ds1 |- SameStrandAs('r, 's)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == SameStrandAs('r, 's))

      }

      'same_strand_implies_strand_lr - {
        val ds1 = ds0 tell Strand('s, Orientation.+) tell SameStrandAs('r, 's)
        val d = ds1 |- Strand('r, Orientation.+)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == Strand('r, Orientation.+))
      }

      'same_strand_implies_strand_rl - {
        val ds1 = ds0 tell Strand('s, Orientation.+) tell SameStrandAs('s, 'r)
        val d = ds1 |- Strand('r, Orientation.+)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == Strand('r, Orientation.+))
      }
    }

    'derive_different_strand_to - {
      'implicits {
        implicitly[Derive[DifferentStrandTo[Symbol], Symbol, Symbol, String]]
      }

      'from_tell - {
        val ds1 = ds0 tell DifferentStrandTo('r, 's)
        val d = ds1 |- DifferentStrandTo('r, 's)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == DifferentStrandTo('r, 's))
      }

      'from_strand - {
        val ds1 = ds0 tell Strand('r, Orientation.+) tell Strand('s, Orientation.-)
        val d = ds1 |- DifferentStrandTo('r, 's)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == DifferentStrandTo('r, 's))
      }

      'different_strand_implies_strand_lr - {
        val ds1 = ds0 tell Strand('s, Orientation.+) tell DifferentStrandTo('r, 's)
        val d = ds1 |- Strand('r, Orientation.-)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == Strand('r, Orientation.-))
      }

      'different_strand_implies_strand_rl - {
        val ds1 = ds0 tell Strand('s, Orientation.+) tell DifferentStrandTo('s, 'r)
        val d = ds1 |- Strand('r, Orientation.-)

        'got_goal - assert(!d.isEmpty.value)
        'goal_is_correct - assert(d.head.value.goal == Strand('r, Orientation.-))
      }
    }

    'derive_strand_chained - {
      val ds1 = ds0 tell
        Strand('z, Orientation.+) tell
        DifferentStrandTo('y, 'z) tell
        SameStrandAs('y, 'x) tell
        SameStrandAs('w, 'x)

      val yzO = ds1 |- Strand('y, Orientation.-)
      val xzD = ds1 |- DifferentStrandTo('x, 'z)
      val xzO = ds1 |- Strand('x, Orientation.-)
      val wzD = ds1 |- DifferentStrandTo('w, 'z)
      val wzO = ds1 |- Strand('w, Orientation.-)

      assert(!yzO.isEmpty.value)
      assert(!xzD.isEmpty.value)
      assert(!xzO.isEmpty.value)
      assert(!wzD.isEmpty.value)
      assert(!wzO.isEmpty.value)
    }
  }
}
