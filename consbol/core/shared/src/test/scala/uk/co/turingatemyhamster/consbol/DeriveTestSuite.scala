package uk.co.turingatemyhamster.consbol


import utest._
import scalaz._
import scalaz.Scalaz._
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._


object DeriveTestSuite extends TestSuite {

  val tests = TestSuite {
    import Tell._
    import Know._
    import Derive._

    implicit class DSOps[R, V, I](_ds0: DerivationState[R, V, I]) {
      def |- [A](a: A)(implicit d: Derive[A, R, V, I]) =
        d(a, _ds0) filter { case (\/-(_), _) => true; case _ => false } map { case (\/-(p), _) => p }

      def |-- [A](a: A)(implicit d: Derive[A, R, V, I]) =
        d(a, _ds0) filter { case (\/-(_), _) => true; case _ => false } map { _._2 }
    }

    val dm = DeriveRules.apply[Symbol, Symbol, String]
    val ds0 = DerivationState(env = DeriveEnv(dm), m0 = Model.empty[Symbol, Symbol, String])

    import ds0.env._

    'derive_relative - {
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

    'derive_at - {
      'lt - {

        'implicits - {
          implicitly[Derive[AT[String], Symbol, Symbol, String]]
          implicitly[Derive[AT[Symbol], Symbol, Symbol, String]]
        }

        'derive_told {
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
