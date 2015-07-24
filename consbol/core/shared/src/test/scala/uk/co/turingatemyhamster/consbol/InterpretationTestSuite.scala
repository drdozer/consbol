package uk.co.turingatemyhamster.consbol

import utest._

/**
 * Created by nmrp3 on 24/07/15.
 */
object InterpretationTestSuite extends TestSuite {

  def tests = TestSuite {
    import Interpretation.InterpretationOps

    val m0 = InterpModel[Symbol, String]()

    'interpModel - {
      val (aI, m1) = m0 interpretation 'a

      assert(m1.v2i('a) == aI)

      val (bI, m2) = m1 interpretation 'b

      assert(m2.v2i('b) == bI)
    }

    'interpPair - {
      val (abI, m1) = m0 interpretation ('a, 'b)

      assert(m1.v2i('a) == abI._1)
      assert(m1.v2i('b) == abI._2)
    }
  }

}
