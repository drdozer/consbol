package uk.co.turingatemyhamster.consbol

import scalaz._
import Scalaz._

trait DeriveTestSuiteBase {
  implicit class DSOps[R, V, I](_ds0: DerivationState[R, V, I]) {
    def |- [A](a: A)(implicit d: Derive[A, R, V, I]) =
      d(a, _ds0) filter { case (\/-(_), _) => true; case _ => false } map { case (\/-(p), _) => p }

    def |-- [A](a: A)(implicit d: Derive[A, R, V, I]) =
      d(a, _ds0) filter { case (\/-(_), _) => true; case _ => false } map { _._2 }
  }

  val dm = DeriveRules.apply[Symbol, Symbol, String]
  val ds0 = DerivationState(env = DeriveEnv(dm), m0 = Model.empty[Symbol, Symbol, String])

}
