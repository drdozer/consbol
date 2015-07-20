package uk.co.turingatemyhamster.consbol

import uk.co.turingatemyhamster.consbol.util.FuncName
import uk.co.turingatemyhamster.consbol.util.FuncNameUtils._

trait LengthDeriveEnv[R, V, I] {
  self : DeriveEnvBase[R, V, I] =>

  import rules._

  implicit lazy final val `Length r -| ?` = guard { derives_Length.reduce(_ || _) }
  def derives_Length: List[Derive[Length[R], R, V, I]]
}

trait LengthDeriveRules[R, V, I] {
  self : DeriveDSL[R, V, I] =>

  final lazy val `Length r -| k(Length r)` = known[Length, R]

}
