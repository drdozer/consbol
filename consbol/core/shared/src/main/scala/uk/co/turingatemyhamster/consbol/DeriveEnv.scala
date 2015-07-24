package uk.co.turingatemyhamster.consbol

import monocle._
import monocle.macros.{GenLens, Lenses}


@Lenses
case class DeriveEnv[R, V, I](ord: OrdDeriveEnv[R, V, I],
                              index: IndexDeriveEnv[R, V, I],
                              range: RangeDeriveEnv[R, V, I],
                              strand: StrandDeriveEnv[R, V, I],
                              length: LengthDeriveEnv[R, V, I])


object DeriveEnv {
  def apply[R, V, I](implicit rules: DeriveRules[R, V, I]) = new DeriveEnv[R, V, I](
    ord = OrdDeriveEnv(
      rules = rules,
      derives_LT =
        rules.`a < b -| k(a < b)` ::
          rules.`a < b -| a @ i, b @ j, i < j` ::
          rules.`a < b -| suc(a, b)` ::
          rules.`a < b -| RangeAs(r, a, b)` ::
          rules.`a < c -| a < b, b < c` ::
          rules.`a < c -| a < b, b <= c` ::
          rules.`a < c -| a <= b, b < c` ::
          Nil,
      derives_LT_EQ =
        rules.`a <= b -| k(a <= b)` ::
          rules.`a <= b -| a @ i, b @ j, i <= j` ::
          rules.`a <= b -| a < b` ::
          rules.`a <= b -| ∃c: b suc c. a < c` ::
          rules.`a <= c -| a <= b, b <= c` ::
          Nil,
      derives_EQ =
        rules.`a = b -| a @ i, b @ j, i = j` ::
          rules.`a = b -| a <=b, b <= a` ::
          rules.`a = b -| ∃c: a suc c, b suc c` ::
          rules.`a = b -| ∃c: c suc a, c suc b` ::
          Nil,
      derives_NOT_EQ =
        rules.`a != b -| k(a != b)` ::
          rules.`a != b -| a @ i, b @ j, i != j` ::
          rules.`a != b -| a < b` ::
          rules.`a != b -| b < a` ::
          Nil),
    index = IndexDeriveEnv(
      rules = rules,
      derives_AT =
        rules.`a @ i -| k(a @ i)` ::
          rules.`a @ i -| ∃b: k(a suc b), b @ (i+1)` ::
          rules.`a @ i -| ∃b: k(b suc a), b @ (i-1)` ::
          Nil,
      derives_Suc =
        rules.`a suc b -| k(a suc b)` ::
          rules.`a suc b -| a @ i, b @ j | i+1=j` ::
          Nil),
    range = RangeDeriveEnv(
      rules = rules,
      derives_RangeAs =
        rules.`RangeAs(r, a, b) -| k(RangeAs(r, a, b))` ::
          Nil),
    strand = StrandDeriveEnv(
      rules = rules,
      derives_SameStrandAs =
        rules.`r±s -| k(r±s) or k(s±r)` ::
          rules.`r±s -| +r, +s` ::
          rules.`r±s -| -r, -s` ::
          rules.`r±s -| ∃t: k(r±t). t±s` ::
          rules.`r±s -| ∃t: k(r∓t). t∓s` ::
          rules.`r±s -| ∃t: k(t±r). t±s` ::
          rules.`r±s -| ∃t: k(t∓r). t∓s` ::
          Nil,
      derives_DifferentStrandTo =
        rules.`r∓s -| k(r∓s) or k(s∓r)` ::
          rules.`r∓s -| +r, -s` ::
          rules.`r∓s -| -r, +s` ::
          rules.`r∓s -| ∃t: k(r∓t). t±s` ::
          rules.`r∓s -| ∃t: k(r±t). t∓s` ::
          rules.`r∓s -| ∃t: k(t∓r). t±s` ::
          rules.`r∓s -| ∃t: k(t±r). t∓s` ::
          Nil,
      derives_Strand =
        rules.`±r -| k(±r)` ::
          rules.`±r -| ∃s: ±s. r±s` ::
          rules.`±r -| ∃s: ∓s, r∓s` ::
          Nil),
    length = LengthDeriveEnv(
      rules = rules,
      derives_Length =
        rules.`Length r -| k(Length r)` ::
        Nil
    )
  )
}


trait DeriveRules[R, V, I]
  extends OrdDeriveRules[R, V, I]
  with IndexDeriveRules[R, V, I]
  with StrandDeriveRules[R, V, I]
  with RangeDeriveRules[R, V, I]
  with LengthDeriveRules[R, V, I]
  with DeriveDSL[R, V, I]

object DeriveRules {
  def apply[R, V, I](implicit _vi: InterpretationSingleton[V, I], _unify: UnifyI[I]): DeriveRules[R, V, I] =
    new DeriveRules[R, V, I]
    {
      override implicit final def vi: InterpretationSingleton[V, I] = _vi

      override implicit final def unify: UnifyI[I] = _unify
    }
}


trait DeriveEnvWithout[A, R, V, I] {
  def apply(env: DeriveEnv[R, V, I], dropList: List[Derive[A, R, V, I]]): DeriveEnv[R, V, I]
}

object DeriveEnvWithout {
  def withoutUsingLense[A, R, V, I](φ: Lens[DeriveEnv[R, V, I], List[Derive[A, R, V, I]]])
  : DeriveEnvWithout[A, R, V, I] = new DeriveEnvWithout[A, R, V, I] {
    override def apply(env: DeriveEnv[R, V, I], dropList: List[Derive[A, R, V, I]]): DeriveEnv[R, V, I] =
    φ.modify(_ diff dropList)(env)
  }

  implicit def withoutSameStrandAs[R, V, I] =
    withoutUsingLense[SameStrandAs[R], R, V, I](GenLens[DeriveEnv[R, V, I]](_.strand.derives_SameStrandAs))

  implicit def withoutDifferentStrandTo[R, V, I] =
    withoutUsingLense[DifferentStrandTo[R], R, V, I](GenLens[DeriveEnv[R, V, I]](_.strand.derives_DifferentStrandTo))

  implicit def withoutLT[R, V, I] =
    withoutUsingLense[LT[I], R, V, I](GenLens[DeriveEnv[R, V, I]](_.ord.derives_LT))

  implicit def withoutLT_EQ[R, V, I] =
    withoutUsingLense[LT_EQ[I], R, V, I](GenLens[DeriveEnv[R, V, I]](_.ord.derives_LT_EQ))
}
