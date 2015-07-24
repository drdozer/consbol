package uk.co.turingatemyhamster.consbol

/**
 * Created by nmrp3 on 24/07/15.
 */
object DeriveEnv {
  def apply[R, V, I](rules: DeriveRules[R, V, I]) = new DeriveEnv[R, V, I](
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
        Nil,

    derives_AT =
      rules.`a @ i -| k(a @ i)` ::
        rules.`a @ i -| ∃b: k(a suc b), b @ (i+1)` ::
        rules.`a @ i -| ∃b: k(b suc a), b @ (i-1)` ::
        Nil,
    derives_Suc =
      rules.`a suc b -| k(a suc b)` ::
        rules.`a suc b -| a @ i, b @ j | i+1=j` ::
        Nil,

    derives_RangeAs =
      rules.`RangeAs(r, a, b) -| k(RangeAs(r, a, b))` ::
        Nil,

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
        Nil,

    derives_Length =
      rules.`Length r -| k(Length r)` ::
      Nil
  )
}
