/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Complex.QuadraticModulus

/-!
# The polynomial modulus lemma: examples

**Sharpness of the quadratic case.** `P = (X + i)²` has `|P(n)| = n² + 1 ∈ ℤ` for every `n`,
so the polynomial modulus lemma applies with `c = 1`, and `P P̄ = (X² + 1)²`; but the
coefficient of `X` in `P` is `2i`, so `P` is not real. It is the square `(X + b)²` with `b = i`,
the second case of the quadratic dichotomy.

**An identity of the line-bundle roots.** For `l s = 1 + d` with `l, d ≠ 0`,
`1/l² + (l - s)/(l d) = (l² - 1)/(d l²)`.
-/

namespace K3TwistsTest.QuadraticModulusExamples

open Polynomial Complex

/-- `|(n + i)²| = n² + 1`. -/
example (n : ℕ) : ‖((X + C I) ^ 2 : ℂ[X]).eval (n : ℂ)‖ = (n : ℝ) ^ 2 + 1 := by
  rw [eval_pow, norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- So the moduli of `(X + i)²` at the integers lie in `ℤ`. -/
example : ∀ᶠ n : ℕ in Filter.atTop,
    ‖((X + C I) ^ 2 : ℂ[X]).eval (n : ℂ)‖ ∈ AddSubgroup.zmultiples (1 : ℝ) := by
  refine Filter.Eventually.of_forall fun n => ⟨(n : ℤ) ^ 2 + 1, ?_⟩
  rw [eval_pow, norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- `(X + i)²` is not real: its coefficient of `X` is `2i`. -/
example : ((X + C I) ^ 2 : ℂ[X]).coeff 1 = 2 * I := by
  rw [sq, add_mul, mul_add, mul_add]
  simp [coeff_X, coeff_C, coeff_mul_C]
  ring

/-- The identity `1/l² + (l - s)/(l d) = (l² - 1)/(d l²)` under `l s = 1 + d`. -/
example (l s d : ℝ) (hl : l ≠ 0) (hd : d ≠ 0) (h : l * s = 1 + d) :
    1 / l ^ 2 + (l - s) / (l * d) = (l ^ 2 - 1) / (d * l ^ 2) := by
  field_simp
  linear_combination -h

end K3TwistsTest.QuadraticModulusExamples
