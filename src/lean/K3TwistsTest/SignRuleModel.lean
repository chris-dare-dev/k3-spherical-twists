/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Matrix.SignRule
import K3Twists.Order.Squeeze

/-!
# The sign rule needs the parity-graded form

Regression tests for `Matrix.signRule_letter`.

* With the symmetric Euler form of a 2-Calabi–Yau category on the diagonal (`K_ii = 2`) and a
  coupling with zero diagonal (`G_ii = 0`), no sign diagonal conjugates a letter of nonzero
  exponent into a count letter (`signRule_fails_of_diag_two`): the diagonal entry of `D E D` is
  `1 - 2e`, that of `P` is `1`. The failure needs `G_ii = 0`: with `G_ii = 2` and `e < 0` the
  diagonal condition holds.
* With `K` and `G` symmetric, adjacent letters that satisfy the sign rule have exponents of the
  same sign (`signRule_same_of_symm`), the opposite of `Matrix.signRule_opposite` for the skew,
  parity-graded form.
* The intertwining of the squeeze, stated for all `x`, forces additivity in the matrix setting
  (`hE_forces_additive`).

Built by `lake test`.
-/

namespace K3TwistsTest.SignRuleModel

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The symmetric 2-Calabi–Yau diagonal defeats every sign diagonal. -/
theorem signRule_fails_of_diag_two {d : ι → ℝ} (hd : IsSign d) (G K : Matrix ι ι ℝ) (i : ι)
    {e : ℤ} (he : e ≠ 0) (hK : K i i = 2) (hG : G i i = 0) :
    diagonal d * signedLetter K i e * diagonal d ≠ countLetter G i e := by
  intro h
  have c := (signRule_letter hd G K i e).1 h i
  rw [hK, hG, hd.mul_self i] at c
  have : (e : ℝ) = 0 := by linarith
  exact he (by exact_mod_cast this)

/-- With `G_ii = 2` and `e < 0` the diagonal condition `-2e = 2|e|` holds. -/
example (e : ℤ) (he : e < 0) : -((e : ℝ) * 1 * 2) = |(e : ℝ)| * 2 := by
  have : (e : ℝ) < 0 := by exact_mod_cast he
  rw [abs_of_neg this]; ring

/-- A symmetric form forces adjacent letters to have exponents of the same sign. -/
theorem signRule_same_of_symm {d : ι → ℝ} (hd : IsSign d) {G K : Matrix ι ι ℝ}
    (hK : ∀ a b, K b a = K a b) (hG : ∀ a b, G b a = G a b) {i j : ι} {e e' : ℤ}
    (he : e ≠ 0) (he' : e' ≠ 0) (hij : G i j ≠ 0)
    (h1 : diagonal d * signedLetter K i e * diagonal d = countLetter G i e)
    (h2 : diagonal d * signedLetter K j e' * diagonal d = countLetter G j e') :
    0 < e * e' := by
  have c1 := (signRule_letter hd G K i e).1 h1 j
  have c2 := (signRule_letter hd G K j e').1 h2 i
  rw [hK, hG] at c2
  have key : ((e' : ℝ) * |(e : ℝ)| - (e : ℝ) * |(e' : ℝ)|) * G i j = 0 := by
    linear_combination (-(e' : ℝ)) * c1 + (e : ℝ) * c2
  have k2 : (e' : ℝ) * |(e : ℝ)| - (e : ℝ) * |(e' : ℝ)| = 0 :=
    (mul_eq_zero.1 key).resolve_right hij
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have he0' : (e' : ℝ) ≠ 0 := by exact_mod_cast he'
  have : (0 : ℝ) < e * e' := by
    rcases lt_or_gt_of_ne he0 with h | h <;> rcases lt_or_gt_of_ne he0' with h' | h'
    · nlinarith
    · rw [abs_of_neg h, abs_of_pos h'] at k2; nlinarith
    · rw [abs_of_pos h, abs_of_neg h'] at k2; nlinarith
    · nlinarith
  exact_mod_cast this

omit [DecidableEq ι] in
/-- The all-`x` intertwining `E(d x) = d P(x)` with a linear `E` and signs `d` forces `P` to be
additive. -/
theorem hE_forces_additive {d : ι → ℝ} (hd : IsSign d) (Em : Matrix ι ι ℝ)
    (P : (ι → ℝ) → (ι → ℝ)) (hE : ∀ x, Em *ᵥ (d * x) = d * P x) (x y : ι → ℝ) :
    P (x + y) = P x + P y := by
  apply hd.mul_injective
  have h1 := hE (x + y)
  have h2 := hE x
  have h3 := hE y
  rw [mul_add, Matrix.mulVec_add] at h1
  show d * P (x + y) = d * (P x + P y)
  rw [mul_add, ← h1, ← h2, ← h3]

end K3TwistsTest.SignRuleModel
