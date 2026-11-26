/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.GelfandRadius

/-!
# The rate of a hyperbolic matrix of determinant one

For `t ≥ 2` put `sl2Rate t = (t + √(t² - 4))/2`, the larger root of `x² - t x + 1`, so that
`sl2Rate t + (sl2Rate t)⁻¹ = t`. The `SL₂` rate lemma `Matrix.gelfandRadius_eq_of_det_eq_one`
takes such a root as an input. With the root supplied, a real `2 × 2` matrix of determinant one
and trace `t > 2` has Gelfand radius `sl2Rate t > 1`, and its Gelfand radius is a root of its
characteristic polynomial `x² - t x + 1`; no eigenvector is used.

## Main results

* `Matrix.sl2Rate_sq_sub_mul_add_one`, `Matrix.sl2Rate_add_inv`, `Matrix.one_lt_sl2Rate`: the
  root, its inverse `(t - √(t² - 4))/2`, and `sl2Rate t > 1` for `t > 2`;
  `Matrix.sl2Rate_eq_of_add_inv`: it is the only root `l ≥ 1`.
* `Matrix.gelfandRadius_eq_sl2Rate`, `Matrix.one_lt_gelfandRadius_of_det_eq_one`,
  `Matrix.gelfandRadius_sq_sub_trace_mul_add_one`: the `SL₂` rate lemma with the root supplied.
* `Matrix.sl2Rate_sq_sub_two`: at trace `k² - 2` the rate is
  `(k² - 2 + √(k⁴ - 4k²))/2`, the form in which Barbacovi and Kim (arXiv:2107.06079,
  Theorem 4.0.1) give the categorical entropy of two spherical twists whose centres have total
  `Ext` dimension `k`.
-/

namespace Matrix

open scoped Matrix.Norms.Operator

/-- The larger root `(t + √(t² - 4))/2` of `x² - t x + 1`. For `t > 2` it is the Gelfand radius of
every real `2 × 2` matrix of determinant one and trace `t` (`Matrix.gelfandRadius_eq_sl2Rate`). -/
noncomputable def sl2Rate (t : ℝ) : ℝ := (t + √(t ^ 2 - 4)) / 2

lemma sq_sqrt_sq_sub_four {t : ℝ} (ht : 2 ≤ t) : √(t ^ 2 - 4) ^ 2 = t ^ 2 - 4 :=
  Real.sq_sqrt (by nlinarith)

/-- `sl2Rate t` is a root of `x² - t x + 1`. -/
theorem sl2Rate_sq_sub_mul_add_one {t : ℝ} (ht : 2 ≤ t) :
    sl2Rate t ^ 2 - t * sl2Rate t + 1 = 0 := by
  have h := sq_sqrt_sq_sub_four ht
  unfold sl2Rate
  linear_combination h / 4

theorem one_le_sl2Rate {t : ℝ} (ht : 2 ≤ t) : 1 ≤ sl2Rate t := by
  have := Real.sqrt_nonneg (t ^ 2 - 4)
  unfold sl2Rate
  linarith

theorem sl2Rate_pos {t : ℝ} (ht : 2 ≤ t) : 0 < sl2Rate t :=
  one_pos.trans_le (one_le_sl2Rate ht)

theorem one_lt_sl2Rate {t : ℝ} (ht : 2 < t) : 1 < sl2Rate t := by
  have := Real.sqrt_nonneg (t ^ 2 - 4)
  unfold sl2Rate
  linarith

/-- The other root: `(sl2Rate t)⁻¹ = (t - √(t² - 4))/2`. -/
theorem sl2Rate_inv {t : ℝ} (ht : 2 ≤ t) : (sl2Rate t)⁻¹ = (t - √(t ^ 2 - 4)) / 2 := by
  have h := sq_sqrt_sq_sub_four ht
  apply inv_eq_of_mul_eq_one_right
  unfold sl2Rate
  linear_combination (-1 / 4 : ℝ) * h

theorem sl2Rate_add_inv {t : ℝ} (ht : 2 ≤ t) : sl2Rate t + (sl2Rate t)⁻¹ = t := by
  rw [sl2Rate_inv ht]
  unfold sl2Rate
  ring

/-- **Uniqueness.** If `l ≥ 1` and `l + l⁻¹ = t`, then `l = sl2Rate t`. -/
theorem sl2Rate_eq_of_add_inv {l t : ℝ} (hl : 1 ≤ l) (h : l + l⁻¹ = t) : sl2Rate t = l := by
  have hl0 : l ≠ 0 := (one_pos.trans_le hl).ne'
  have hinv : l⁻¹ ≤ l := (inv_le_one_of_one_le₀ hl).trans hl
  have hsq : t ^ 2 - 4 = (l - l⁻¹) ^ 2 := by
    rw [← h]
    have : l * l⁻¹ = 1 := mul_inv_cancel₀ hl0
    linear_combination 4 * this
  rw [sl2Rate, hsq, Real.sqrt_sq (by linarith), ← h]
  ring

/-- At trace `k² - 2` the rate is `(k² - 2 + √(k⁴ - 4k²))/2`. -/
theorem sl2Rate_sq_sub_two (k : ℝ) :
    sl2Rate (k ^ 2 - 2) = (k ^ 2 - 2 + √(k ^ 4 - 4 * k ^ 2)) / 2 := by
  rw [sl2Rate, show (k ^ 2 - 2) ^ 2 - 4 = k ^ 4 - 4 * k ^ 2 by ring]

/-! ### The `SL₂` rate lemma with the root supplied -/

/-- **Hyperbolic `SL₂(ℝ)`, explicit rate.** A real `2 × 2` matrix of determinant one and trace
`t > 2` has Gelfand radius `sl2Rate t = (t + √(t² - 4))/2`. -/
theorem gelfandRadius_eq_sl2Rate (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1)
    (htr : 2 < M.trace) : gelfandRadius M = sl2Rate M.trace :=
  gelfandRadius_eq_of_det_eq_one M hdet (one_lt_sl2Rate htr) (sl2Rate_add_inv htr.le).symm

/-- A real `2 × 2` matrix of determinant one and trace `> 2` grows exponentially. -/
theorem one_lt_gelfandRadius_of_det_eq_one (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1)
    (htr : 2 < M.trace) : 1 < gelfandRadius M := by
  rw [gelfandRadius_eq_sl2Rate M hdet htr]
  exact one_lt_sl2Rate htr

/-- **The Gelfand radius is a root of the characteristic polynomial** `x² - (tr M) x + 1`, for a
real `2 × 2` matrix of determinant one and trace `> 2`. -/
theorem gelfandRadius_sq_sub_trace_mul_add_one (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1)
    (htr : 2 < M.trace) : gelfandRadius M ^ 2 - M.trace * gelfandRadius M + 1 = 0 := by
  rw [gelfandRadius_eq_sl2Rate M hdet htr]
  exact sl2Rate_sq_sub_mul_add_one htr.le

end Matrix
