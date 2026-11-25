/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The Crofton constant and the Crofton barycentre

The length of a vector is the average of the lengths of its projections:
`∫₀^{2π} |cos(θ - α)| dθ = 4` (`Complex.integral_abs_cos_sub`), so for finitely many
`z_j ∈ ℂ`

  `Σ_j |z_j| = (1/4) ∫₀^{2π} Σ_j |Re(e^{-iθ} z_j)| dθ`

(`Complex.sum_norm_eq_integral`), the Cauchy–Crofton formula for the perimeter of a polygon with
edges `z_j`. For a stability condition with HN factors of charges `z_j` the left side is the
mass and the integrand the directional profile `ν_θ`, so the mass is the barycentre of the
directional profiles.

The **directional ratio** `θ ↦ Σ_j |Re(e^{-iθ} z_j)| / Σ_j |z_j|` (`Complex.directionalRatio`)
takes values in `[0, 1]` (`Complex.directionalRatio_mem_Icc`), has period `π`, is `1`-Lipschitz
(`Complex.lipschitzWith_directionalRatio`), also in the distance of the circle `ℝ / 2πℤ`
(`Complex.abs_directionalRatio_sub_le_norm`), and has average `2/π`
(`Complex.average_directionalRatio`).
-/

open Real intervalIntegral MeasureTheory Finset

namespace Complex

/-- `|cos|` has period `π`. -/
lemma periodic_abs_cos : Function.Periodic (fun θ ↦ |Real.cos θ|) π := fun θ ↦ by
  simp [Real.cos_add_pi, abs_neg]

lemma integral_abs_cos_period (t : ℝ) : ∫ θ in t..t + π, |Real.cos θ| = 2 := by
  rw [periodic_abs_cos.intervalIntegral_add_eq t (-(π / 2)),
    show -(π / 2) + π = π / 2 by ring]
  have hcos : ∀ θ ∈ Set.uIcc (-(π / 2)) (π / 2), |Real.cos θ| = Real.cos θ := fun θ hθ ↦ by
    rw [Set.uIcc_of_le (by linarith [pi_pos])] at hθ
    exact abs_of_nonneg (cos_nonneg_of_mem_Icc hθ)
  rw [integral_congr hcos, integral_cos]
  simp
  ring

/-- **The Crofton constant**: `∫₀^{2π} |cos(θ - α)| dθ = 4`. -/
theorem integral_abs_cos_sub (α : ℝ) : ∫ θ in (0)..(2 * π), |Real.cos (θ - α)| = 4 := by
  rw [intervalIntegral.integral_comp_sub_right (fun θ ↦ |Real.cos θ|) α]
  have hc : Continuous fun θ ↦ |Real.cos θ| := continuous_abs.comp Real.continuous_cos
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0 - α + π)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), integral_abs_cos_period,
    show 2 * π - α = 0 - α + π + π by ring, integral_abs_cos_period]
  norm_num

/-- `|Re(e^{-iθ} z)| = |z| |cos(θ - arg z)|`. -/
lemma abs_re_exp_neg_mul (z : ℂ) (θ : ℝ) :
    |(exp (-(θ * I)) * z).re| = ‖z‖ * |Real.cos (θ - arg z)| := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [show exp (-(θ * I)) * (‖z‖ * exp (arg z * I)) = ‖z‖ * exp ((arg z - θ : ℝ) * I) by
    rw [mul_left_comm, ← exp_add]; push_cast; ring_nf]
  rw [re_ofReal_mul, exp_ofReal_mul_I_re, abs_mul, abs_norm, ← Real.cos_neg, neg_sub]

lemma continuous_abs_re_exp_neg_mul (z : ℂ) :
    Continuous fun θ : ℝ ↦ |(exp (-(θ * I)) * z).re| := by
  simp_rw [abs_re_exp_neg_mul]
  fun_prop

lemma abs_re_exp_neg_mul_le (z : ℂ) (θ : ℝ) : |(exp (-(θ * I)) * z).re| ≤ ‖z‖ := by
  rw [abs_re_exp_neg_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (abs_cos_le_one _)

/-- **The Crofton barycentre**: for finitely many `z_j ∈ ℂ`,
`Σ_j |z_j| = (1/4) ∫₀^{2π} Σ_j |Re(e^{-iθ} z_j)| dθ`. -/
theorem sum_norm_eq_integral {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ∑ j ∈ s, ‖z j‖ =
      (1 / 4) * ∫ θ in (0)..(2 * π), ∑ j ∈ s, |(exp (-(θ * I)) * z j).re| := by
  rw [intervalIntegral.integral_finsetSum fun j _ ↦
    (continuous_abs_re_exp_neg_mul (z j)).intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp_rw [abs_re_exp_neg_mul, intervalIntegral.integral_const_mul, integral_abs_cos_sub]
  ring

/-- The **directional ratio** `θ ↦ Σ_j |Re(e^{-iθ} z_j)| / Σ_j |z_j|` of finitely many complex
numbers. -/
noncomputable def directionalRatio {ι : Type*} (s : Finset ι) (z : ι → ℂ) (θ : ℝ) : ℝ :=
  (∑ j ∈ s, |(exp (-(θ * I)) * z j).re|) / ∑ j ∈ s, ‖z j‖

variable {ι : Type*} (s : Finset ι) (z : ι → ℂ)

/-- The directional ratio takes values in `[0, 1]`. -/
theorem directionalRatio_mem_Icc (θ : ℝ) : directionalRatio s z θ ∈ Set.Icc 0 1 := by
  refine ⟨div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (sum_nonneg fun _ _ ↦ norm_nonneg _),
    div_le_one_of_le₀ (sum_le_sum fun j _ ↦ abs_re_exp_neg_mul_le (z j) θ)
      (sum_nonneg fun _ _ ↦ norm_nonneg _)⟩

/-- The directional ratio has period `π`. -/
theorem directionalRatio_periodic : Function.Periodic (directionalRatio s z) π := fun θ ↦ by
  simp only [directionalRatio, abs_re_exp_neg_mul, show ∀ a, θ + π - a = (θ - a) + π by
    intro a; ring, Real.cos_add_pi, abs_neg]

/-- The directional ratio is `1`-Lipschitz. -/
theorem lipschitzWith_directionalRatio : LipschitzWith 1 (directionalRatio s z) := by
  refine LipschitzWith.of_dist_le_mul fun θ θ' ↦ ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, directionalRatio, directionalRatio,
    ← sub_div]
  set D := ∑ j ∈ s, ‖z j‖
  rcases (show 0 ≤ D from sum_nonneg fun j _ ↦ norm_nonneg (z j)).eq_or_lt with hD | hD
  · rw [← hD, div_zero, abs_zero]
    exact abs_nonneg _
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine sum_le_sum fun j _ ↦ ?_
  rw [abs_re_exp_neg_mul, abs_re_exp_neg_mul, ← mul_sub, abs_mul, abs_norm, mul_comm |θ - θ'|]
  refine mul_le_mul_of_nonneg_left ((abs_abs_sub_abs_le_abs_sub _ _).trans ?_) (norm_nonneg _)
  refine (abs_cos_sub_cos_le _ _).trans (le_of_eq ?_)
  ring_nf

/-- **`1`-Lipschitz in angular distance**: the directional ratio moves by at most the distance
of `θ` and `θ'` on the circle `ℝ / 2πℤ`. -/
theorem abs_directionalRatio_sub_le_norm (θ θ' : ℝ) :
    |directionalRatio s z θ - directionalRatio s z θ'| ≤
      ‖((θ - θ' : ℝ) : AddCircle (2 * π))‖ := by
  rw [AddCircle.norm_eq]
  set m := round ((2 * π)⁻¹ * (θ - θ'))
  have hper : directionalRatio s z θ' = directionalRatio s z (θ' + (2 * m : ℤ) * π) := by
    rw [(directionalRatio_periodic s z).int_mul (2 * m) θ']
  rw [hper]
  have := (lipschitzWith_directionalRatio s z).dist_le_mul θ (θ' + (2 * m : ℤ) * π)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

/-- The directional ratio has average `2/π` over a period, when some `z_j ≠ 0`. -/
theorem average_directionalRatio (h : ∑ j ∈ s, ‖z j‖ ≠ 0) :
    (1 / (2 * π)) * ∫ θ in (0)..(2 * π), directionalRatio s z θ = 2 / π := by
  have h4 := sum_norm_eq_integral s z
  simp only [directionalRatio]
  rw [intervalIntegral.integral_div]
  have : ∫ θ in (0)..(2 * π), ∑ j ∈ s, |(exp (-(θ * I)) * z j).re| =
      4 * ∑ j ∈ s, ‖z j‖ := by linarith
  rw [this]
  field_simp
  ring

end Complex
