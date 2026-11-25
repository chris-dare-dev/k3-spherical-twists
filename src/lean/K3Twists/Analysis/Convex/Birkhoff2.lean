/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Matrix.Mul
import K3Twists.Analysis.Convex.HilbertMetric

/-!
# Birkhoff's contraction for positive `2 × 2` matrices

A real matrix `M = [[a, b], [c, d]]` with positive entries maps the open positive cone of `ℝ²` into
itself, and acts on ratios `x = x₀ / x₁` by the Möbius map `x ↦ (ax + b) / (cx + d)`
(`Matrix.ratioMap`). Birkhoff's theorem (Trans. Amer. Math. Soc. 85 (1957); Hopf, J. Math. Mech.
12 (1963)) says that `M` contracts Hilbert's projective metric by `tanh (Δ / 4)`, `Δ` the Hilbert
diameter of the image of the cone. In dimension two the image is spanned by the columns,
`Δ = |log (ad / bc)|`, and the coefficient is `|√(ad) - √(bc)| / (√(ad) + √(bc))`
(`Matrix.birkhoffCoeff`).

This strict contraction is a linear theorem: there is no condition on the determinant, and a
monotone positively homogeneous map is in general only nonexpansive. Positivity of the entries is
needed: `[[0, 1], [1, 1]]` and `[[1, 1], [1, 0]]` are primitive, but their product
`[[1, 0], [2, 1]]` is reducible, so an alphabet of primitive matrices need not contract
(`K3TwistsTest/BirkhoffModel.lean`).

## Main results

* `Matrix.abs_log_ratioMap_sub_le`: `|log R(x) - log R(y)| ≤ κ |log x - log y|` for `x, y > 0`,
  `R` the ratio map and `κ` the Birkhoff coefficient, by the mean value theorem in logarithmic
  coordinates and `act² + bd ≥ 2 √(ac) √(bd) t` (`Matrix.abs_det_mul_le`);
* `Matrix.birkhoffCoeff_eq_tanh`: `κ = tanh (|log (ad / bc)| / 4)`;
  `Matrix.birkhoffCoeff_lt_one`: `κ < 1`;
* `hilbertEDist_univ_fin_two`: on the positive cone of `ℝ²` the Hilbert pseudometric of
  `Analysis/Convex/HilbertMetric.lean` is `|log (x₀/x₁) - log (y₀/y₁)|`;
* `Matrix.hilbertEDist_mulVec_le`: `d_H(Mx, My) ≤ κ d_H(x, y)`.
-/

open Real Set

namespace Matrix

variable (M : Matrix (Fin 2) (Fin 2) ℝ)

/-- The action of `M = [[a, b], [c, d]]` on ratios `x = x₀ / x₁`: `x ↦ (a x + b) / (c x + d)`. -/
noncomputable def ratioMap (x : ℝ) : ℝ := (M 0 0 * x + M 0 1) / (M 1 0 * x + M 1 1)

/-- The **Birkhoff coefficient** of `M = [[a, b], [c, d]]`, `|√(ad) - √(bc)| / (√(ad) + √(bc))`;
for positive `M` it is `tanh (Δ / 4)` with `Δ = |log (ad / bc)|` (`birkhoffCoeff_eq_tanh`). -/
noncomputable def birkhoffCoeff : ℝ :=
  |√(M 0 0 * M 1 1) - √(M 0 1 * M 1 0)| / (√(M 0 0 * M 1 1) + √(M 0 1 * M 1 0))

variable {M}

lemma birkhoffCoeff_nonneg : 0 ≤ M.birkhoffCoeff := by
  unfold birkhoffCoeff
  positivity

lemma birkhoffCoeff_lt_one (hM : ∀ i j, 0 < M i j) : M.birkhoffCoeff < 1 := by
  have hp : 0 < √(M 0 0 * M 1 1) := Real.sqrt_pos.2 (mul_pos (hM 0 0) (hM 1 1))
  have hq : 0 < √(M 0 1 * M 1 0) := Real.sqrt_pos.2 (mul_pos (hM 0 1) (hM 1 0))
  rw [birkhoffCoeff, div_lt_one (by positivity)]
  rcases le_total (√(M 0 1 * M 1 0)) (√(M 0 0 * M 1 1)) with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]; linarith
  · rw [abs_of_nonpos (sub_nonpos.2 h)]; linarith

/-- `tanh y = (e^{2y} - 1) / (e^{2y} + 1)`. -/
lemma _root_.Real.tanh_eq_exp_two_mul (y : ℝ) : tanh y = (exp (2 * y) - 1) / (exp (2 * y) + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h1 : exp (2 * y) = exp y * exp y := by rw [← Real.exp_add]; ring_nf
  have h2 : exp (-y) = (exp y)⁻¹ := Real.exp_neg y
  rw [h1, h2]
  have := Real.exp_pos y
  field_simp

/-- For positive `M`, the Birkhoff coefficient is `tanh (Δ / 4)`, `Δ = |log (ad / bc)|` the
Hilbert distance between the columns of `M`. -/
theorem birkhoffCoeff_eq_tanh (hM : ∀ i j, 0 < M i j) :
    M.birkhoffCoeff = tanh (|log (M 0 0 * M 1 1 / (M 0 1 * M 1 0))| / 4) := by
  have hpq : M 0 0 * M 1 1 / (M 0 1 * M 1 0) = (√(M 0 0 * M 1 1) / √(M 0 1 * M 1 0)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (mul_pos (hM 0 0) (hM 1 1)).le,
      Real.sq_sqrt (mul_pos (hM 0 1) (hM 1 0)).le]
  rw [hpq, birkhoffCoeff]
  set p := √(M 0 0 * M 1 1)
  set q := √(M 0 1 * M 1 0)
  have hp : 0 < p := Real.sqrt_pos.2 (mul_pos (hM 0 0) (hM 1 1))
  have hq : 0 < q := Real.sqrt_pos.2 (mul_pos (hM 0 1) (hM 1 0))
  rw [Real.log_pow, Real.tanh_eq_exp_two_mul]
  have hpq0 : 0 < p / q := div_pos hp hq
  rcases le_total q p with h | h
  · have hl : 0 ≤ log (p / q) := Real.log_nonneg ((one_le_div hq).2 h)
    rw [abs_of_nonneg (sub_nonneg.2 h),
      abs_of_nonneg (show (0 : ℝ) ≤ ((2 : ℕ) : ℝ) * log (p / q) by positivity)]
    have : 2 * (((2 : ℕ) : ℝ) * log (p / q) / 4) = log (p / q) := by push_cast; ring
    rw [this, Real.exp_log hpq0]
    field_simp
  · have hl : log (p / q) ≤ 0 := Real.log_nonpos hpq0.le ((div_le_one hq).2 h)
    rw [abs_of_nonpos (sub_nonpos.2 h),
      abs_of_nonpos (show ((2 : ℕ) : ℝ) * log (p / q) ≤ 0 by push_cast; linarith)]
    have : 2 * (-(((2 : ℕ) : ℝ) * log (p / q)) / 4) = log (q / p) := by
      rw [show q / p = (p / q)⁻¹ by rw [inv_div], Real.log_inv]; push_cast; ring
    rw [this, Real.exp_log (div_pos hq hp)]
    field_simp
    ring

/-- The key inequality: `|ad - bc| t ≤ κ (a t + b)(c t + d)` for `t > 0`, `κ` the Birkhoff
coefficient, from `act² + bd - 2 √(ac) √(bd) t = (√(ac) t - √(bd))² ≥ 0`. -/
lemma abs_det_mul_le (hM : ∀ i j, 0 < M i j) (t : ℝ) :
    |M 0 0 * M 1 1 - M 0 1 * M 1 0| * t ≤
      M.birkhoffCoeff * ((M 0 0 * t + M 0 1) * (M 1 0 * t + M 1 1)) := by
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  have ha := hM 0 0
  have hb := hM 0 1
  have hc := hM 1 0
  have hd := hM 1 1
  set p := √(a * d)
  set q := √(b * c)
  have hp : 0 < p := Real.sqrt_pos.2 (mul_pos ha hd)
  have hq : 0 < q := Real.sqrt_pos.2 (mul_pos hb hc)
  have hp2 : p ^ 2 = a * d := Real.sq_sqrt (mul_pos ha hd).le
  have hq2 : q ^ 2 = b * c := Real.sq_sqrt (mul_pos hb hc).le
  set r := √(a * c)
  set s := √(b * d)
  have hr2 : r ^ 2 = a * c := Real.sq_sqrt (mul_pos ha hc).le
  have hs2 : s ^ 2 = b * d := Real.sq_sqrt (mul_pos hb hd).le
  have hpqrs : p * q = r * s := by
    rw [← Real.sqrt_mul (mul_pos ha hd).le, ← Real.sqrt_mul (mul_pos ha hc).le]
    congr 1
    ring
  have hdet : |a * d - b * c| = |p - q| * (p + q) := by
    rw [← hp2, ← hq2, show p ^ 2 - q ^ 2 = (p - q) * (p + q) by ring, abs_mul,
      abs_of_pos (add_pos hp hq)]
  have heq : (a * t + b) * (c * t + d) = (p + q) ^ 2 * t + (r * t - s) ^ 2 := by
    linear_combination (-t ^ 2) * hr2 + (-t) * hp2 + (-t) * hq2 + (-1) * hs2 +
      (-2 * t) * hpqrs
  have hsq : (p + q) ^ 2 * t ≤ (a * t + b) * (c * t + d) := by
    rw [heq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  rw [hdet, birkhoffCoeff]
  change |p - q| * (p + q) * t ≤ |p - q| / (p + q) * ((a * t + b) * (c * t + d))
  rw [div_mul_eq_mul_div, le_div_iff₀ (add_pos hp hq)]
  calc |p - q| * (p + q) * t * (p + q) = |p - q| * ((p + q) ^ 2 * t) := by ring
    _ ≤ |p - q| * ((a * t + b) * (c * t + d)) := mul_le_mul_of_nonneg_left hsq (abs_nonneg _)

/-- **Birkhoff's contraction for a positive `2 × 2` matrix.** The ratio map of a matrix with
positive entries is Lipschitz in logarithmic coordinates with constant the Birkhoff coefficient
`tanh (Δ / 4) < 1`. No condition on the determinant. -/
theorem abs_log_ratioMap_sub_le (hM : ∀ i j, 0 < M i j) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |log (M.ratioMap x) - log (M.ratioMap y)| ≤ M.birkhoffCoeff * |log x - log y| := by
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  have ha := hM 0 0
  have hb := hM 0 1
  have hc := hM 1 0
  have hd := hM 1 1
  -- `g u = log (a e^u + b) - log (c e^u + d)`, the ratio map in logarithmic coordinates
  set g : ℝ → ℝ := fun u ↦ log (a * exp u + b) - log (c * exp u + d)
  have hg : ∀ u, HasDerivAt g ((a * d - b * c) * exp u /
      ((a * exp u + b) * (c * exp u + d))) u := by
    intro u
    have he := Real.exp_pos u
    have h1 := (((Real.hasDerivAt_exp u).const_mul a).add_const b).log (by positivity)
    have h2 := (((Real.hasDerivAt_exp u).const_mul c).add_const d).log (by positivity)
    convert h1.sub h2 using 1
    have h3 : a * exp u + b ≠ 0 := by positivity
    have h4 : c * exp u + d ≠ 0 := by positivity
    field_simp
    ring
  have hbound : ∀ u, ‖deriv g u‖ ≤ M.birkhoffCoeff := by
    intro u
    have he := Real.exp_pos u
    rw [(hg u).deriv, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos he,
      abs_of_pos (by positivity : 0 < (a * exp u + b) * (c * exp u + d)),
      div_le_iff₀ (by positivity)]
    exact abs_det_mul_le hM (exp u)
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := g)
    (fun u _ ↦ (hg u).differentiableAt) (fun u _ ↦ hbound u) convex_univ (mem_univ (log y))
    (mem_univ (log x))
  have hgx : g (log x) = log (M.ratioMap x) := by
    simp only [g, Real.exp_log hx, ratioMap]
    rw [Real.log_div (by positivity) (by positivity)]
  have hgy : g (log y) = log (M.ratioMap y) := by
    simp only [g, Real.exp_log hy, ratioMap]
    rw [Real.log_div (by positivity) (by positivity)]
  rw [hgx, hgy, Real.norm_eq_abs, Real.norm_eq_abs] at key
  exact key

/-- On the positive cone of `ℝ²` the Hilbert pseudometric is `|log (x₀/x₁) - log (y₀/y₁)|`. -/
theorem _root_.hilbertEDist_univ_fin_two {x y : Fin 2 → ℝ} (hx : ∀ i, 0 < x i)
    (hy : ∀ i, 0 < y i) :
    hilbertEDist univ x y = ENNReal.ofReal |log (x 0 / x 1) - log (y 0 / y 1)| := by
  have hf : log (x 0 / x 1) - log (y 0 / y 1) =
      (log (x 0) - log (y 0)) - (log (x 1) - log (y 1)) := by
    rw [Real.log_div (hx 0).ne' (hx 1).ne', Real.log_div (hy 0).ne' (hy 1).ne']
    ring
  rw [hf]
  refine le_antisymm (hilbertEDist_le_iff.2 fun i _ j _ ↦ ?_) ?_
  · refine ENNReal.ofReal_le_ofReal ?_
    fin_cases i <;> fin_cases j <;> simp [le_abs_self]
    linarith [neg_abs_le ((log (x 0) - log (y 0)) - (log (x 1) - log (y 1)))]
  · rcases le_total 0 ((log (x 0) - log (y 0)) - (log (x 1) - log (y 1))) with h | h
    · rw [abs_of_nonneg h]
      exact le_hilbertEDist (mem_univ 0) (mem_univ 1)
    · rw [abs_of_nonpos h]
      refine le_of_eq_of_le ?_ (le_hilbertEDist (x := x) (y := y) (mem_univ 1) (mem_univ 0))
      ring_nf

lemma mulVec_fin_two_ratio {x : Fin 2 → ℝ} (hx : 0 < x 1) :
    (M *ᵥ x) 0 / (M *ᵥ x) 1 = M.ratioMap (x 0 / x 1) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two, ratioMap]
  field_simp

/-- **Birkhoff's contraction in the Hilbert metric**: a positive `2 × 2` matrix contracts the
Hilbert pseudometric of the positive cone by its Birkhoff coefficient `tanh (Δ / 4) < 1`. -/
theorem hilbertEDist_mulVec_le (hM : ∀ i j, 0 < M i j) {x y : Fin 2 → ℝ} (hx : ∀ i, 0 < x i)
    (hy : ∀ i, 0 < y i) :
    hilbertEDist univ (M *ᵥ x) (M *ᵥ y) ≤
      ENNReal.ofReal M.birkhoffCoeff * hilbertEDist univ x y := by
  have hMx : ∀ i, 0 < (M *ᵥ x) i := fun i ↦ by
    simp only [mulVec, dotProduct, Fin.sum_univ_two]
    have := hM i 0; have := hM i 1; have := hx 0; have := hx 1
    positivity
  have hMy : ∀ i, 0 < (M *ᵥ y) i := fun i ↦ by
    simp only [mulVec, dotProduct, Fin.sum_univ_two]
    have := hM i 0; have := hM i 1; have := hy 0; have := hy 1
    positivity
  rw [hilbertEDist_univ_fin_two hMx hMy, hilbertEDist_univ_fin_two hx hy,
    mulVec_fin_two_ratio (hx 1), mulVec_fin_two_ratio (hy 1),
    ← ENNReal.ofReal_mul birkhoffCoeff_nonneg]
  exact ENNReal.ofReal_le_ofReal
    (abs_log_ratioMap_sub_le hM (div_pos (hx 0) (hx 1)) (div_pos (hy 0) (hy 1)))

end Matrix
