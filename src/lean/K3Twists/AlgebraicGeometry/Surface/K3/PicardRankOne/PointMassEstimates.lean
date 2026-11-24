/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The finite estimates behind the point-mass corollary

The algebra inside Lemma A.1 of the article and the arithmetic of its explicit constant:

* `piece_bound`, `slope_bound`: for the cohomology objects `K_i` of a rigid object in the tilted
  heart, `d c_i² = r_i s_i - dim End K_i` and `|Re Z(K_i)| ≤ m(K_i)` give
  `c_i ≤ a|r_i| + d^{-1/2} √(|r_i| m(K_i))`; summing with Cauchy–Schwarz gives
  `V(E) ≤ a R(E) + d^{-1/2} √(R(E) m(E))`;
* `fixedTest_of_generic`: the last paragraph of Lemma A.1, which turns the two generic
  comparisons `|h(E, F) - r_F h(E, 𝒪)| ≤ c'_F X` and `|h(E, G) - 3h(E, 𝒪)| ≤ c'_G X`,
  `X = R + √(R m)`, and `m ≤ C h(E, G)` into `h(E, G) ≤ (6/r_F) h(E, F) + (2b + Cb²) R` with
  `b = c'_G + 3c'_F/r_F`;
* `koszul_bound`: a sequence with `f(s + 3) ≤ 3f(s + 2) + 3f(s + 1) + f(s)` grows at most like
  `7^s`, which is how the Koszul complex of three sections of `A` reaches every power `A^{±s}`
  from `A^{-2}, A^{-1}, 𝒪`;
* `diag_constant`: the five terms of the resolution of the diagonal assemble into the constant
  `K = 5(2 + 36ν)(2 + 25ν)⁸ 7⁴⁶`.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open Finset Real

/-! ### Slopes of rigid objects -/

/-- **One cohomology object.** If `dc² - rs = -e` with `e ≥ 0` (Riemann–Roch for a rigid object,
`e = dim End`) and the real part `da²r - s` of its central charge is at most its mass `m` in
absolute value, then `dc² ≤ da²r² + |r| m`. -/
lemma piece_bound {d a r c s e m : ℝ} (hrig : d * c ^ 2 - r * s = -e) (he : 0 ≤ e)
    (hRe : |d * a ^ 2 * r - s| ≤ m) : d * c ^ 2 ≤ d * a ^ 2 * r ^ 2 + |r| * m := by
  have h2 : -(r * (d * a ^ 2 * r - s)) ≤ |r| * m := by
    calc -(r * (d * a ^ 2 * r - s)) ≤ |r * (d * a ^ 2 * r - s)| := neg_le_abs _
      _ = |r| * |d * a ^ 2 * r - s| := abs_mul _ _
      _ ≤ |r| * m := mul_le_mul_of_nonneg_left hRe (abs_nonneg r)
  nlinarith

/-- From `dc² ≤ da²r² + |r| m` with `c ≥ 0`: `c ≤ a|r| + d^{-1/2} √|r| √m`. -/
lemma c_le_of_piece {d a r c m : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (hc : 0 ≤ c) (hm : 0 ≤ m)
    (h : d * c ^ 2 ≤ d * a ^ 2 * r ^ 2 + |r| * m) :
    c ≤ a * |r| + (√d)⁻¹ * (√|r| * √m) := by
  set y := (√d)⁻¹ * (√|r| * √m) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy2 : y ^ 2 = |r| * m / d := by
    rw [hy, mul_pow, mul_pow, sq_sqrt (abs_nonneg r), sq_sqrt hm, inv_pow, sq_sqrt hd.le]
    field_simp
  have hc2 : c ^ 2 ≤ (a * |r| + y) ^ 2 := by
    have h' : c ^ 2 ≤ a ^ 2 * r ^ 2 + |r| * m / d := by
      rw [show a ^ 2 * r ^ 2 + |r| * m / d = (d * a ^ 2 * r ^ 2 + |r| * m) / d by
        field_simp]
      rw [le_div_iff₀ hd]; linarith
    calc c ^ 2 ≤ a ^ 2 * r ^ 2 + |r| * m / d := h'
      _ = (a * |r|) ^ 2 + y ^ 2 := by rw [hy2, mul_pow, sq_abs]
      _ ≤ (a * |r| + y) ^ 2 := by nlinarith [mul_nonneg ha (abs_nonneg r)]
  exact (pow_le_pow_iff_left₀ hc (by positivity) two_ne_zero).mp hc2

/-- **The slope estimate.** If each piece satisfies `dc_i² ≤ da²r_i² + |r_i| m_i` with
`c_i, m_i ≥ 0`, then `Σ c_i ≤ a Σ|r_i| + d^{-1/2} √(Σ|r_i| · Σ m_i)`. -/
theorem slope_bound {ι : Type*} (s : Finset ι) {d a : ℝ} (hd : 0 < d) (ha : 0 ≤ a)
    (r c m : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (hm : ∀ i, 0 ≤ m i)
    (h : ∀ i ∈ s, d * c i ^ 2 ≤ d * a ^ 2 * r i ^ 2 + |r i| * m i) :
    ∑ i ∈ s, c i ≤ a * ∑ i ∈ s, |r i| + (√d)⁻¹ * √((∑ i ∈ s, |r i|) * ∑ i ∈ s, m i) := by
  calc ∑ i ∈ s, c i ≤ ∑ i ∈ s, (a * |r i| + (√d)⁻¹ * (√|r i| * √(m i))) :=
        sum_le_sum fun i hi => c_le_of_piece hd ha (hc i hi) (hm i) (h i hi)
    _ = a * ∑ i ∈ s, |r i| + (√d)⁻¹ * ∑ i ∈ s, √|r i| * √(m i) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ a * ∑ i ∈ s, |r i| + (√d)⁻¹ * (√(∑ i ∈ s, |r i|) * √(∑ i ∈ s, m i)) := by
        gcongr
        exact sum_sqrt_mul_sqrt_le s (fun i => abs_nonneg (r i)) hm
    _ = a * ∑ i ∈ s, |r i| + (√d)⁻¹ * √((∑ i ∈ s, |r i|) * ∑ i ∈ s, m i) := by
        rw [sqrt_mul (sum_nonneg fun i _ => abs_nonneg (r i))]

/-- The slope estimate in the form used for a rigid object `E`: with `Σ|r_i| ≤ R(E)` and
`Σ m(K_i) = m(E)`, `V(E) = Σ c_i ≤ a R(E) + d^{-1/2} √(R(E) m(E))`. -/
theorem slope_bound_of_le {ι : Type*} (s : Finset ι) {d a R mE : ℝ} (hd : 0 < d) (ha : 0 ≤ a)
    (r c m : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (hm : ∀ i, 0 ≤ m i)
    (h : ∀ i ∈ s, d * c i ^ 2 ≤ d * a ^ 2 * r i ^ 2 + |r i| * m i)
    (hR : ∑ i ∈ s, |r i| ≤ R) (hmE : ∑ i ∈ s, m i = mE) :
    ∑ i ∈ s, c i ≤ a * R + (√d)⁻¹ * √(R * mE) := by
  refine (slope_bound s hd ha r c m hc hm h).trans ?_
  rw [hmE]
  have hmE0 : 0 ≤ mE := hmE ▸ sum_nonneg fun i _ => hm i
  gcongr

/-! ### The last step of Lemma A.1 -/

/-- **Absorbing the square root.** From the two generic comparisons
`|h(E, F) - r_F h(E, 𝒪)| ≤ c'_F X`, `|h(E, G) - 3 h(E, 𝒪)| ≤ c'_G X` with `X = R + √(R m)`,
and the mass bound `m ≤ C h(E, G)`, it follows that
`h(E, G) ≤ (6/r_F) h(E, F) + (2b + Cb²) R` with `b = c'_G + 3c'_F/r_F`. -/
theorem fixedTest_of_generic {hEG hEF hEO R m rF cF cG C : ℝ} (hrF : 0 < rF) (hcF : 0 ≤ cF)
    (hcG : 0 ≤ cG) (hC : 0 ≤ C) (hR : 0 ≤ R) (hEG0 : 0 ≤ hEG)
    (hF : |hEF - rF * hEO| ≤ cF * (R + √(R * m)))
    (hG : |hEG - 3 * hEO| ≤ cG * (R + √(R * m))) (hmass : m ≤ C * hEG) :
    hEG ≤ 6 / rF * hEF + (2 * (cG + 3 * cF / rF) + C * (cG + 3 * cF / rF) ^ 2) * R := by
  set b := cG + 3 * cF / rF with hb
  have hb0 : 0 ≤ b := by positivity
  set X := R + √(R * m) with hX
  -- `h(E, G) ≤ (3/r_F) h(E, F) + b X`
  have step1 : hEG ≤ 3 / rF * hEF + b * X := by
    have h1 := (abs_le.mp hG).2
    have h2 := (abs_le.mp hF).1
    have h3 : hEO ≤ (hEF + cF * X) / rF := by rw [le_div_iff₀ hrF]; linarith
    calc hEG ≤ 3 * hEO + cG * X := by linarith
      _ ≤ 3 * ((hEF + cF * X) / rF) + cG * X := by gcongr
      _ = 3 / rF * hEF + b * X := by rw [hb]; field_simp; ring
  -- `b √(R m) ≤ h(E, G)/2 + C b² R/2`
  set z := √(R * C * hEG) with hz
  have hz0 : 0 ≤ z := sqrt_nonneg _
  have hz2 : z ^ 2 = R * C * hEG := sq_sqrt (by positivity)
  have hy : √(R * m) ≤ z := sqrt_le_sqrt (by nlinarith)
  have hamgm : b * z ≤ (hEG + C * b ^ 2 * R) / 2 := by
    have key : (b * z) ^ 2 ≤ ((hEG + C * b ^ 2 * R) / 2) ^ 2 := by
      rw [mul_pow, hz2]
      nlinarith [sq_nonneg (hEG - C * b ^ 2 * R)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp key
  have step2 : b * X ≤ b * R + (hEG + C * b ^ 2 * R) / 2 := by
    rw [hX, mul_add]
    have : b * √(R * m) ≤ b * z := mul_le_mul_of_nonneg_left hy hb0
    linarith
  have : hEG ≤ 3 / rF * hEF + b * R + (hEG + C * b ^ 2 * R) / 2 := by linarith
  have h6 : 6 / rF * hEF = 2 * (3 / rF * hEF) := by ring
  rw [h6]
  nlinarith

/-! ### The Koszul recursion and the constant `K` -/

/-- **Seven per step.** If `f(s + 3) ≤ 3 f(s + 2) + 3 f(s + 1) + f(s)` and the first three values
are at most `M ≥ 0`, then `f(s) ≤ 7^s M`. For `f(s) = h(U, A^{-2+s})` (or `h(A^{t}, V)` read in
the other direction) this is the Koszul complex `0 → A^{s-3} → (A^{s-2})³ → (A^{s-1})³ → A^s → 0`
of three sections of `A` without common zero. -/
theorem koszul_bound {f : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (h0 : f 0 ≤ M) (h1 : f 1 ≤ M)
    (h2 : f 2 ≤ M) (hrec : ∀ s, f (s + 3) ≤ 3 * f (s + 2) + 3 * f (s + 1) + f s) (s : ℕ) :
    f s ≤ 7 ^ s * M := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    match s, ih with
    | 0, _ => simpa using h0
    | 1, _ => calc f 1 ≤ M := h1
        _ ≤ 7 ^ 1 * M := by nlinarith
    | 2, _ => calc f 2 ≤ M := h2
        _ ≤ 7 ^ 2 * M := by nlinarith
    | s + 3, ih =>
      have a := ih (s + 2) (by omega)
      have b := ih (s + 1) (by omega)
      have c := ih s (by omega)
      have hpow : (0 : ℝ) ≤ 7 ^ s * M := by positivity
      calc f (s + 3) ≤ 3 * f (s + 2) + 3 * f (s + 1) + f s := hrec s
        _ ≤ 3 * (7 ^ (s + 2) * M) + 3 * (7 ^ (s + 1) * M) + 7 ^ s * M := by linarith
        _ = 169 * (7 ^ s * M) := by ring
        _ ≤ 343 * (7 ^ s * M) := by nlinarith
        _ = 7 ^ (s + 3) * M := by ring

/-- The twists `t_j = 3 + 5j`, `0 ≤ j ≤ 4`, of the resolution of the diagonal stay within
`23 = t₄` steps of the starting powers. -/
lemma twist_le (j : Fin 5) : 3 + 5 * (j : ℕ) ≤ 23 := by
  have := j.isLt; omega

/-- **The constant `K`.** The five terms of the resolution of the diagonal contribute at most
`m_j h(U, A^{-t_j}) h(A^{t_j}, V)`, with `m₀ ≤ 2 + 36ν`, `m_{j+1} ≤ m_j (2 + 25ν)²`, and each
Hom factor at most `7²³` times the corresponding `G`-test. Their sum is at most
`5(2 + 36ν)(2 + 25ν)⁸ 7⁴⁶ h(U, G) h(G, V)`. -/
theorem diag_constant {ν X Y : ℝ} (hν : 0 ≤ ν) (m x y : Fin 5 → ℝ)
    (hm0 : m 0 ≤ 2 + 36 * ν) (hm : ∀ j : Fin 4, m j.succ ≤ m j.castSucc * (2 + 25 * ν) ^ 2)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 7 ^ 23 * X)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 7 ^ 23 * Y) :
    ∑ j, m j * x j * y j ≤ 5 * (2 + 36 * ν) * (2 + 25 * ν) ^ 8 * 7 ^ 46 * X * Y := by
  set q := (2 + 25 * ν) ^ 2 with hq
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith
  have hq0 : 0 ≤ q := by positivity
  -- `m_j ≤ (2 + 36ν) q⁴` for every `j`
  have m1 : m 1 ≤ (2 + 36 * ν) * q := (hm 0).trans (by gcongr; exact hm0)
  have m2 : m 2 ≤ (2 + 36 * ν) * q ^ 2 := (hm 1).trans (by
    calc m 1 * q ≤ (2 + 36 * ν) * q * q := by gcongr
      _ = (2 + 36 * ν) * q ^ 2 := by ring)
  have m3 : m 3 ≤ (2 + 36 * ν) * q ^ 3 := (hm 2).trans (by
    calc m 2 * q ≤ (2 + 36 * ν) * q ^ 2 * q := by gcongr
      _ = (2 + 36 * ν) * q ^ 3 := by ring)
  have m4 : m 4 ≤ (2 + 36 * ν) * q ^ 4 := (hm 3).trans (by
    calc m 3 * q ≤ (2 + 36 * ν) * q ^ 3 * q := by gcongr
      _ = (2 + 36 * ν) * q ^ 4 := by ring)
  have hc0 : 0 ≤ 2 + 36 * ν := by positivity
  have hmax : ∀ j, m j ≤ (2 + 36 * ν) * q ^ 4 := by
    intro j
    fin_cases j
    · simp only [Fin.zero_eta]
      calc m 0 ≤ 2 + 36 * ν := hm0
        _ ≤ (2 + 36 * ν) * q ^ 4 := le_mul_of_one_le_right hc0 (one_le_pow₀ hq1)
    · exact m1.trans (mul_le_mul_of_nonneg_left (le_self_pow₀ hq1 (by norm_num)) hc0)
    · exact m2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 (by norm_num)) hc0)
    · exact m3.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 (by norm_num)) hc0)
    · exact m4
  have hX : 0 ≤ X := by
    have := (hx 0).1.trans (hx 0).2
    nlinarith [pow_pos (show (0 : ℝ) < 7 by norm_num) 23]
  have hY : 0 ≤ Y := by
    have := (hy 0).1.trans (hy 0).2
    nlinarith [pow_pos (show (0 : ℝ) < 7 by norm_num) 23]
  have hterm : ∀ j, m j * x j * y j ≤ (2 + 36 * ν) * q ^ 4 * (7 ^ 23 * X) * (7 ^ 23 * Y) := by
    intro j
    have hM0 : 0 ≤ (2 + 36 * ν) * q ^ 4 := mul_nonneg hc0 (pow_nonneg hq0 4)
    have hX0 : 0 ≤ 7 ^ 23 * X := mul_nonneg (by norm_num) hX
    exact mul_le_mul (mul_le_mul (hmax j) (hx j).2 (hx j).1 hM0) (hy j).2 (hy j).1
      (mul_nonneg hM0 hX0)
  calc ∑ j, m j * x j * y j ≤ ∑ _j : Fin 5, (2 + 36 * ν) * q ^ 4 * (7 ^ 23 * X) * (7 ^ 23 * Y) :=
        sum_le_sum fun j _ => hterm j
    _ = 5 * (2 + 36 * ν) * (2 + 25 * ν) ^ 8 * 7 ^ 46 * X * Y := by
        rw [sum_const, card_univ, Fintype.card_fin, hq]; ring

end AlgebraicGeometry.K3.PicardRankOne
