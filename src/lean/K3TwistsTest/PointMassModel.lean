/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.PointMass

/-!
# The inputs of the point-mass corollary are consistent

A theorem proved from inconsistent hypotheses says nothing. This file builds a model of
`PointMassHypotheses`, and with it of `MassComparisonHypotheses`: five objects `S₀, S₁, S₂, G, 𝒪_x`
with total Hom `h(U, V) = w(U) w(V)` and mass `w(U)` for the weights `1, 1, 1, 3, 1`, the trivial
group of autoequivalences (every twist is the identity), one stability condition with the zero
distance bound, and one point. Every field holds, and the corollary specializes to rate one.

The model says nothing about K3 surfaces; it only shows that the list of inputs can be met.

Built by `lake test`.
-/

namespace AlgebraicGeometry.K3.PicardRankOne.PointMassModel

open Filter Topology Real

/-- `S₀, S₁, S₂` are `0, 1, 2`, `G` is `3` and the point is `4`. -/
abbrev Obj := Fin 5

/-- The weights `w(S_i) = 1`, `w(G) = 3`, `w(𝒪_x) = 1`. -/
def w (U : Obj) : ℝ := if U = 3 then 3 else 1

lemma w_nonneg (U : Obj) : 0 ≤ w U := by unfold w; split_ifs <;> norm_num

lemma w_G : w 3 = 3 := by simp [w]

lemma w_of_ne {U : Obj} (h : U ≠ 3) : w U = 1 := by simp [w, h]

lemma ne_of_spherical {U : Obj} (h : U.val < 3) : U ≠ 3 := fun e => by simp [e] at h

lemma w_S (i : Fin 3) : w (Fin.castLE (by norm_num) i) = 1 := by
  fin_cases i <;> simp [w]

/-- The trivial group acts trivially on the objects. -/
instance : MulAction Unit Obj where
  smul _ U := U
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma unit_smul (g : Unit) (U : Obj) : g • U = U := rfl

/-- The model. -/
noncomputable def model : PointMassHypotheses Obj Unit Unit Unit where
  mass _ U := w U
  mass_nonneg _ U := w_nonneg U
  δ _ _ := 0
  δ_nonneg _ _ := le_rfl
  δ_symm _ _ := rfl
  mass_le_exp_δ _ _ U := by simp
  hom U V := w U * w V
  hom_nonneg U V := mul_nonneg (w_nonneg U) (w_nonneg V)
  hom_comm _ _ := mul_comm _ _
  hom_smul _ _ _ := rfl
  mass_smul _ _ _ := rfl
  G := 3
  S i := Fin.castLE (by norm_num) i
  hom_G V := by
    show w 3 * w V = ∑ i : Fin 3, w (Fin.castLE _ i) * w V
    rw [Fin.sum_univ_three, w_S, w_S, w_S, w_G]; ring
  K := 1
  K_pos := one_pos
  hom_diag U V := by
    show w U * w V ≤ 1 * (w U * w 3) * (w 3 * w V)
    rw [w_G]; nlinarith [mul_nonneg (w_nonneg U) (w_nonneg V)]
  one_le_hom_G _ := by
    show 1 ≤ w 3 * w (3 : Obj)
    rw [w_G]; norm_num
  Spherical U := U.val < 3
  spherical_S i := i.isLt
  spherical_smul _ _ h := h
  twist _ := ()
  twist_conj _ _ _ := rfl
  twist_smul_of_hom_eq_zero _ _ _ _ := rfl
  mass_twist_le _ E V _ := by
    show w V ≤ w V + w E * w V * w E
    nlinarith [mul_nonneg (mul_nonneg (w_nonneg E) (w_nonneg V)) (w_nonneg E)]
  mass_twist_inv_le _ E V _ := by
    show w V ≤ w V + w V * w E * w E
    nlinarith [mul_nonneg (mul_nonneg (w_nonneg V) (w_nonneg E)) (w_nonneg E)]
  hom_mul_mass_le _ E V h := by
    show w E * w V * w E ≤ w V + w V
    rw [w_of_ne (ne_of_spherical h)]; nlinarith [w_nonneg V]
  mass_pos_of_spherical _ E h := by
    show 0 < w E
    rw [w_of_ne (ne_of_spherical h)]; norm_num
  C₁ := 1
  C₁_pos := one_pos
  dhkk_comparison _ U := by
    show 1 * w U ≤ w 3 * (w 3 * w U)
    rw [w_G]; nlinarith [w_nonneg U]
  rank _ := 1
  point _ := 4
  τ := ()
  Standard _ := True
  ν := 1
  ν_pos := one_pos
  δ_le_dist _ _ := dist_nonneg
  rank_nonneg _ := zero_le_one
  hom_point U _ h := by
    show w U * w 4 = 1
    rw [w_of_ne (ne_of_spherical h), w_of_ne (by decide)]; norm_num
  nu_rank_le U h := by
    show 1 * 1 ≤ w U * w 3
    rw [w_of_ne (ne_of_spherical h), w_G]; norm_num
  fixedTest F _ := ⟨3, by norm_num, fun U h => by
    show w U * w 3 ≤ 3 * (1 + w U * w F)
    rw [w_of_ne (ne_of_spherical h), w_G]
    nlinarith [w_nonneg F]⟩
  standard_of_rank_zero _ _ _ := trivial
  standard_zpow _ _ _ := trivial
  standard_mass _ _ _ := by
    show w 4 = 1
    exact w_of_ne (by decide)
  standard_hom _ _ := ⟨9, 0, fun n => by
    show w 3 * w (3 : Obj) ≤ 9 + 0 * (n : ℝ) ^ 2
    rw [w_G]; norm_num⟩
  mass_pos _ _ _ := by
    show 0 < w 4
    rw [w_of_ne (by decide)]; norm_num

/-- In the model the categorical entropy of every word is zero. -/
lemma model_hcat (Φ : Unit) : model.hcat Φ = 0 := by
  refine tendsto_nhds_unique (model.hcat_spec Φ) ?_
  show Tendsto (fun n : ℕ => log (w 3 * w (3 : Obj)) / n) atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- In the model the corollary gives rate one. -/
example : Tendsto (fun n : ℕ => model.mass () (() ^ n • model.point ()) ^ (n : ℝ)⁻¹) atTop
    (𝓝 1) := by
  simpa [model_hcat] using model.tendsto_pointMass () () ()

end AlgebraicGeometry.K3.PicardRankOne.PointMassModel
