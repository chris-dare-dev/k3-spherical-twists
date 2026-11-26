/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.GroupAction.FillingProfile
import K3TwistsTest.PointMassModel

/-!
# The inputs of the filling theorem are consistent

A theorem proved from inconsistent hypotheses says nothing. This file builds a model of
`FillingHypotheses` for any action of a group `Γ` on a type `Obj`: one summand `S = G`, the
constant count `h ≡ 1`, the constant profile `μ ≡ 1`, every constant equal to one and every object
a test object. Every field holds, and the filling theorem specializes to rate one.

Every autoequivalence of the model of `K3TwistsTest/PointMassModel.lean` is standard, so the
point-mass instance `PointMassHypotheses.toFillingHypotheses` does not apply to it. Its variant in
which no autoequivalence is standard is again a model of `PointMassHypotheses`: the rank is one
everywhere, so `R(Φ 𝒪_x) = 0` never holds, and the fields on standard autoequivalences are empty.
The point-mass instance applies to this variant, and the filling theorem gives the comparison for
a fixed period and rate one there. On the point-mass model itself the file checks that a fixed
point has entropy zero and that the point profile is the rank on spherical objects only.

The models say nothing about K3 surfaces; they only show that the lists of inputs can be met.

Built by `lake test`.
-/

namespace FillingProfileModel

open AlgebraicGeometry.K3.PicardRankOne Filter Topology Real

/-! ### The constant model -/

section Constant

variable (Obj Γ : Type*) [Group Γ] [MulAction Γ Obj]

/-- The constant model: one summand `S = G`, `h ≡ 1`, `μ ≡ 1`, all constants one and every object
a test object. -/
noncomputable def constModel (G : Obj) (Φ : Γ) : FillingHypotheses Obj Γ Unit where
  hom _ _ := 1
  hom_nonneg _ _ := zero_le_one
  hom_comm _ _ := rfl
  hom_smul _ _ _ := rfl
  G := G
  S _ := G
  hom_G _ := by simp
  K := 1
  K_pos := one_pos
  hom_diag _ _ := by norm_num
  one_le_hom_G _ := le_rfl
  μ _ := 1
  μ_nonneg _ := zero_le_one
  T _ := True
  T_S _ := trivial
  T_smul _ _ _ := trivial
  K' := 1
  generation _ _ := by simp
  ν := 1
  ν_pos := one_pos
  dom _ _ := by norm_num
  Φ := Φ
  C := 1
  fill _ _ := by norm_num

/-- The one-object model: the trivial group acting on one object. -/
noncomputable example : FillingHypotheses Unit Unit Unit := constModel Unit Unit () ()

/-- In the constant model the categorical entropy of every element is zero. -/
lemma constModel_hcat (G : Obj) (Φ Ψ : Γ) : (constModel Obj Γ G Φ).hcat Ψ = 0 := by
  refine tendsto_nhds_unique ((constModel Obj Γ G Φ).tendsto_hcat Ψ) ?_
  show Tendsto (fun n : ℕ => log 1 / n) atTop (𝓝 0)
  simp only [log_one, zero_div]
  exact tendsto_const_nhds

/-- In the constant model the filling comparison holds with the constant `C (1 + K' H(Φ)) = 2`. -/
example (G : Obj) (Φ W : Γ) (hW : Commute W Φ) :
    (constModel Obj Γ G Φ).H W ≤ 2 * (constModel Obj Γ G Φ).P W := by
  have h := (constModel Obj Γ G Φ).H_le_mul_P hW
  norm_num [constModel, FillingHypotheses.H] at h ⊢
  exact h

/-- In the constant model the filling theorem gives rate one along the powers of `Φ`. -/
example (G : Obj) (Φ : Γ) :
    Tendsto (fun n : ℕ => (constModel Obj Γ G Φ).P (Φ ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
  have h := (constModel Obj Γ G Φ).tendsto_P_pow
  rw [constModel_hcat, exp_zero] at h
  exact h

/-- In the constant model the filling theorem gives rate one along the negative powers of `Φ`. -/
example (G : Obj) (Φ : Γ) :
    Tendsto (fun n : ℕ => (constModel Obj Γ G Φ).P (Φ⁻¹ ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
  have h := (constModel Obj Γ G Φ).tendsto_P_inv_pow
  rw [constModel_hcat, exp_zero] at h
  exact h

end Constant

/-! ### The point-mass instance -/

/-- Every autoequivalence of the point-mass model is standard. -/
example (g : Unit) : PointMassModel.model.Standard g := trivial

/-- The point-mass model with no standard autoequivalence. -/
noncomputable def nonstandardModel : PointMassHypotheses PointMassModel.Obj Unit Unit Unit :=
  { PointMassModel.model with
    Standard := fun _ => False
    standard_of_rank_zero := fun _ _ h => absurd h one_ne_zero
    standard_zpow := fun _ h _ => h
    standard_mass := fun _ h _ => h.elim
    standard_hom := fun _ h => h.elim }

/-- In the nonstandard model the categorical entropy of every word is zero. -/
lemma nonstandardModel_hcat (Φ : Unit) : nonstandardModel.hcat Φ = 0 :=
  PointMassModel.model_hcat Φ

/-- The point-mass instance of the filling theorem, on the nonstandard model. -/
noncomputable example : FillingHypotheses PointMassModel.Obj Unit (Fin 3) :=
  nonstandardModel.toFillingHypotheses () not_false

/-- The comparison for a fixed period, re-derived from the filling theorem, on the nonstandard
model. -/
example : ∃ J > 0, ∀ W : Unit, Commute W () → nonstandardModel.H W ≤ J * nonstandardModel.p W :=
  nonstandardModel.exists_H_le_mul_p_of_filling () not_false

/-- On the nonstandard model the filling theorem gives rate one for the point measurement. -/
example : Tendsto (fun n : ℕ => nonstandardModel.p (() ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
  have h := nonstandardModel.tendsto_p_pow () not_false
  rwa [nonstandardModel_hcat, exp_zero] at h

/-- On the point-mass model the group fixes the point, so a fixed point has entropy zero. -/
example : PointMassModel.model.hcat () = 0 :=
  PointMassModel.model.hcat_eq_zero_of_smul_point_eq (x := ()) rfl

/-- On the point-mass model the point profile is the rank on the spherical summands, but not on the
generator `G`, which is not spherical there: `h(G, 𝒪_x) = 3` while `R(G) = 1`. -/
example : PointMassModel.model.pointProfile () 0 = PointMassModel.model.rank 0 ∧
    PointMassModel.model.pointProfile () 3 = 3 := by
  refine ⟨PointMassModel.model.pointProfile_eq_rank ()
    (show (0 : PointMassModel.Obj).val < 3 by decide), ?_⟩
  show PointMassModel.w 3 * PointMassModel.w 4 = 3
  rw [PointMassModel.w_G, PointMassModel.w_of_ne (by decide)]
  norm_num

end FillingProfileModel
