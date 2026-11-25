/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.StabilitySpace

/-!
# The stability-space interface can hold

A theorem proved from hypotheses that cannot hold together says nothing. This file builds
`StabilitySpaceHypotheses` on the one-point space at a prestability condition `σ`, assuming of `σ`
only that its central charge is injective on the class lattice (which gives the support property
for the norm `x ↦ |Z(x)|`) and Ikeda subadditivity. The covering, the metric bounds and the action
of the trivial group hold by proof, and the path layer and the `2m(D)` lemma apply.

This is a relative check: Mathlib has no triangulated category with a slicing yet, so the
prestability condition is a variable here.

Built by `lake test`.
-/

noncomputable section

namespace CategoryTheory.Triangulated.StabilitySpaceModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- **The one-point model.** A prestability condition with injective central charge and Ikeda
subadditivity is a space of stability conditions with one point, on which the trivial group
acts by the identity. -/
def onePoint (σ : PreStabilityCondition.WithClassMap C v) (hZ : Function.Injective σ.Z)
    (hσ : σ.MassSubadditive) : StabilitySpaceHypotheses C v Unit Unit where
  cond _ := σ
  isCoveringMap_charge := by
    have : Subsingleton (Set.range fun _ : Unit => ⇑σ.Z) :=
      (Set.subsingleton_range _).coe_sort
    exact IsCoveringMap.of_discreteTopology _
  abs_phiPlus_sub_le _ _ E hE := by simp
  abs_phiMinus_sub_le _ _ E hE := by simp
  mass_le_exp_dist _ _ E := by simp
  classNorm x := ‖σ.Z x‖
  classNorm_pos x hx := norm_pos_iff.mpr fun h => hx (hZ (h.trans (map_zero σ.Z).symm))
  support _ := ⟨1, one_pos, fun _ E _ => by
    simp [PreStabilityCondition.WithClassMap.charge_def]⟩
  tri _ := TriEquiv.id
  slicing_smul _ _ := (TriEquiv.act_id _).symm
  charge_smul _ _ _ := rfl
  mass_subadditive _ := hσ

/-- In the model, the path layer applies to every path. -/
example (σ : PreStabilityCondition.WithClassMap C v) (hZ : Function.Injective σ.Z)
    (hσ : σ.MassSubadditive) (γ : ℝ → Unit) (hγ : ContinuousOn γ (Set.Icc 0 1)) :
    ∃ N : ℕ, 0 < N ∧ ∀ k < N, σ.slicing.PhaseClose σ.slicing (1 / 4) :=
  (onePoint σ hZ hσ).exists_subdivision_phaseClose γ hγ (by norm_num)

/-- In the model, the `2m(D)` lemma applies. -/
example [IsTriangulated C] (σ : PreStabilityCondition.WithClassMap C v)
    (hZ : Function.Injective σ.Z) (hσ : σ.MassSubadditive) {A B D K K' : C} {f f' : A ⟶ B}
    (a : A ⟶ D) (b : D ⟶ B) (hf : f' = f + a ≫ b) {g : B ⟶ K} {h : K ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) {g' : B ⟶ K'} {h' : K' ⟶ A⟦(1 : ℤ)⟧}
    (hT' : Triangle.mk f' g' h' ∈ distTriang C) :
    |σ.mass K - σ.mass K'| ≤ 2 * σ.mass D :=
  (onePoint σ hZ hσ).abs_sub_mass_cone_le () a b hf hT hT'

end CategoryTheory.Triangulated.StabilitySpaceModel
