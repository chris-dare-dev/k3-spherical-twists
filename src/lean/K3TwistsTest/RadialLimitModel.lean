/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Mass.RadialLimit

/-!
# The fields of a radial ray can hold together

A theorem proved from hypotheses that cannot hold together says nothing. This file builds
`RadialRayHypotheses` on the constant ray at one prestability condition `σ`: the direction is
`V = 0`, so every class is radial; the mass is constant along the ray; and the one candidate sum of
an object is read from one of its HN filtrations. The radial limit is then the mass, and the class
infimum of the radial limit is `|Z(γ)|` on every class with a semistable representative.

This is a relative check: Mathlib has no triangulated category with a slicing yet, so the
prestability condition is a variable here.

Built by `lake test`.
-/

noncomputable section

namespace CategoryTheory.Triangulated.RadialLimitModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Set

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- A sum of single classes, read through a weight. -/
lemma sum_sum_single {ι M : Type*} (s : Finset ι) (c : ι → M) (g : M → ℝ) :
    ((∑ i ∈ s, Finsupp.single (c i) (1 : ℕ)).sum fun γ k ↦ (k : ℝ) * g γ) = ∑ i ∈ s, g (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.sum_add_index' (fun _ ↦ by simp)
      (fun _ _ _ ↦ by push_cast; ring), Finsupp.sum_single_index (by simp), ih]
    simp

/-- **The constant ray** at a prestability condition: `σ_a = σ`, `V = 0`, `L = 0`. -/
def constantRay (σ : PreStabilityCondition.WithClassMap C v) : RadialRayHypotheses C v where
  cond _ := σ
  a₀ := 1
  a₀_pos := one_pos
  Z₀ := σ.Z
  V := 0
  charge_eq _ _ γ := by simp
  L := 0
  L_nonneg := le_rfl
  continuousOn_mass _ := continuousOn_const
  finite_selection E _ _ := by
    classical
    obtain ⟨F⟩ := σ.slicing.hn_exists E
    refine ⟨1, fun _ ↦ ∑ i, Finsupp.single (classOf C v (F.factor i)) 1,
      fun _ γ _ ↦ Or.inr fun a _ ↦ by simp, fun a _ ↦ ⟨0, ?_⟩⟩
    dsimp only
    rw [σ.mass_eq_sum F]
    rw [sum_sum_single Finset.univ (fun i ↦ classOf C v (F.factor i))
      (fun γ ↦ ‖σ.Z γ + a * (0 : Λ →+ ℂ) γ‖)]
    simp [PreStabilityCondition.WithClassMap.charge_def]

/-- On the constant ray the radial limit is the mass. -/
example (σ : PreStabilityCondition.WithClassMap C v) (E : C) :
    (constantRay σ).radialMass E = σ.mass E :=
  tendsto_nhds_unique ((constantRay σ).tendsto_radialMass E) tendsto_const_nhds

/-- On the constant ray the class infimum of the radial limit is `|Z(γ)|`, on a class with a
semistable representative in `𝒮`. -/
example (σ : PreStabilityCondition.WithClassMap C v) {𝒮 : Set C} {γ : Λ}
    (h : ∃ S ∈ 𝒮, classOf C v S = γ ∧ ∃ φ, σ.slicing.P φ S) :
    (Profile.classInf 𝒮 (classOf C v) (constantRay σ).radialProfile γ : ℝ) = ‖σ.Z γ‖ :=
  (constantRay σ).classInf_radialProfile fun _ _ ↦ h

end CategoryTheory.Triangulated.RadialLimitModel
