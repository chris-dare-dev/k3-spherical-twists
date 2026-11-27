/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Convex.ProjectiveJoin
import K3Twists.CategoryTheory.MassProfile.Basic

/-!
# Projective joins of profiles

The projective join of `Analysis/Convex/ProjectiveJoin.lean` lives in a real vector space; for
boundary points of profiles that space is `Obj → ℝ`, the real functionals on objects with the
product topology. This file connects the join with the profile layer of
`CategoryTheory/MassProfile/Basic.lean`, where a group `Γ` of autoequivalences acts on profiles by
`(g • μ)(E) = μ(g⁻¹ • E)`.

## Main definitions

* `Profile.toReal μ`: a profile `μ : Obj → ℝ≥0` as a real functional. It is continuous, injective,
  additive and `ℝ≥0`-linear (`Profile.continuous_toReal`, `Profile.toReal_injective`,
  `Profile.toReal_add`, `Profile.toReal_nnreal_smul`).
* `Profile.translate g`: the action `f ↦ f(g⁻¹ • -)` of `g : Γ` on real functionals, a linear map,
  continuous for the product topology (`Profile.continuous_translate`).

## Main results

* `Profile.toReal_smul`: `toReal` carries the action on profiles to `translate`.
* **Equivariance of the join** (`Profile.translate_projectiveJoin`): `g` carries the join of
  points `f i` normalized by `ℓ` to the join of the points `g • f i` normalized by `ℓ ∘ g⁻¹`, with
  the same weights. For the profiles `h(A_i, -)` of a `Γ`-invariant count, the translated points
  are the profiles `h(g • A_i, -)` (`Profile.translate_projectiveJoin_homProfile`), by
  `Profile.homProfile_smul`: the joins `[w₀ m_* + ∑ w_i h(A_i, -)]` of masses and `Hom` profiles
  are carried to joins of the same shape.
* `Profile.mapClusterPt_translate_iff`: `translate g` preserves cluster points, so cluster sets of
  translated families are the translated cluster sets.

No field is added: everything follows from linearity of the join and `Profile.homProfile_smul`.
-/

open Filter Topology
open scoped NNReal

namespace Profile

variable {Obj : Type*}

/-- A profile as a real functional on objects. -/
def toReal (μ : Profile Obj) : Obj → ℝ := fun E ↦ μ E

@[simp]
lemma toReal_apply (μ : Profile Obj) (E : Obj) : toReal μ E = μ E := rfl

lemma toReal_injective : Function.Injective (toReal : Profile Obj → Obj → ℝ) :=
  fun _ _ h ↦ Profile.ext fun E ↦ NNReal.coe_injective (congrFun h E)

lemma continuous_toReal : Continuous (toReal : Profile Obj → Obj → ℝ) :=
  continuous_pi fun E ↦ NNReal.continuous_coe.comp (continuous_apply E)

@[simp]
lemma toReal_add (μ ν : Profile Obj) : toReal (μ + ν) = toReal μ + toReal ν := by
  funext E
  simp

@[simp]
lemma toReal_nnreal_smul (c : ℝ≥0) (μ : Profile Obj) :
    toReal (c • μ) = (c : ℝ) • toReal μ := by
  funext E
  simp

section Action

variable {Γ : Type*} [Group Γ] [MulAction Γ Obj]

/-- The action `f ↦ f(g⁻¹ • -)` of `g : Γ` on real functionals on objects. -/
def translate (g : Γ) : (Obj → ℝ) →ₗ[ℝ] Obj → ℝ := LinearMap.funLeft ℝ ℝ (g⁻¹ • ·)

@[simp]
lemma translate_apply (g : Γ) (f : Obj → ℝ) (E : Obj) : translate g f E = f (g⁻¹ • E) := rfl

lemma continuous_translate (g : Γ) : Continuous (translate g : (Obj → ℝ) → Obj → ℝ) :=
  continuous_pi fun _ ↦ _root_.continuous_apply _

@[simp]
lemma translate_inv_translate (g : Γ) (f : Obj → ℝ) : translate g⁻¹ (translate g f) = f := by
  funext E
  simp [smul_smul]

@[simp]
lemma translate_translate_inv (g : Γ) (f : Obj → ℝ) : translate g (translate g⁻¹ f) = f := by
  simpa using translate_inv_translate g⁻¹ f

/-- `toReal` carries the action on profiles to `translate`. -/
lemma toReal_smul (g : Γ) (μ : Profile Obj) : toReal (g • μ) = translate g (toReal μ) := by
  funext E
  simp

/-- `translate g` preserves cluster points: `x` is a cluster point of `f` along `l` iff
`translate g x` is a cluster point of `translate g ∘ f`. -/
theorem mapClusterPt_translate_iff {α : Type*} {l : Filter α} (g : Γ) {f : α → Obj → ℝ}
    {x : Obj → ℝ} :
    MapClusterPt (translate g x) l (fun a ↦ translate g (f a)) ↔ MapClusterPt x l f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.continuousAt_comp (continuous_translate g).continuousAt⟩
  have := h.continuousAt_comp (continuous_translate g⁻¹).continuousAt
  simpa [Function.comp_def] using this

/-- **Equivariance of the projective join.** `g` carries the join of the points `f i` normalized by
`ℓ` to the join of the points `g • f i` normalized by `ℓ ∘ g⁻¹`, with the same weights. -/
theorem translate_projectiveJoin {ι : Type*} [Fintype ι] (g : Γ) (ℓ : (Obj → ℝ) →ₗ[ℝ] ℝ)
    (f : ι → Obj → ℝ) (w : ι → ℝ) :
    translate g (projectiveJoin ℓ f w) =
      projectiveJoin (ℓ ∘ₗ translate g⁻¹) (fun i ↦ translate g (f i)) w := by
  simp only [projectiveJoin, map_smul, map_sum, LinearMap.comp_apply, translate_inv_translate]

/-- **Joins of `Hom` profiles.** For a `Γ`-invariant count `h`, `g` carries the join of the
profiles `h(A_i, -)` normalized by `ℓ` to the join of the profiles `h(g • A_i, -)` normalized by
`ℓ ∘ g⁻¹`, with the same weights. -/
theorem translate_projectiveJoin_homProfile {Src ι : Type*} [MulAction Γ Src] [Fintype ι]
    (h : Src → Obj → ℝ≥0) (hh : ∀ (g : Γ) A E, h (g • A) (g • E) = h A E) (g : Γ)
    (ℓ : (Obj → ℝ) →ₗ[ℝ] ℝ) (A : ι → Src) (w : ι → ℝ) :
    translate g (projectiveJoin ℓ (fun i ↦ toReal (homProfile h (A i))) w) =
      projectiveJoin (ℓ ∘ₗ translate g⁻¹) (fun i ↦ toReal (homProfile h (g • A i))) w := by
  rw [translate_projectiveJoin]
  congr 1
  funext i
  rw [← toReal_smul, homProfile_smul h hh]

end Action

end Profile
