/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import K3Twists.CategoryTheory.MassProfile.Basic
import K3Twists.RepresentationTheory.Quiver.Kronecker.Preprojective

/-!
# Hom profiles of Kronecker representations

The profile layer (`CategoryTheory/MassProfile/Basic.lean`) on real objects: representations of
the doubled Kronecker quiver with arrow set `ι`, the count `h(M, N) = dim_k Hom(M, N)` and the
group `Equiv.Perm ι` of relabellings of the arrows, which acts on representations by
`(σ • M)_i = M_{σ⁻¹ i}` for both families of arrows. Relabelling is an automorphism of the
quiver fixing its vertices, so it preserves the preprojective relations and the morphism spaces,
`Hom(σ • M, σ • N) = Hom(M, N)` as subspaces (`Hom_smul`). The profile `h(A, -)` therefore
satisfies `σ • h(A, -) = h(σ • A, -)` (`smul_homDimProfile`, an instance of
`Profile.homProfile_smul`).

Relabelling does not preserve isomorphism classes: for `ι = Fin 2`, the representation
`k ⇉ k` with arrows `(1, 0)` and its relabelling `(0, 1)` have different profiles (checked in
`K3TwistsTest/ProfileModel.lean`), so the action on profiles is not trivial.
-/

open Module
open scoped NNReal

namespace Quiver.Kronecker.DoubledRep

variable {k ι V₀ V₁ W₀ W₁ : Type*} [Field k] [AddCommGroup V₀] [Module k V₀]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup W₀] [Module k W₀] [AddCommGroup W₁]
  [Module k W₁]

/-- Relabelling the arrows: `(σ • M).A i = M.A (σ⁻¹ i)` and `(σ • M).B i = M.B (σ⁻¹ i)`. -/
instance : MulAction (Equiv.Perm ι) (DoubledRep k ι V₀ V₁) where
  smul σ M := ⟨fun i ↦ M.A (σ⁻¹ i), fun i ↦ M.B (σ⁻¹ i)⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
lemma smul_A (σ : Equiv.Perm ι) (M : DoubledRep k ι V₀ V₁) (i : ι) :
    (σ • M).A i = M.A (σ⁻¹ i) :=
  rfl

@[simp]
lemma smul_B (σ : Equiv.Perm ι) (M : DoubledRep k ι V₀ V₁) (i : ι) :
    (σ • M).B i = M.B (σ⁻¹ i) :=
  rfl

/-- Relabelling preserves the preprojective relations. -/
lemma IsPreprojective.smul [Fintype ι] {M : DoubledRep k ι V₀ V₁} (hM : M.IsPreprojective)
    (σ : Equiv.Perm ι) : (σ • M).IsPreprojective := by
  refine ⟨?_, ?_⟩
  · simpa using (Equiv.sum_comp σ⁻¹ fun i ↦ M.B i ∘ₗ M.A i).trans hM.1
  · simpa using (Equiv.sum_comp σ⁻¹ fun i ↦ M.A i ∘ₗ M.B i).trans hM.2

/-- Relabelling both representations does not change the morphisms between them. -/
lemma Hom_smul (σ : Equiv.Perm ι) (M : DoubledRep k ι V₀ V₁) (N : DoubledRep k ι W₀ W₁) :
    Hom (σ • M) (σ • N) = Hom M N := by
  ext f
  simp only [mem_Hom, smul_A, smul_B]
  exact ⟨fun h i ↦ by simpa using h (σ i), fun h i ↦ h (σ⁻¹ i)⟩

/-- The dimension `h(M, N) = dim_k Hom(M, N)` of the morphism space. -/
noncomputable def homDim (M : DoubledRep k ι V₀ V₁) (N : DoubledRep k ι W₀ W₁) : ℕ :=
  finrank k (Hom M N)

lemma homDim_smul (σ : Equiv.Perm ι) (M : DoubledRep k ι V₀ V₁) (N : DoubledRep k ι W₀ W₁) :
    homDim (σ • M) (σ • N) = homDim M N := by
  rw [homDim, homDim, Hom_smul]

/-- The profile `h(A, -) = dim_k Hom(A, -)` on representations on `W₀, W₁`. -/
noncomputable def homDimProfile (A : DoubledRep k ι V₀ V₁) : Profile (DoubledRep k ι W₀ W₁) :=
  Profile.homProfile (fun M N ↦ (homDim M N : ℝ≥0)) A

@[simp]
lemma homDimProfile_apply (A : DoubledRep k ι V₀ V₁) (E : DoubledRep k ι W₀ W₁) :
    homDimProfile A E = homDim A E :=
  rfl

/-- Relabelling the arrows carries the profile of `A` to the profile of the relabelled `A`. -/
theorem smul_homDimProfile (σ : Equiv.Perm ι) (A : DoubledRep k ι V₀ V₁) :
    σ • (homDimProfile A : Profile (DoubledRep k ι W₀ W₁)) = homDimProfile (σ • A) :=
  Profile.homProfile_smul _ (fun σ M N ↦ by rw [homDim_smul]) σ A

end Quiver.Kronecker.DoubledRep
