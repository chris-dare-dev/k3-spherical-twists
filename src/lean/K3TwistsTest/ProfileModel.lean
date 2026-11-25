/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.HomProfile

/-!
# The profile layer on Kronecker representations

`Profile` has no fields to satisfy, so the check here is that its instance from real objects is
not trivial: on representations of the doubled Kronecker quiver with two arrows, relabelling the
arrows moves the `Hom` profile of the representation `k ⇉ k` with arrows `(1, 0)` (all `B`
arrows zero) to a different profile. The profile of `P` takes the value `dim Hom(P, P) ≥ 1` at
`P`, while its relabelling takes the value `dim Hom(σ • P, P) = 0` there.
-/

open Module Profile Quiver.Kronecker DoubledRep
open scoped NNReal

namespace ProfileModel

variable (k : Type*) [Field k]

/-- The representation `k ⇉ k` with `A₀ = 1`, `A₁ = 0` and both `B` arrows zero. -/
def P : DoubledRep k (Fin 2) k k := ⟨![LinearMap.id, 0], fun _ ↦ 0⟩

/-- The relabelling that swaps the two arrows. -/
def σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1

lemma Hom_σP_P : Hom (σ • P k) (P k) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun f hf ↦ ?_
  have h0 := (hf 0).1
  have h1 := (hf 1).1
  simp only [smul_A, σ, P, Equiv.swap_inv, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.comp_zero, LinearMap.comp_id,
    LinearMap.id_comp, LinearMap.zero_comp] at h0 h1
  exact Prod.ext h0.symm h1

lemma homDim_σP_P : homDim (σ • P k) (P k) = 0 := by
  rw [homDim, Hom_σP_P, finrank_bot]

lemma one_le_homDim_P_P : 1 ≤ homDim (P k) (P k) := by
  rw [homDim, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  intro h
  have hid := id_mem_Hom (P k)
  rw [h, Submodule.mem_bot] at hid
  have := congrArg (fun f ↦ f.1 1) hid
  simp at this

/-- Relabelling the arrows moves the profile `h(P, -)` to a different profile. -/
theorem smul_homDimProfile_ne :
    σ • (homDimProfile (P k) : Profile (DoubledRep k (Fin 2) k k)) ≠ homDimProfile (P k) := by
  rw [smul_homDimProfile]
  intro h
  have := congrArg (fun μ : Profile (DoubledRep k (Fin 2) k k) ↦ μ (P k)) h
  simp only [homDimProfile_apply, homDim_σP_P, Nat.cast_zero] at this
  have h1 : (1 : ℝ≥0) ≤ homDim (P k) (P k) := by exact_mod_cast one_le_homDim_P_P k
  rw [← this] at h1
  exact absurd h1 (by norm_num)

/-- The pseudometrics over the set of all representations are invariant under relabelling. -/
example (τ : Equiv.Perm (Fin 2)) (μ ν : Profile (DoubledRep k (Fin 2) k k)) :
    thompsonEDist Set.univ (τ • μ) (τ • ν) = thompsonEDist Set.univ μ ν ∧
      halfHilbertEDist Set.univ (τ • μ) (τ • ν) = halfHilbertEDist Set.univ μ ν :=
  ⟨thompsonEDist_smul_of_invariant (fun _ _ _ ↦ Set.mem_univ _) τ μ ν,
    halfHilbertEDist_smul_of_invariant (fun _ _ _ ↦ Set.mem_univ _) τ μ ν⟩

end ProfileModel
