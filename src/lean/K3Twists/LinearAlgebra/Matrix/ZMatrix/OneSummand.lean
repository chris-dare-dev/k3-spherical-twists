/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Linarith

/-!
# Roots of an orthogonal sum lie in one summand

Let `B` be a bilinear form on an abelian group `M`, and `x : A → M` a finite family of mutually
orthogonal vectors with `B(x a, x a) ≤ -2` whenever `x a ≠ 0`: summands of an orthogonal sum of
even negative definite lattices, in the Mukai sign. If `Σ x a` is a root, `B(Σ x a, Σ x a) = -2`,
then **all but one of the `x a` vanish** (`LinearMap.BilinForm.exists_forall_ne_eq_zero`): the
form of the sum is the sum of the forms, each term is `0` or at most `-2`, and two nonzero terms
give at most `-4`.

This is the lemma that makes several exceptional fibres reduce to one: a `(-2)`-class supported on
mutually orthogonal fibres lies on one of them
(`Mukai.FundamentalCycle.exists_forall_ne_eq_zero_of_root`, in
`LinearAlgebra/Lattice/Mukai/AffineWeyl/SeveralFibres.lean`). Kac, *Infinite dimensional Lie
algebras*, §1.2, states the corresponding decomposition of the root system of a decomposable
Cartan matrix.
-/

namespace LinearMap.BilinForm

variable {M A : Type*} [AddCommGroup M] [Fintype A] (B : LinearMap.BilinForm ℤ M)

/-- The form of a sum of mutually orthogonal vectors is the sum of their forms. -/
theorem apply_sum_sum_of_orthogonal {x : A → M}
    (horth : ∀ a a', a ≠ a' → B (x a) (x a') = 0) :
    B (∑ a, x a) (∑ a, x a) = ∑ a, B (x a) (x a) := by
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_eq_single a (fun a' _ h => horth a' a h) (by simp)

/-- **Roots of an orthogonal sum lie in one summand.** If the `x a` are mutually orthogonal, each
nonzero one has `B(x a, x a) ≤ -2`, and `B(Σ x a, Σ x a) = -2`, then all but one of the `x a`
are zero. -/
theorem exists_forall_ne_eq_zero {x : A → M} (horth : ∀ a a', a ≠ a' → B (x a) (x a') = 0)
    (hneg : ∀ a, x a ≠ 0 → B (x a) (x a) ≤ -2) (hroot : B (∑ a, x a) (∑ a, x a) = -2) :
    ∃ a, ∀ a', a' ≠ a → x a' = 0 := by
  classical
  rw [B.apply_sum_sum_of_orthogonal horth] at hroot
  have hle : ∀ a, B (x a) (x a) ≤ 0 := fun a => by
    by_cases h : x a = 0
    · simp [h]
    · linarith [hneg a h]
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra! h
    simp [h] at hroot
  refine ⟨a, fun a' ha' => ?_⟩
  by_contra h'
  have hsub : ({a, a'} : Finset A) ⊆ Finset.univ := Finset.subset_univ _
  have := Finset.sum_le_sum_of_subset_of_nonpos hsub (fun c _ _ => hle c)
  rw [Finset.sum_pair (Ne.symm ha')] at this
  linarith [hneg a ha, hneg a' h']

end LinearMap.BilinForm
