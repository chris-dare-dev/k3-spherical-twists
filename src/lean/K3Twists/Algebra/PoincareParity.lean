/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.GCD

/-!
# The parity of a Poincaré polynomial

For a finitely supported family of dimensions `f : ℤ →₀ ℕ` (the graded dimensions of a graded
vector space) the Poincaré polynomial `P(t) = Σ_j f(j) tʲ` has `P(1) = Σ_j f(j)`
(`Finsupp.poincareOne`) and `P(-1) = Σ_j (-1)ʲ f(j)` (`Finsupp.poincareNegOne`). Then

  `|P(-1)| ≤ P(1)` and `P(-1) ≡ P(1) mod 2`

(`Finsupp.abs_poincareNegOne_le`, `Finsupp.poincareNegOne_modEq`): total dimension bounds the
Euler characteristic, with the same parity. This is the input of the fibre-functor bound
`μ_F ≥ |⟨w_F, v⟩|` (`CategoryTheory/MassProfile/FibreFunctor.lean`).
-/

open Finset

namespace Finsupp

/-- `P(1) = Σ_j f j`, the total dimension of a graded space with dimensions `f`. -/
def poincareOne (f : ℤ →₀ ℕ) : ℕ := f.sum fun _ n ↦ n

/-- `P(-1) = Σ_j (-1)^j f j`, the Euler characteristic of a graded space with dimensions `f`. -/
def poincareNegOne (f : ℤ →₀ ℕ) : ℤ := f.sum fun j n ↦ (j.negOnePow : ℤ) * n

lemma poincareOne_eq (f : ℤ →₀ ℕ) : (f.poincareOne : ℤ) = ∑ j ∈ f.support, (f j : ℤ) := by
  simp [poincareOne, Finsupp.sum]

@[simp]
lemma poincareOne_add (f g : ℤ →₀ ℕ) : (f + g).poincareOne = f.poincareOne + g.poincareOne :=
  Finsupp.sum_add_index' (fun _ ↦ rfl) fun _ _ _ ↦ rfl

@[simp]
lemma poincareOne_single (j : ℤ) (n : ℕ) : (Finsupp.single j n).poincareOne = n :=
  Finsupp.sum_single_index rfl

@[simp]
lemma poincareNegOne_add (f g : ℤ →₀ ℕ) :
    (f + g).poincareNegOne = f.poincareNegOne + g.poincareNegOne :=
  Finsupp.sum_add_index' (fun _ ↦ by simp) fun _ _ _ ↦ by push_cast; exact mul_add _ _ _

@[simp]
lemma poincareNegOne_single (j : ℤ) (n : ℕ) :
    (Finsupp.single j n).poincareNegOne = (j.negOnePow : ℤ) * n :=
  Finsupp.sum_single_index (by simp)

/-- `|P(-1)| ≤ P(1)`. -/
theorem abs_poincareNegOne_le (f : ℤ →₀ ℕ) : |f.poincareNegOne| ≤ f.poincareOne := by
  rw [poincareOne_eq, poincareNegOne, Finsupp.sum]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ ↦ ?_))
  rw [abs_mul, Int.abs_negOnePow, one_mul, Nat.abs_cast]

/-- `P(-1) ≡ P(1) mod 2`. -/
theorem poincareNegOne_modEq (f : ℤ →₀ ℕ) : f.poincareNegOne ≡ f.poincareOne [ZMOD 2] := by
  rw [poincareOne_eq, poincareNegOne, Finsupp.sum, Int.modEq_iff_dvd, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j _ ↦ ?_
  rcases Int.even_or_odd j with h | h
  · simp [Int.negOnePow_even _ h]
  · simp only [Int.negOnePow_odd _ h, Units.val_neg, Units.val_one, neg_mul, one_mul,
      sub_neg_eq_add]
    exact ⟨f j, (two_mul _).symm⟩

end Finsupp
