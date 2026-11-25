/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group


/-!
# Fork words are conjugate to a two-letter period

Let `H` and `L₁, L₂, …` be elements of a group such that the `L_i` commute with each other and
each `L_i` satisfies the braid relation `H L_i H = L_i H L_i` with `H`. The *fork words* are the
iterated commutators

  `W₀ = H`,  `W_i = ⁅W_{i-1}, L_i⁆ = W_{i-1} L_i W_{i-1}⁻¹ L_i⁻¹`.

Each `W_i` (`i ≥ 1`) is conjugate to the two-letter word `H L_i⁻¹`, by
`D_i = L₁⁻¹ L₂⁻¹ ⋯ L_i⁻¹`. For spherical twists `H = T_A` and `L_i = T_{B_i}` with `A` meeting each
`B_i` once and the `B_i` mutually orthogonal (a fork of `A₂` configurations), the twists satisfy
these relations (Seidel–Thomas, arXiv:math/0001043, Theorem 1.3), so every fork word is conjugate
to the `A₂` period `T_A T_{B_i}⁻¹`; growth rates are conjugacy invariants, so all fork words grow
like that period.

## Main definitions

* `forkWord H L i`: the iterated commutator `W_i`;
* `forkConj L i`: the conjugator `D_i = L₁⁻¹ ⋯ L_i⁻¹` (with `D₀ = 1`).

## Main results

* `forkWord_succ_eq_conj`: `W_{i+1} = D_{i+1} (H L_{i+1}⁻¹) D_{i+1}⁻¹`.
-/

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The fork words: `W₀ = H` and `W_{i+1} = ⁅W_i, L_{i+1}⁆`. -/
def forkWord (H : G) (L : ℕ → G) : ℕ → G
  | 0 => H
  | i + 1 => ⁅forkWord H L i, L (i + 1)⁆

/-- The conjugators `D₀ = 1` and `D_{i+1} = D_i L_{i+1}⁻¹`. -/
def forkConj (L : ℕ → G) : ℕ → G
  | 0 => 1
  | i + 1 => forkConj L i * (L (i + 1))⁻¹

@[simp] lemma forkWord_zero (H : G) (L : ℕ → G) : forkWord H L 0 = H := rfl

lemma forkWord_succ (H : G) (L : ℕ → G) (i : ℕ) :
    forkWord H L (i + 1) = ⁅forkWord H L i, L (i + 1)⁆ := rfl

@[simp] lemma forkConj_zero (L : ℕ → G) : forkConj L 0 = 1 := rfl

lemma forkConj_succ (L : ℕ → G) (i : ℕ) : forkConj L (i + 1) = forkConj L i * (L (i + 1))⁻¹ :=
  rfl

/-- If `x` commutes with every `L_j`, it commutes with every conjugator `D_i`. -/
lemma commute_forkConj {L : ℕ → G} {x : G} (hx : ∀ j, Commute x (L j)) (i : ℕ) :
    Commute x (forkConj L i) := by
  induction i with
  | zero => exact Commute.one_right x
  | succ i ih => exact ih.mul_right (hx (i + 1)).inv_right

/-- **Fork words are conjugate to a two-letter period.** If the `L_i` commute pairwise and each
satisfies the braid relation `H L_i H = L_i H L_i`, then
`W_{i+1} = D_{i+1} (H L_{i+1}⁻¹) D_{i+1}⁻¹`, that is `W_{i+1} = D_i L_{i+1}⁻¹ H D_i⁻¹`. -/
theorem forkWord_succ_eq_conj {H : G} {L : ℕ → G} (hL : ∀ i j, Commute (L i) (L j))
    (hbraid : ∀ i, H * L i * H = L i * H * L i) (i : ℕ) :
    forkWord H L (i + 1) =
      forkConj L (i + 1) * (H * (L (i + 1))⁻¹) * (forkConj L (i + 1))⁻¹ := by
  -- the braid relation as `H L H⁻¹ = L⁻¹ H L`
  have hconj : ∀ j, H * L j * H⁻¹ = (L j)⁻¹ * H * L j := fun j => by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, mul_assoc, ← mul_assoc H, hbraid j]; group
  -- the invariant `W_{i+1} = D_i L_{i+1}⁻¹ H D_i⁻¹`
  have key : ∀ i, forkWord H L (i + 1) = forkConj L i * (L (i + 1))⁻¹ * H * (forkConj L i)⁻¹ := by
    intro i
    induction i with
    | zero =>
      rw [forkWord_succ, forkWord_zero, commutatorElement_def, forkConj_zero, hconj]; group
    | succ i ih =>
      set D := forkConj L i
      have hD : Commute (L (i + 2)) D := commute_forkConj (hL (i + 2)) i
      have hD' : Commute (L (i + 1)) (L (i + 2)) := hL _ _
      rw [forkWord_succ, ih, commutatorElement_def, forkConj_succ]
      -- `W_{i+1} L_{i+2} W_{i+1}⁻¹ L_{i+2}⁻¹` with `W_{i+1} = D L_{i+1}⁻¹ H D⁻¹`
      calc D * (L (i + 1))⁻¹ * H * D⁻¹ * L (i + 1 + 1) *
            (D * (L (i + 1))⁻¹ * H * D⁻¹)⁻¹ * (L (i + 1 + 1))⁻¹
          = D * (L (i + 1))⁻¹ * (H * (D⁻¹ * L (i + 2) * D) * H⁻¹) * L (i + 1) * D⁻¹ *
              (L (i + 2))⁻¹ := by group
        _ = D * (L (i + 1))⁻¹ * (H * L (i + 2) * H⁻¹) * L (i + 1) * D⁻¹ * (L (i + 2))⁻¹ := by
            rw [show D⁻¹ * L (i + 2) * D = L (i + 2) by
              rw [mul_assoc, hD.eq, ← mul_assoc, inv_mul_cancel, one_mul]]
        _ = D * (L (i + 1))⁻¹ * ((L (i + 2))⁻¹ * H * L (i + 2)) * L (i + 1) * D⁻¹ *
              (L (i + 2))⁻¹ := by rw [hconj]
        _ = D * (L (i + 1))⁻¹ * (L (i + 2))⁻¹ * H * (D * (L (i + 1))⁻¹)⁻¹ := by
            have e1 : L (i + 2) * L (i + 1) = L (i + 1) * L (i + 2) := hD'.eq.symm
            have e2 : (L (i + 2))⁻¹ * D⁻¹ = D⁻¹ * (L (i + 2))⁻¹ := (hD.inv_right.inv_left).eq
            calc D * (L (i + 1))⁻¹ * ((L (i + 2))⁻¹ * H * L (i + 2)) * L (i + 1) * D⁻¹ *
                  (L (i + 2))⁻¹
                = D * (L (i + 1))⁻¹ * (L (i + 2))⁻¹ * H * (L (i + 2) * L (i + 1)) *
                    (D⁻¹ * (L (i + 2))⁻¹) := by group
              _ = D * (L (i + 1))⁻¹ * (L (i + 2))⁻¹ * H * (L (i + 1) * L (i + 2)) *
                    ((L (i + 2))⁻¹ * D⁻¹) := by rw [e1, e2]
              _ = _ := by group
  rw [key i, forkConj_succ]
  group
