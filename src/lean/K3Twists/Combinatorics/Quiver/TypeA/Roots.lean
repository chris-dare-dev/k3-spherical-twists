/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# The positive roots of a quiver of type `A_n`

A quiver whose underlying graph is the Dynkin diagram `A_n` (vertices `0, …, n - 1`, an edge
between `i` and `i + 1`) has Tits form

  `q(α) = Σ_i α_i² - Σ_i α_i α_{i+1}`,

which is half the quadratic form of the Cartan matrix of type `A_n`, Mathlib's
`CartanMatrix.A n` (`dotProduct_cartanA_mulVec`). Its positive roots, the dimension vectors
`α ∈ ℕⁿ` with `q(α) = 1`, are exactly the intervals `[i, j]`: `α_k = 1` for `i ≤ k ≤ j` and
`0` elsewhere (`titsForm_eq_one_iff`). By Gabriel's theorem (*Unzerlegbare Darstellungen I*,
Manuscripta Math. 6, 1972) they are the dimension vectors of the indecomposable representations.

The proof writes `2q(α)` as a sum of squared differences of the sequence `0, α_0, …, α_{n-1}, 0`
(`two_mul_titsForm`). A sum of squares of integers equal to `2` has exactly two terms `±1`; as the
sequence is nonnegative and starts and ends at `0`, it steps up once and down once.

## Main results

* `dotProduct_cartanA_mulVec`: `αᵀ A_n α = 2 q(α)`;
* `two_mul_titsForm`: `2 q(α) = Σ_{k ≤ n} (a_{k+1} - a_k)²` for `a = (0, α_0, …, α_{n-1}, 0)`;
* `titsForm_eq_one_iff`: the positive roots of `A_n` are the intervals.
-/

open Finset Matrix

namespace Quiver.TypeA

variable {n : ℕ}

/-- The Tits form `q(α) = Σ_i α_i² - Σ_i α_i α_{i+1}` of a quiver of type `A_n`. -/
def titsForm (α : Fin n → ℤ) : ℤ :=
  (∑ i, α i ^ 2) - ∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = i + 1 then α i * α j else 0

/-- The sequence `0, α_0, …, α_{n-1}, 0, 0, …`: `pad α (k + 1) = α_k` for `k < n`. -/
def pad (α : Fin n → ℤ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => if h : k < n then α ⟨k, h⟩ else 0

@[simp]
theorem pad_zero (α : Fin n → ℤ) : pad α 0 = 0 := rfl

theorem pad_succ (α : Fin n → ℤ) (i : Fin n) : pad α (i + 1) = α i := by
  simp [pad, i.2]

theorem pad_eq_zero_of_le (α : Fin n → ℤ) {k : ℕ} (hk : n + 1 ≤ k) : pad α k = 0 := by
  cases k with
  | zero => omega
  | succ k => simp [pad, show ¬k < n by omega]

theorem pad_nonneg {α : Fin n → ℤ} (hα : ∀ i, 0 ≤ α i) (k : ℕ) : 0 ≤ pad α k := by
  cases k with
  | zero => simp
  | succ k =>
    show 0 ≤ if h : k < n then α ⟨k, h⟩ else 0
    split_ifs
    · exact hα _
    · exact le_rfl

/-- The edge sum at a vertex `i`: `Σ_j [j = i + 1] α_i α_j = a_{i+1} a_{i+2}`. -/
theorem sum_edge (α : Fin n → ℤ) (i : Fin n) :
    (∑ j : Fin n, if (j : ℕ) = i + 1 then α i * α j else 0) =
      pad α (i + 1) * pad α (i + 2) := by
  rw [pad_succ]
  by_cases h : (i : ℕ) + 1 < n
  · rw [Finset.sum_eq_single ⟨i + 1, h⟩]
    · simp [pad, h]
    · intro j _ hj
      rw [ite_eq_right_iff]
      intro h'
      exact (hj (Fin.ext h')).elim
    · simp
  · rw [Finset.sum_eq_zero, pad_eq_zero_of_le α (by omega), mul_zero]
    intro j _
    rw [ite_eq_right_iff]
    intro h'
    have := j.2
    omega

/-- **The Tits form as a sum of squared differences.** -/
theorem two_mul_titsForm (α : Fin n → ℤ) :
    2 * titsForm α = ∑ k ∈ range (n + 1), (pad α (k + 1) - pad α k) ^ 2 := by
  have h1 : ∑ i : Fin n, α i ^ 2 = ∑ k ∈ range n, pad α (k + 1) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => pad α (k + 1) ^ 2)]
    simp [pad_succ]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, (if (j : ℕ) = i + 1 then α i * α j else 0) =
      ∑ k ∈ range n, pad α (k + 1) * pad α (k + 2) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => pad α (k + 1) * pad α (k + 2))]
    simp [sum_edge]
  have e1 : ∑ k ∈ range (n + 1), pad α (k + 1) ^ 2 = ∑ k ∈ range n, pad α (k + 1) ^ 2 := by
    rw [sum_range_succ, pad_eq_zero_of_le α le_rfl]
    simp
  have e2 : ∑ k ∈ range (n + 1), pad α k ^ 2 = ∑ k ∈ range n, pad α (k + 1) ^ 2 := by
    rw [sum_range_succ']
    simp
  have e3 : ∑ k ∈ range (n + 1), pad α k * pad α (k + 1) =
      ∑ k ∈ range n, pad α (k + 1) * pad α (k + 2) := by
    rw [sum_range_succ']
    simp
  have expand : ∑ k ∈ range (n + 1), (pad α (k + 1) - pad α k) ^ 2 =
      ∑ k ∈ range (n + 1), pad α (k + 1) ^ 2 + ∑ k ∈ range (n + 1), pad α k ^ 2 -
        2 * ∑ k ∈ range (n + 1), pad α k * pad α (k + 1) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [expand, e1, e2, e3, titsForm, h1, h2]
  ring

/-- **The Tits form is half the Cartan form**: `αᵀ A_n α = 2 q(α)` for Mathlib's Cartan matrix
`CartanMatrix.A n` of the Dynkin diagram `A_n`. -/
theorem dotProduct_cartanA_mulVec (α : Fin n → ℤ) :
    α ⬝ᵥ (CartanMatrix.A n *ᵥ α) = 2 * titsForm α := by
  have key : ∀ i j : Fin n, α i * (CartanMatrix.A n i j * α j) =
      (if i = j then 2 * α i ^ 2 else 0) - (if (j : ℕ) = i + 1 then α i * α j else 0) -
        (if (i : ℕ) = j + 1 then α j * α i else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [CartanMatrix.A]
      ring
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp only [CartanMatrix.A, Matrix.of_apply, hij, ↓reduceIte]
      split_ifs <;> first | (exfalso; omega) | ring
  have hswap : (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) = y + 1 then α y * α x else 0) =
      ∑ x : Fin n, ∑ y : Fin n, if (y : ℕ) = x + 1 then α x * α y else 0 :=
    Finset.sum_comm
  simp only [dotProduct, mulVec, mul_sum, key, sum_sub_distrib, sum_ite_eq, mem_univ,
    ↓reduceIte]
  rw [hswap, titsForm, mul_sub, mul_sum]
  ring

/-- The interval root `[i, j]`: `1` at the vertices `i, i + 1, …, j` and `0` elsewhere. -/
def intervalRoot (i j : Fin n) : Fin n → ℕ := fun k => if i ≤ k ∧ k ≤ j then 1 else 0

/-- **The positive roots of `A_n` are the intervals.** A dimension vector `α ∈ ℕⁿ` has
`q(α) = 1` exactly when it is an interval root `[i, j]`, `i ≤ j`. -/
theorem titsForm_eq_one_iff (α : Fin n → ℕ) :
    titsForm (fun k => (α k : ℤ)) = 1 ↔ ∃ i j, i ≤ j ∧ α = intervalRoot i j := by
  set a : Fin n → ℤ := fun k => (α k : ℤ) with ha
  set P := pad a with hP
  have hsq := two_mul_titsForm a
  rw [← hP] at hsq
  set d : ℕ → ℤ := fun k => P (k + 1) - P k with hd
  constructor
  · intro h
    rw [h] at hsq
    -- every difference is `-1`, `0` or `1`
    have hbound : ∀ k ∈ range (n + 1), -1 ≤ d k ∧ d k ≤ 1 := by
      intro k hk
      have := single_le_sum (f := fun k => (P (k + 1) - P k) ^ 2)
        (fun k _ => sq_nonneg _) hk
      show -1 ≤ P (k + 1) - P k ∧ P (k + 1) - P k ≤ 1
      constructor <;> nlinarith
    -- so the sum of squares counts the nonzero differences
    set s := (range (n + 1)).filter fun k => d k ≠ 0 with hs
    have hcard : s.card = 2 := by
      have : ∑ k ∈ range (n + 1), (P (k + 1) - P k) ^ 2 =
          ∑ k ∈ range (n + 1), if d k ≠ 0 then (1 : ℤ) else 0 := by
        refine sum_congr rfl fun k hk => ?_
        obtain ⟨h1, h2⟩ := hbound k hk
        have : d k = -1 ∨ d k = 0 ∨ d k = 1 := by omega
        rcases this with h | h | h <;> simp [hd] at h ⊢ <;> rw [h] <;> norm_num
      rw [this, sum_boole] at hsq
      have : ((s.card : ℕ) : ℤ) = 2 := by rw [hs]; linarith
      exact_mod_cast this
    obtain ⟨x, y, hxy, hsxy⟩ := card_eq_two.1 hcard
    -- the sequence is the sum of its differences
    have htel : ∀ k, k ≤ n + 1 → P k = ∑ j ∈ s.filter (· < k), d j := by
      intro k hk
      have h1 : P k = ∑ j ∈ range k, d j := by
        rw [hd, sum_range_sub (fun j => P j) k]
        simp [hP]
      rw [h1, ← sum_filter_ne_zero]
      congr 1
      ext j
      simp only [mem_filter, mem_range, hs]
      constructor
      · rintro ⟨hjk, hdj⟩
        exact ⟨⟨by omega, hdj⟩, hjk⟩
      · rintro ⟨⟨_, hdj⟩, hjk⟩
        exact ⟨hjk, hdj⟩
    have hPnn : ∀ k, 0 ≤ P k := pad_nonneg fun i => by simp [ha]
    have hxs : x ∈ s := by rw [hsxy]; simp
    have hys : y ∈ s := by rw [hsxy]; simp
    have hxn : x ≤ n := by have := (mem_filter.1 hxs).1; simp at this; omega
    have hyn : y ≤ n := by have := (mem_filter.1 hys).1; simp at this; omega
    have hdx := (mem_filter.1 hxs).2
    have hdy := (mem_filter.1 hys).2
    -- without loss of generality `x < y`
    wlog hlt : x < y generalizing x y
    · exact this y x hxy.symm (by rw [hsxy, pair_comm]) hys hxs hyn hxn hdy hdx
        (by omega)
    have hfilter : ∀ k, s.filter (· < k) =
        (if x < k then {x} else ∅) ∪ (if y < k then {y} else ∅) := by
      intro k
      ext j
      rw [hsxy]
      simp only [mem_filter, mem_insert, mem_singleton, mem_union]
      split_ifs <;> simp <;> omega
    have hval : ∀ k, k ≤ n + 1 →
        P k = (if x < k then d x else 0) + (if y < k then d y else 0) := by
      intro k hk
      rw [htel k hk, hfilter k]
      split_ifs with h1 h2 h2
      · rw [sum_union (by simp [hxy])]
        simp
      · simp
      · simp
      · simp
    -- the step up at `x` is `1` and the step down at `y` is `-1`
    have hend := hval (n + 1) le_rfl
    rw [show P (n + 1) = 0 from pad_eq_zero_of_le a le_rfl] at hend
    simp only [show x < n + 1 by omega, show y < n + 1 by omega, ↓reduceIte] at hend
    have hup := hval (x + 1) (by omega)
    simp only [show x < x + 1 by omega, show ¬y < x + 1 by omega, ↓reduceIte, add_zero] at hup
    have hx1 : d x = 1 := by
      have := hPnn (x + 1)
      have := (hbound x (by simp; omega))
      omega
    have hy1 : d y = -1 := by omega
    refine ⟨⟨x, by omega⟩, ⟨y - 1, by omega⟩, by simp only [Fin.mk_le_mk]; omega, ?_⟩
    funext k
    have hk := hval (k + 1) (by omega)
    rw [hP, pad_succ] at hk
    simp only [ha] at hk
    rw [hx1, hy1] at hk
    simp only [intervalRoot, Fin.le_def]
    split_ifs at hk ⊢ <;> omega
  · rintro ⟨i, j, hij, rfl⟩
    have hPk : ∀ k, P k = if (i : ℕ) + 1 ≤ k ∧ k ≤ j + 1 then 1 else 0 := by
      intro k
      cases k with
      | zero => simp [hP]
      | succ k =>
        by_cases hk : k < n
        · have : P (k + 1) = a ⟨k, hk⟩ := pad_succ a ⟨k, hk⟩
          rw [this]
          simp only [ha, intervalRoot, Fin.le_def]
          split_ifs <;> first | (exfalso; omega) | norm_num
        · rw [hP, pad_eq_zero_of_le a (by omega), eq_comm, ite_eq_right_iff]
          intro h'
          have := j.2
          omega
    have hle : (j : ℕ) + 1 ≤ n := j.2
    have hsum : ∑ k ∈ range (n + 1), (P (k + 1) - P k) ^ 2 = 2 := by
      have hi := i.2
      rw [sum_eq_add_of_mem (i : ℕ) ((j : ℕ) + 1) (mem_range.2 (by omega)) (mem_range.2 (by omega))
        (by simp only [Fin.le_def] at hij; omega)]
      · simp only [hPk]
        split_ifs <;> first | (exfalso; omega) | norm_num
      · intro k _ hk
        simp only [hPk]
        split_ifs <;> first | (exfalso; omega) | simp
    rw [hsum] at hsq
    linarith

end Quiver.TypeA
