/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Polynomial envelopes of powers

If an element `a` of a normed algebra is killed by `∏_{μ ∈ s} (X - μ)` and every `μ ∈ s` has
`‖μ‖ ≤ ρ` with `ρ > 0`, then `‖a ^ k‖ ≤ C (1 + k) ^ (|s| - 1) ρ ^ k` for one constant `C`
(`exists_norm_pow_le_of_aeval_eq_zero`). For a complex `r × r` matrix whose eigenvalues all have
modulus at most `ρ`, the characteristic polynomial gives
`‖M ^ k‖ ≤ C (1 + k) ^ (r - 1) ρ ^ k` (`Matrix.exists_norm_pow_le_of_forall_mem_spectrum`).

This is the envelope one usually reads off a unitary Schur form `D + N`, expanding `(D + N)^k`
and using that a product with `r` factors `N` vanishes. Mathlib has no Schur form; the proof
here is an induction on the roots of an annihilating polynomial, through
`a x = μ x + (a - μ) x`, with Cayley–Hamilton (`Matrix.aeval_self_charpoly`) for matrices.

The bound holds for every `ρ > 0`, in particular for `ρ ≥ 1`
(`Matrix.exists_norm_pow_le_of_forall_mem_spectrum_of_one_le`), and it **fails at `ρ = 0`**: the
nilpotent `[[0, 1], [0, 0]]` has every eigenvalue `0` but is not `0`
(`Matrix.not_exists_norm_pow_le_of_spectrum_zero`). Matrix norms are the `ℓ∞` operator norms of
`Matrix.Norms.Operator`.
-/

open Polynomial

section NormedAlgebra

variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The polynomial envelope of powers from an annihilating polynomial: if
`∏_{μ ∈ s} (a - μ)` kills `x` and every `μ ∈ s` has `‖μ‖ ≤ ρ`, `0 < ρ`, then
`‖a ^ k * x‖ ≤ C (1 + k) ^ (|s| - 1) ρ ^ k ‖x‖` for one constant `C`. -/
theorem exists_norm_pow_mul_le_of_aeval_mul_eq_zero (a : A) (s : Multiset 𝕜) {ρ : ℝ}
    (hρ : 0 < ρ) (hs : ∀ μ ∈ s, ‖μ‖ ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A, aeval a (s.map fun μ ↦ X - Polynomial.C μ).prod * x = 0 →
      ∀ k : ℕ, ‖a ^ k * x‖ ≤ C * (1 + k) ^ (Multiset.card s - 1) * ρ ^ k * ‖x‖ := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨0, le_rfl, fun x hx k ↦ ?_⟩
    simp only [Multiset.map_zero, Multiset.prod_zero, map_one, one_mul] at hx
    simp [hx]
  | cons μ t ih =>
    obtain ⟨C, hC, hCt⟩ := ih fun ν hν ↦ hs ν (Multiset.mem_cons_of_mem hν)
    have hμ : ‖μ‖ ≤ ρ := hs μ (Multiset.mem_cons_self _ _)
    set Q := (t.map fun μ ↦ X - Polynomial.C μ).prod
    -- the step: `a x = μ x + y` with `y = (a - μ) x` killed by `Q(a)`
    set D := C / ρ * ‖a - algebraMap 𝕜 A μ‖
    refine ⟨1 + D, by positivity, fun x hx k ↦ ?_⟩
    set y := (a - algebraMap 𝕜 A μ) * x with hy_def
    have hy : aeval a Q * y = 0 := by
      calc aeval a Q * y = aeval a (Q * (X - Polynomial.C μ)) * x := by
            rw [hy_def, ← mul_assoc, map_mul]
            simp
        _ = aeval a ((μ ::ₘ t).map fun μ ↦ X - Polynomial.C μ).prod * x := by
            rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
        _ = 0 := hx
    have hax : a * x = μ • x + y := by
      rw [hy_def, sub_mul, Algebra.smul_def]
      abel
    have hyk : ∀ k : ℕ, ‖a ^ k * y‖ ≤ C * (1 + k) ^ (Multiset.card t - 1) * ρ ^ k * ‖y‖ :=
      hCt y hy
    have hyn : ‖y‖ ≤ ‖a - algebraMap 𝕜 A μ‖ * ‖x‖ := norm_mul_le _ _
    -- induction on `k`
    have key : ∀ k : ℕ, ‖a ^ k * x‖ ≤
        ρ ^ k * (‖x‖ + C / ρ * k * (1 + k) ^ (Multiset.card t - 1) * ‖y‖) := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        have h1 : a ^ (k + 1) * x = μ • (a ^ k * x) + a ^ k * y := by
          rw [pow_succ, mul_assoc, hax, mul_add, mul_smul_comm]
        rw [h1]
        have hmono : (1 + (k : ℝ)) ^ (Multiset.card t - 1) ≤
            (1 + ((k : ℝ) + 1)) ^ (Multiset.card t - 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        have h3 : C / ρ * ((k : ℝ) + 1) * (1 + k) ^ (Multiset.card t - 1) * ‖y‖ ≤
            C / ρ * ((k : ℝ) + 1) * (1 + ((k : ℝ) + 1)) ^ (Multiset.card t - 1) * ‖y‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (by positivity))
            (norm_nonneg _)
        push_cast
        calc ‖μ • (a ^ k * x) + a ^ k * y‖ ≤ ‖μ‖ * ‖a ^ k * x‖ + ‖a ^ k * y‖ :=
              (norm_add_le _ _).trans (by rw [norm_smul])
          _ ≤ ρ * (ρ ^ k * (‖x‖ + C / ρ * k * (1 + k) ^ (Multiset.card t - 1) * ‖y‖)) +
                C * (1 + k) ^ (Multiset.card t - 1) * ρ ^ k * ‖y‖ :=
              add_le_add (mul_le_mul hμ ihk (norm_nonneg _) hρ.le) (hyk k)
          _ = ρ ^ (k + 1) * (‖x‖ + C / ρ * (k + 1) * (1 + k) ^ (Multiset.card t - 1) * ‖y‖) := by
              field_simp
              ring
          _ ≤ ρ ^ (k + 1) * (‖x‖ + C / ρ * ((k : ℝ) + 1) *
                (1 + ((k : ℝ) + 1)) ^ (Multiset.card t - 1) * ‖y‖) :=
              mul_le_mul_of_nonneg_left (add_le_add le_rfl h3) (by positivity)
    -- the exponent
    rcases Multiset.empty_or_exists_mem t with rfl | ⟨ν, hν⟩
    · -- `Q = 1`, so `y = 0`
      have hy0 : y = 0 := by simpa [Q] using hy
      have := key k
      simp only [hy0, norm_zero, mul_zero, add_zero] at this
      have hD : 0 ≤ D := by positivity
      calc ‖a ^ k * x‖ ≤ ρ ^ k * ‖x‖ := this
        _ ≤ (1 + D) * (ρ ^ k * ‖x‖) := le_mul_of_one_le_left (by positivity) (by linarith)
        _ = (1 + D) * (1 + k) ^ (Multiset.card (μ ::ₘ 0) - 1) * ρ ^ k * ‖x‖ := by
          simp only [Multiset.card_cons, Multiset.card_zero, zero_add, tsub_self, pow_zero,
            mul_one]
          ring
    · have hcard : Multiset.card (μ ::ₘ t) - 1 = (Multiset.card t - 1) + 1 := by
        have := Multiset.card_pos_iff_exists_mem.2 ⟨ν, hν⟩
        rw [Multiset.card_cons]
        omega
      rw [hcard]
      calc ‖a ^ k * x‖
          ≤ ρ ^ k * (‖x‖ + C / ρ * k * (1 + k) ^ (Multiset.card t - 1) * ‖y‖) := key k
        _ ≤ ρ ^ k * (‖x‖ + C / ρ * k * (1 + k) ^ (Multiset.card t - 1) *
              (‖a - algebraMap 𝕜 A μ‖ * ‖x‖)) := by gcongr
        _ = ρ ^ k * ‖x‖ * (1 + D * (k * (1 + k) ^ (Multiset.card t - 1))) := by
              simp only [D]; ring
        _ ≤ ρ ^ k * ‖x‖ * ((1 + D) * (1 + k) ^ (Multiset.card t - 1 + 1)) := by
              gcongr
              have h1 : (1 : ℝ) ≤ (1 + k) ^ (Multiset.card t - 1 + 1) :=
                one_le_pow₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
              have h2 : (k : ℝ) * (1 + k) ^ (Multiset.card t - 1) ≤
                  (1 + k) ^ (Multiset.card t - 1 + 1) := by
                rw [pow_succ, mul_comm]
                gcongr
                linarith
              have : 0 ≤ D := by positivity
              nlinarith
        _ = (1 + D) * (1 + k) ^ (Multiset.card t - 1 + 1) * ρ ^ k * ‖x‖ := by ring

/-- **Polynomial envelope of powers.** If `∏_{μ ∈ s} (a - μ) = 0` with `‖μ‖ ≤ ρ` for every
`μ ∈ s` and `0 < ρ`, then `‖a ^ k‖ ≤ C (1 + k) ^ (|s| - 1) ρ ^ k` for one constant `C`. -/
theorem exists_norm_pow_le_of_aeval_eq_zero (a : A) (s : Multiset 𝕜) {ρ : ℝ} (hρ : 0 < ρ)
    (hs : ∀ μ ∈ s, ‖μ‖ ≤ ρ) (ha : aeval a (s.map fun μ ↦ X - Polynomial.C μ).prod = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖a ^ k‖ ≤ C * (1 + k) ^ (Multiset.card s - 1) * ρ ^ k := by
  obtain ⟨C, hC, h⟩ := exists_norm_pow_mul_le_of_aeval_mul_eq_zero a s hρ hs
  refine ⟨C * ‖(1 : A)‖, by positivity, fun k ↦ ?_⟩
  have := h 1 (by rw [ha, zero_mul]) k
  rw [mul_one] at this
  calc ‖a ^ k‖ ≤ C * (1 + k) ^ (Multiset.card s - 1) * ρ ^ k * ‖(1 : A)‖ := this
    _ = C * ‖(1 : A)‖ * (1 + k) ^ (Multiset.card s - 1) * ρ ^ k := by ring

end NormedAlgebra

namespace Matrix

open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The polynomial envelope of a complex matrix.** If every eigenvalue of `M` has modulus at
most `ρ`, `0 < ρ`, then `‖M ^ k‖ ≤ C (1 + k) ^ (r - 1) ρ ^ k`, `r` the size of `M`. -/
theorem exists_norm_pow_le_of_forall_mem_spectrum (M : Matrix n n ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hM : ∀ μ ∈ spectrum ℂ M, ‖μ‖ ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖M ^ k‖ ≤ C * (1 + k) ^ (Fintype.card n - 1) * ρ ^ k := by
  have hsplit : (M.charpoly.roots.map fun μ ↦ X - Polynomial.C μ).prod = M.charpoly :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic M)
      (splits_iff_card_roots.1 (IsAlgClosed.splits _))
  have hcard : Multiset.card M.charpoly.roots = Fintype.card n := by
    rw [(splits_iff_card_roots.1 (IsAlgClosed.splits M.charpoly)), charpoly_natDegree_eq_dim]
  have := exists_norm_pow_le_of_aeval_eq_zero M M.charpoly.roots hρ
    (fun μ hμ ↦ hM μ (mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hμ)))
    (by rw [hsplit, aeval_self_charpoly])
  rwa [hcard] at this

end Matrix

namespace Matrix

open scoped Matrix.Norms.Operator

/-- At `ρ ≥ 1` the envelope holds with the size of the matrix in the exponent. -/
theorem exists_norm_pow_le_of_forall_mem_spectrum_of_one_le {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n ℂ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hM : ∀ μ ∈ spectrum ℂ M, ‖μ‖ ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖M ^ k‖ ≤ C * (1 + k) ^ (Fintype.card n - 1) * ρ ^ k :=
  exists_norm_pow_le_of_forall_mem_spectrum M (zero_lt_one.trans_le hρ) hM

/-- **The envelope fails at `ρ = 0`**: the nilpotent `[[0, 1], [0, 0]]` has every eigenvalue
`0`, but no bound `‖N ^ k‖ ≤ C (1 + k) 0 ^ k` holds, since `N ≠ 0`. -/
theorem not_exists_norm_pow_le_of_spectrum_zero :
    (∀ μ ∈ spectrum ℂ !![(0 : ℂ), 1; 0, 0], ‖μ‖ ≤ 0) ∧
      ¬ ∃ C : ℝ, ∀ k : ℕ, ‖!![(0 : ℂ), 1; 0, 0] ^ k‖ ≤ C * (1 + k) ^ (2 - 1) * 0 ^ k := by
  refine ⟨fun μ hμ ↦ ?_, fun ⟨C, hC⟩ ↦ ?_⟩
  · rw [mem_spectrum_iff_isRoot_charpoly, charpoly_fin_two] at hμ
    simp [trace_fin_two] at hμ
    simp [hμ]
  · have := hC 1
    simp only [pow_one, Nat.cast_one, mul_zero, norm_le_zero_iff] at this
    have h01 := congrFun (congrFun this 0) 1
    simp at h01

end Matrix
