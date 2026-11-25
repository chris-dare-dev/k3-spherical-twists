/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Powers of an element with a quadratic relation

Mathlib's rescaled Chebyshev polynomials `S_n` (`Polynomial.Chebyshev.S`) satisfy
`S_{n+1} = X S_n - S_{n-1}` with `S_0 = 1`, `S_{-1} = 0`. They compute the powers of any element
`x` of an algebra with `x² = t x - 1`, and in particular the powers of a `2 × 2` matrix of
determinant one, whose trace plays the role of `t`.

## Main results

* `Polynomial.Chebyshev.pow_eq_S_eval_smul_sub`: if `x² = t x - 1` in an `R`-algebra, then
  `xⁿ = S_{n-1}(t) x - S_{n-2}(t)` for every `n : ℕ`.
* `Polynomial.Chebyshev.S_eval_add_inv_mul_sub_inv`: the closed form
  `S_n(l + l⁻¹) (l - l⁻¹) = l^{n+1} - l^{-(n+1)}` in a field.
* `Matrix.sq_eq_trace_smul_sub_det_smul`: Cayley–Hamilton for `2 × 2` matrices,
  `M² = tr(M) M - det(M)`.
* `Matrix.pow_eq_S_eval_trace_smul_sub`: for `det M = 1`,
  `Mⁿ = S_{n-1}(tr M) M - S_{n-2}(tr M)`.

The Kronecker sequence `Quiver.Kronecker.u g m` of the real roots of the `g`-Kronecker quiver is
`S_{m-1}(g)` by definition, so these formulas apply to it at `t = g`.
-/

namespace Polynomial.Chebyshev

/-- **Powers under a quadratic relation.** If `x² = t x - 1` in an `R`-algebra, then
`xⁿ = S_{n-1}(t) x - S_{n-2}(t)` for every `n`, with Mathlib's rescaled Chebyshev polynomials
`S` (so `S_{-1} = 0` and `S_{-2} = -1`). -/
theorem pow_eq_S_eval_smul_sub {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A)
    (t : R) (hx : x ^ 2 = t • x - 1) (n : ℕ) :
    x ^ n = (S R ((n : ℤ) - 1)).eval t • x - (S R ((n : ℤ) - 2)).eval t • (1 : A) := by
  induction n with
  | zero => simp [S_neg_one, S_neg_two]
  | succ n ih =>
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← sq, hx]
    have e1 : ((n + 1 : ℕ) : ℤ) - 1 = n := by push_cast; ring
    have e2 : ((n + 1 : ℕ) : ℤ) - 2 = n - 1 := by push_cast; ring
    rw [e1, e2, S_eq R (n : ℤ)]
    simp only [eval_sub, eval_mul, eval_X]
    module

/-- **Closed form at `l + l⁻¹`.** In a field, `S_n(l + l⁻¹) (l - l⁻¹) = l^{n+1} - l^{-(n+1)}`
for `l ≠ 0`. -/
theorem S_eval_add_inv_mul_sub_inv {K : Type*} [Field K] {l : K} (hl : l ≠ 0) (n : ℕ) :
    (S K n).eval (l + l⁻¹) * (l - l⁻¹) = l ^ (n + 1) - l⁻¹ ^ (n + 1) := by
  have hll : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  have pair : ∀ n : ℕ,
      (S K n).eval (l + l⁻¹) * (l - l⁻¹) = l ^ (n + 1) - l⁻¹ ^ (n + 1) ∧
      (S K (n + 1 : ℕ)).eval (l + l⁻¹) * (l - l⁻¹) = l ^ (n + 2) - l⁻¹ ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp, ?_⟩
      simp only [zero_add, Nat.cast_one, S_one, eval_X]
      ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      rw [e, S_add_two]
      simp only [eval_sub, eval_mul, eval_X]
      have h0 := ih.1
      have h1 := ih.2
      push_cast at h1
      linear_combination (l + l⁻¹) * h1 - h0 + (l ^ (n + 1) - l⁻¹ ^ (n + 1)) * hll
  exact (pair n).1

end Polynomial.Chebyshev

namespace Matrix

open Polynomial

/-- **Cayley–Hamilton for `2 × 2` matrices**: `M² = tr(M) M - det(M)`. -/
theorem sq_eq_trace_smul_sub_det_smul {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring

/-- **Powers of a `2 × 2` matrix of determinant one**: `Mⁿ = S_{n-1}(tr M) M - S_{n-2}(tr M)`. -/
theorem pow_eq_S_eval_trace_smul_sub {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (hdet : M.det = 1) (n : ℕ) :
    M ^ n = (Chebyshev.S R ((n : ℤ) - 1)).eval M.trace • M -
      (Chebyshev.S R ((n : ℤ) - 2)).eval M.trace • (1 : Matrix (Fin 2) (Fin 2) R) :=
  Chebyshev.pow_eq_S_eval_smul_sub M M.trace
    (by rw [sq_eq_trace_smul_sub_det_smul, hdet, one_smul]) n

end Matrix
