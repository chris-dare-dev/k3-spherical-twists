/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.JointSpectralRadius
import K3Twists.Combinatorics.Quiver.Kronecker.RealRoots

/-!
# Examples of matrix growth rates

Special cases of the rate formulas of `K3Twists.Analysis.Matrix`, kept as examples that must
keep compiling:

* the golden ratio as the joint spectral radius of `[[1, 1], [0, 1]]` and `[[1, 0], [1, 1]]`;
* the rate `3 + 2√2` of two squared twists with `μ = 1`;
* the powers of the Kronecker matrix `[[g, -1], [1, 0]]` through the sequence
  `Quiver.Kronecker.u g` of the real roots of the `g`-Kronecker quiver.
-/

open Matrix
open scoped Matrix.Norms.Operator

/-- The golden ratio is the joint spectral radius of the two elementary unipotent matrices. -/
example : jointSpectralRadius ![!![1, 1; 0, 1], !![1, 0; 1, 1]] = (1 + √5) / 2 := by
  have h := jointSpectralRadius_unipotent_pair (s := 1) le_rfl
  norm_num at h
  exact h

/-- Two squared twists with `μ = 1` grow at the rate `3 + 2√2`. -/
example : gelfandRadius (thurstonA 2 1 * thurstonB 2 1) = 3 + 2 * √2 := by
  rw [gelfandRadius_thurston_two_two one_pos]
  norm_num

/-- The Kronecker matrix `K = [[g, -1], [1, 0]]` has `Kᵐ = u_m K - u_{m-1}`, where
`u₀ = 0`, `u₁ = 1`, `u_{m+1} = g u_m - u_{m-1}`. -/
example (g : ℤ) (m : ℕ) :
    !![g, -1; 1, 0] ^ m = Quiver.Kronecker.u g m • !![g, -1; 1, 0] -
      Quiver.Kronecker.u g (m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  have h := pow_eq_S_eval_trace_smul_sub !![g, -1; 1, 0] (by simp [det_fin_two]) m
  rw [h, trace_fin_two]
  simp only [Quiver.Kronecker.u, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, add_zero]
  rw [sub_sub, one_add_one_eq_two]
