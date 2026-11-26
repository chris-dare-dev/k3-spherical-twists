/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Convex.ProjectiveCocycle

/-!
# Projective cocycles of two spherical twists: examples

* **The block identity** at sample values: for `g = 1` the block `b = 2` sends `(3, 5)` to
  `(25, 11)`, and `25 - 2 · 11 = 3`; on the explicit formulas over `ℤ`, `b = 4`, `g = 3` send
  `(2, 7)` to `(188, 31)`, and `188 - 6 · 31 = 2`.
* **The block as a product**: `twoTwistBlock 2 1 = U² L² = [[5, 2], [2, 1]]` for
  `U = [[1, 1], [0, 1]]`, `L = [[1, 0], [1, 1]]`, and the count representation sends the block
  word `T₁² T₂⁻²` to it.
* **The cusp ratio** at `g = 1`: `(25, 11)` has `x ≥ 2y` and ratio `14/108 ≥ 1/9`, while `(1, 1)`
  has neither.
* **The moving-start lemma** on `u_k = 2ᵏ`, `d = 2`, `C = 0`: `∑_{k<m} 2ᵏ ≤ 2ᵐ`.
* **A periodic word**: the constant word in the block `b = 2` at `g = 1` has limit ratio
  `1 + √2`, because `(1 + √2, 1)` is a positive eigenvector of `[[5, 2], [2, 1]]` (eigenvalue
  `3 + 2√2`); so the ratios of `P_n (1, 1)` converge to `1 + √2`.

Built by `lake test`.
-/

namespace K3TwistsTest.ProjectiveCocycleExamples

open Matrix Filter Topology

/-! ### The block identity -/

example : twoTwistBlock 2 1 *ᵥ ![3, 5] = ![25, 11] := by
  ext i
  fin_cases i <;> norm_num [twoTwistBlock_mulVec_zero, twoTwistBlock_mulVec_one]

example : (twoTwistBlock 2 1 *ᵥ ![3, 5]) 0 - 2 * 1 * (twoTwistBlock 2 1 *ᵥ ![3, 5]) 1 = 3 := by
  simpa using twoTwistBlock_mulVec_zero_sub 2 1 ![3, 5]

example : (1 + 2 * 4 * 3 ^ 2) * 2 + 2 * 3 * 7 = (188 : ℤ) ∧ 4 * 3 * 2 + 7 = (31 : ℤ) ∧
    (188 : ℤ) - 2 * 3 * 31 = 2 := by
  norm_num

example : (1 + 2 * 4 * 3 ^ 2) * 2 + 2 * 3 * 7 - 2 * 3 * (4 * 3 * 2 + 7) = (2 : ℤ) :=
  twoTwistBlock_identity 4 3 2 7

/-! ### The block as a product -/

example : twoTwistBlock 2 1 = !![5, 2; 2, 1] := by
  norm_num [twoTwistBlock]

example :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 * !![1, 0; 1, 1] ^ 2 = !![5, 2; 2, 1] := by
  norm_num [sq, mul_fin_two]

example : twoTwistBlock 2 1 = !![1, 1; 0, 1] ^ 2 * !![1, 0; 1, 1] ^ 2 := by
  have h := twoTwistBlock_natCast 2 1
  rw [thurstonA, thurstonB, mul_one, Nat.cast_ofNat] at h
  exact h

example : (twistCountRep 1 (twoTwistBlockWord 2) : Matrix (Fin 2) (Fin 2) ℝ) = !![5, 2; 2, 1] := by
  rw [twistCountRep_twoTwistBlockWord]
  norm_num [twoTwistBlock]

/-! ### The cusp ratio -/

example : (2 * 1 - 1) / (3 * (2 * 1 + 1)) ≤ ((25 : ℝ) - 11) / (3 * (25 + 11)) :=
  (two_mul_sub_one_div_le_iff (by norm_num) (by norm_num)).2 (by norm_num)

example : ¬ (2 * 1 - 1) / (3 * (2 * 1 + 1)) ≤ ((1 : ℝ) - 1) / (3 * (1 + 1)) := by
  rw [two_mul_sub_one_div_le_iff (by norm_num) (by norm_num)]
  norm_num

/-! ### The moving-start lemma -/

/-- The moving-start lemma on `u_k = 2ᵏ` with `d = 2` and `C = 0`. -/
theorem sum_range_two_pow_le (m : ℕ) : ∑ k ∈ Finset.range m, (2 : ℝ) ^ k ≤ 2 ^ m := by
  have h := sum_range_le_of_mul_sub_le (u := fun k ↦ (2 : ℝ) ^ k) (C := 0) one_lt_two
    (by norm_num) (fun k ↦ by rw [pow_succ]; linarith) m
  norm_num at h
  exact h

/-! ### A periodic word -/

/-- The constant word in the block `b = 2` at `g = 1` has limit ratio `1 + √2`: the vector
`(1 + √2, 1)` is a positive eigenvector of `[[5, 2], [2, 1]]`, with eigenvalue `3 + 2√2`. -/
theorem cocycleRatio_const_false :
    cocycleRatio (twoBlockAlphabet 1) (fun _ ↦ false) = 1 + √2 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hv : ∀ i, 0 < (![1 + √2, 1] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i
    · change 0 < 1 + √2
      positivity
    · exact one_pos
  have hl : (cocycle (twoBlockAlphabet 1) (fun _ ↦ false) 1)ᵀ *ᵥ ![1 + √2, 1] =
      (3 + 2 * √2) • ![1 + √2, 1] := by
    ext i
    fin_cases i <;>
      simp [cocycle_succ, twoBlockAlphabet, twoTwistBlock, IFS.blockExponent, mulVec,
        dotProduct, Fin.sum_univ_two] <;>
      nlinarith [hs]
  have h := congrFun (eq_smul_cocycleRay_of_periodic (twoBlockAlphabet_pos one_pos) one_pos
    (fun _ ↦ rfl) hv hl) 0
  simp only [Fin.isValue, cons_val_zero, cons_val_one, Pi.smul_apply, cocycleRay_zero,
    smul_eq_mul, one_mul] at h
  exact h.symm

/-- So the ratios of `P_n (1, 1)` along the constant word converge to `1 + √2`. -/
example : Tendsto (fun n ↦ ((cocycle (twoBlockAlphabet 1) (fun _ ↦ false) n)ᵀ *ᵥ ![1, 1]) 0 /
    ((cocycle (twoBlockAlphabet 1) (fun _ ↦ false) n)ᵀ *ᵥ ![1, 1]) 1) atTop (𝓝 (1 + √2)) := by
  rw [← cocycleRatio_const_false]
  refine tendsto_ratio_transpose_cocycle_mulVec (twoBlockAlphabet_pos one_pos) _ fun i ↦ ?_
  fin_cases i <;> simp

end K3TwistsTest.ProjectiveCocycleExamples
