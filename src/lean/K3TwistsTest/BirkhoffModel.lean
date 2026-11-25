/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Convex.IFS
import K3Twists.Analysis.Normed.Algebra.PowerBound

/-!
# Birkhoff contraction, the two-block alphabet and the power envelope: examples

* Positivity of the entries is needed for a contraction: `[[0, 1], [1, 1]]` and `[[1, 1], [1, 0]]`
  are primitive (their squares are positive) but their product `[[1, 0], [2, 1]]` is reducible.
* The block `T₁² T₂^{-2}` with `g = 1` has count matrix `[[5, 2], [2, 1]]` and Birkhoff
  coefficient `(√5 - 2) / (√5 + 2)`.
* The constant word `b = 2, 2, 2, …` at `g = 1` has centre ratio `1 + √2 = [2; 2, 2, 2, …]`.
-/

open Matrix Real IFS

namespace BirkhoffModel

/-- Two primitive matrices with a reducible product. -/
example : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = !![1, 1; 1, 2] ∧
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = !![2, 1; 1, 1] ∧
    (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 1; 1, 0] = !![1, 0; 2, 1] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

example : twoTwistBlock 2 1 = !![5, 2; 2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [twoTwistBlock]

example : (twoTwistBlock 2 1).birkhoffCoeff = (√5 - 2) / (√5 + 2) := by
  rw [birkhoffCoeff_twoTwistBlock]
  have h4 : √4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [h4]

/-- The constant word in the block `b = 2` at `g = 1` has centre ratio `1 + √2`. -/
theorem centreRatio_const_two : centreRatio 1 (fun _ ↦ false) = 1 + √2 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < 1 + √2 := by positivity
  have hfix : comp (twoBlockLetter 1) 1 (fun _ ↦ false) (log (1 + √2)) = log (1 + √2) := by
    rw [comp_succ, comp_zero, twoBlockLetter, Real.exp_log hpos,
      ratioMap_transpose_twoTwistBlock_eq (by norm_num) hpos]
    congr 1
    simp only [blockExponent]
    have hd : (0 : ℝ) < 2 * 1 * (1 + √2) + 1 := by positivity
    field_simp
    nlinarith [hs]
  have := eq_codingMap_of_periodic (lipschitzWith_twoBlockLetter one_pos)
    (twoBlockConst_lt_one one_pos) one_pos (fun _ ↦ rfl) hfix
  rw [centreRatio, ← this, Real.exp_log hpos]

end BirkhoffModel
