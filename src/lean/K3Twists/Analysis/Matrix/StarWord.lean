/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.BipartiteCompression
import K3Twists.Analysis.Matrix.SLTwoRate

/-!
# The star word

Take a star: one hub and `d ≥ 1` leaves, each leaf meeting the hub once. The bipartite word
`P = H ∏ L_i⁻¹`, the twist at the hub after the inverse twists at the leaves, acts on hub and
leaf counts `(x, y)` by

  `[[1 + d, 𝟙ᵀ], [𝟙, I_d]]`:

first every leaf picks up the hub (`y ↦ y + x 𝟙`), then the hub picks up all leaves
(`x ↦ x + 𝟙ᵀ y`). In the language of `BipartiteCompression.lean` this is the word
`[A 1, B 1]` for the `1 × d` intersection matrix `𝟙ᵀ`, whose Perron data are `u = 1`,
`v = 𝟙/√d`, `μ = √d`. The compression `(x, y) ↦ (x, 𝟙ᵀ y/√d)` carries it to the Thurston product
`[[1, √d], [0, 1]] [[1, 0], [√d, 1]]` of determinant one and trace `d + 2`, so:

* `Matrix.BipartiteCompression.tendsto_star_rate`: the total count of `Pⁿ z` grows at the rate
  `sl2Rate (d + 2) = (d + 2 + √(d² + 4d))/2` for every seed `z ≥ 0` with a positive hub count and
  a positive leaf sum;
* `Matrix.BipartiteCompression.starRate_root`: **the star polynomial**, the rate is the larger
  root of `t² - (d + 2) t + 1`, and it exceeds one.

The rate does not depend on how the leaves are spread: no Perron–Frobenius argument on the
`(d + 1) × (d + 1)` matrix is needed, only the two relations `uᵀ G = μ vᵀ`, `G v = μ u`.
-/

open Filter Topology

namespace Matrix.BipartiteCompression

open scoped Matrix.Norms.Operator

/-- The intersection matrix of a star with `d` leaves: the hub meets every leaf once. -/
def starMatrix (d : ℕ) : Matrix Unit (Fin d) ℝ := fun _ _ => 1

/-- The star word `P = H ∏ L_i⁻¹`: the leaves pick up the hub, then the hub picks up the leaves. -/
def starWord : List Letter := [.A 1, .B 1]

/-- **The rate of the star word.** For `d ≥ 1` leaves and a seed `z ≥ 0` with a positive hub count
and a positive leaf sum, the total count of `Pⁿ z` grows at the rate
`sl2Rate (d + 2) = (d + 2 + √((d + 2)² - 4))/2`. -/
theorem tendsto_star_rate {d : ℕ} (hd : 1 ≤ d) (z : (Unit → ℝ) × (Fin d → ℝ))
    (hz : 0 ≤ z.1 ∧ 0 ≤ z.2) (hx : 0 < z.1 ()) (hy : 0 < ∑ j, z.2 j) :
    Tendsto (fun n : ℕ => (∑ i, ((fun z => starWord.foldr (act (starMatrix d)) z)^[n] z).1 i +
        ∑ j, ((fun z => starWord.foldr (act (starMatrix d)) z)^[n] z).2 j) ^ (n : ℝ)⁻¹)
      atTop (𝓝 (Matrix.sl2Rate (d + 2))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set μ := √(d : ℝ) with hμ
  have hμ0 : 0 < μ := Real.sqrt_pos.2 hd0
  have hμ1 : 1 ≤ μ := by
    rw [hμ, show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  have hμsq : μ ^ 2 = d := Real.sq_sqrt hd0.le
  set u : Unit → ℝ := fun _ => 1 with hu
  set v : Fin d → ℝ := fun _ => μ⁻¹ with hv
  have hmμ : 0 < μ⁻¹ := inv_pos.2 hμ0
  have hμinv1 : μ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hμ1
  have huG : u ᵥ* starMatrix d = μ • v := by
    funext j
    simp [hu, hv, starMatrix, vecMul, dotProduct, hμ0.ne']
  have hGv : starMatrix d *ᵥ v = μ • u := by
    funext i
    simp only [starMatrix, mulVec, dotProduct, hv, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Pi.smul_apply, hu, smul_eq_mul, mul_one]
    rw [← hμsq]
    field_simp
  have hw : ∀ ℓ ∈ starWord, ℓ.Nonneg := by
    intro ℓ hℓ
    simp only [starWord, List.mem_cons, List.not_mem_nil, or_false] at hℓ
    rcases hℓ with rfl | rfl <;> norm_num [Letter.Nonneg]
  set c := min (z.1 ()) (μ⁻¹ * ∑ j, z.2 j) with hc
  have hc0 : 0 < c := lt_min hx (mul_pos hmμ hy)
  have hκ : ∀ k, c ≤ compress u v z k := by
    intro k
    fin_cases k
    · simp [compress, hu, dotProduct, hc]
    · simp only [compress, hv, dotProduct, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        hc]
      rw [← Finset.mul_sum]
      exact min_le_right _ _
  have h := tendsto_rate_of_compress_pos (starMatrix d) (fun _ _ => zero_le_one) (μ := μ)
    (m := μ⁻¹) (M := 1) hμ0.le hmμ (fun _ => by simp [hu]; exact hμinv1) (fun _ => by simp [hu])
    (fun _ => le_rfl) (fun _ => hμinv1) huG hGv starWord hw z hz hc0 hκ
  have hprod : (starWord.map (thurston μ)).prod = thurstonA 1 μ * thurstonB 1 μ := by
    simp [starWord, thurston]
  have hl : gelfandRadius (thurstonA 1 μ * thurstonB 1 μ) = Matrix.sl2Rate (d + 2) := by
    have ht : (2 : ℝ) < d + 2 := by linarith
    refine gelfandRadius_thurston (Matrix.one_lt_sl2Rate ht) ?_
    rw [Matrix.sl2Rate_add_inv ht.le, hμsq]
    ring
  rwa [hprod, hl] at h

/-- **The star polynomial.** The rate `λ = sl2Rate (d + 2)` of the star word with `d ≥ 1` leaves is
the larger root of `t² - (d + 2) t + 1`, and `λ > 1`. -/
theorem starRate_root {d : ℕ} (hd : 1 ≤ d) :
    Matrix.sl2Rate (d + 2) ^ 2 - (d + 2) * Matrix.sl2Rate (d + 2) + 1 = 0 ∧
      1 < Matrix.sl2Rate (d + 2) := by
  have ht : (2 : ℝ) < d + 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact ⟨Matrix.sl2Rate_sq_sub_mul_add_one ht.le, Matrix.one_lt_sl2Rate ht⟩

end Matrix.BipartiteCompression
