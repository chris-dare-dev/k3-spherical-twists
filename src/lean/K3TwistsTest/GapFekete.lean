/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.SpecificLimits.GrowthRate
import K3Twists.GroupTheory.Commutator.ForkWord

/-!
# Fekete's lemma with a gap: why the supremum starts at `q = 1`

`Real.tendsto_div_of_superadd_gap` takes the supremum of the certificates `ℓ(q)/(q + D)` over
`q ≥ 1` only. With `q = 0` allowed and `D = 0`, the convention `x / 0 = 0` adds the certificate
`0`, and the statement becomes false: `ℓ(n) = -n` is additive, its limit is `-1`, while the
supremum over all `q` is `0`. This file checks the counterexample, and that the restricted
statement gives the right limit on it.

Built by `lake test`.
-/

namespace K3TwistsTest.GapFekete

open Filter Topology Real

/-- `ℓ(n) = -n` satisfies the gap inequality with `D = 0`. -/
lemma superadd_neg (m n : ℕ) : -(m : ℝ) + -(n : ℝ) ≤ -((m + n + 0 : ℕ) : ℝ) := by
  push_cast; linarith

/-- With `q = 0` included the supremum is `0`, but the limit is `-1`. -/
theorem fekete_q0_false :
    ¬ Tendsto (fun N : ℕ => -(N : ℝ) / N) atTop
      (𝓝 (⨆ q : ℕ, -(q : ℝ) / ((q : ℝ) + ((0 : ℕ) : ℝ)))) := by
  have hle : ∀ q : ℕ, -(q : ℝ) / ((q : ℝ) + ((0 : ℕ) : ℝ)) ≤ 0 := fun q => by
    simp only [Nat.cast_zero, add_zero]
    exact div_nonpos_of_nonpos_of_nonneg (by simp) (Nat.cast_nonneg q)
  have hb : BddAbove (Set.range fun q : ℕ => -(q : ℝ) / ((q : ℝ) + ((0 : ℕ) : ℝ))) :=
    ⟨0, by rintro _ ⟨q, rfl⟩; exact hle q⟩
  have hsup : (⨆ q : ℕ, -(q : ℝ) / ((q : ℝ) + ((0 : ℕ) : ℝ))) = 0 := by
    refine le_antisymm (ciSup_le hle) ?_
    have := le_ciSup hb 0
    simpa using this
  have hlim : Tendsto (fun N : ℕ => -(N : ℝ) / N) atTop (𝓝 (-1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  intro h
  rw [hsup] at h
  have := tendsto_nhds_unique hlim h
  norm_num at this

/-- The supremum over `q ≥ 1` is the limit `-1`. -/
example : Tendsto (fun N : ℕ => -(N : ℝ) / N) atTop
    (𝓝 (⨆ q : ℕ, -((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + ((0 : ℕ) : ℝ)))) := by
  refine tendsto_div_of_superadd_gap (ℓ := fun n => -(n : ℝ)) superadd_neg ⟨0, ?_⟩
  rintro _ ⟨q, rfl⟩
  simp only [Nat.cast_zero, add_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by push_cast; linarith) (by positivity)

/-- The witness `2^{n + ⌈√n⌉}` is submultiplicative with rate `2` and no polynomial envelope. -/
example : (∀ a b, sqrtWitness 2 (a + b) ≤ sqrtWitness 2 a * sqrtWitness 2 b) ∧
    Tendsto (fun n : ℕ => sqrtWitness 2 n ^ (n : ℝ)⁻¹) atTop (𝓝 2) ∧
    ¬ ∃ B s : ℝ, ∀ n : ℕ, sqrtWitness 2 n ≤ B * (1 + n) ^ s * 2 ^ n :=
  ⟨sqrtWitness_add_le two_pos, tendsto_sqrtWitness two_pos,
    not_exists_poly_envelope_sqrtWitness two_pos⟩

/-- With a single letter `L` and the braid relation `H L H = L H L` of `A₂`, the first fork word
is `⁅H, L⁆ = L⁻¹ (H L⁻¹) L`. -/
example {G : Type*} [Group G] {H L : G} (h : H * L * H = L * H * L) :
    forkWord H (fun _ => L) 1 = L⁻¹ * (H * L⁻¹) * L⁻¹⁻¹ := by
  have := forkWord_succ_eq_conj (H := H) (L := fun _ => L) (fun _ _ => Commute.refl L)
    (fun _ => h) 0
  simpa [forkConj] using this

end K3TwistsTest.GapFekete
