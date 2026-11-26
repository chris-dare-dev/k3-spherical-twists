/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Phase gaps of finitely many charges

Phases are measured in units of `π`: a nonzero complex number `z` lies on the ray of phase `ψ`
when `z = m e^{iπψ}` with `m > 0`, and `ψ` is then determined modulo `2`
(`Complex.eq_of_mul_exp_eq`). For finitely many charges `z ∈ S` and finitely many phases
`φ ∈ Φ` there is a **phase gap**: some `ε ∈ (0, 1/8)` such that `2ε` is smaller than every nonzero
distance from a `φ ∈ Φ` to a phase of some `z ∈ S`, and smaller than every nonzero distance
between two phases of `Φ` (`Complex.exists_phaseGap`). It is the choice of neighbourhood in the
lemma on intersecting ordinary walls (Bridgeland, arXiv:math/0212237, §8): the charges are those
of the finitely many lattice classes of square at least `-2` and bounded charge.
-/

open Real

namespace Complex

/-- **A ray determines its phase modulo `2`.** If `m e^{iπψ} = m' e^{iπψ'}` with `m, m' > 0` and
`|ψ - ψ'| < 1`, then `ψ = ψ'`. -/
theorem eq_of_mul_exp_eq {m m' ψ ψ' : ℝ} (hm : 0 < m)
    (h : (m : ℂ) * exp ((π * ψ : ℝ) * I) = (m' : ℂ) * exp ((π * ψ' : ℝ) * I))
    (hψ : |ψ - ψ'| < 1) : ψ = ψ' := by
  have key : (m : ℂ) * exp ((π * (ψ - ψ') : ℝ) * I) = (m' : ℂ) := by
    have e1 : exp ((π * (ψ - ψ') : ℝ) * I) =
        exp ((π * ψ : ℝ) * I) * exp (-((π * ψ' : ℝ) * I)) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    rw [e1, ← mul_assoc, h, mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]
  have him := congrArg im key
  rw [im_ofReal_mul, exp_ofReal_mul_I_im, ofReal_im] at him
  have hsin : Real.sin (π * (ψ - ψ')) = 0 := (mul_eq_zero.mp him).resolve_left hm.ne'
  have hlt := abs_lt.mp hψ
  have h0 : π * (ψ - ψ') = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])).mp hsin
  have := (mul_eq_zero.mp h0).resolve_left Real.pi_ne_zero
  linarith

/-- **The phase gap.** For a finite set `S` of charges and a finite set `Φ` of phases there is
`ε ∈ (0, 1/8)` such that a charge of `S` on a ray of phase `ψ` with `|ψ - φ| < 2ε` for some
`φ ∈ Φ` has `ψ = φ`, and distinct phases of `Φ` are more than `2ε` apart. -/
theorem exists_phaseGap (S : Set ℂ) (hS : S.Finite) (Φ : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧
      (∀ z ∈ S, ∀ φ ∈ Φ, ∀ m ψ : ℝ, 0 < m → z = (m : ℂ) * exp ((π * ψ : ℝ) * I) →
        |ψ - φ| < 2 * ε → ψ = φ) ∧
      ∀ φ ∈ Φ, ∀ φ' ∈ Φ, φ ≠ φ' → 2 * ε < |φ - φ'| := by
  classical
  -- the phases of `z` within `1/2` of `φ`: at most one
  let A : ℂ → ℝ → Set ℝ := fun z φ =>
    {ψ | |ψ - φ| < 1 / 2 ∧ ∃ m : ℝ, 0 < m ∧ z = (m : ℂ) * exp ((π * ψ : ℝ) * I)}
  have hA : ∀ z φ, (A z φ).Subsingleton := by
    rintro z φ ψ₁ ⟨h₁, m₁, hm₁, hz₁⟩ ψ₂ ⟨h₂, m₂, hm₂, hz₂⟩
    refine eq_of_mul_exp_eq hm₁ (hz₁.symm.trans hz₂) ?_
    have := abs_sub_le ψ₁ φ ψ₂
    rw [abs_sub_comm φ ψ₂] at this
    linarith
  -- the nonzero distances to avoid
  let D : Set ℝ := (⋃ z ∈ S, ⋃ φ ∈ (Φ : Set ℝ), (fun ψ => |ψ - φ|) '' (A z φ \ {φ})) ∪
    (⋃ φ ∈ (Φ : Set ℝ), ⋃ φ' ∈ (Φ : Set ℝ) \ {φ}, {|φ - φ'|})
  have hD : D.Finite := by
    refine Set.Finite.union (hS.biUnion fun z _ => Φ.finite_toSet.biUnion fun φ _ =>
      ((hA z φ).anti Set.sdiff_subset).finite.image _) ?_
    exact Φ.finite_toSet.biUnion fun φ _ => (Φ.finite_toSet.sdiff).biUnion fun _ _ =>
      Set.finite_singleton _
  have hDpos : ∀ d ∈ D, 0 < d := by
    rintro d (hd | hd)
    · simp only [Set.mem_iUnion, Set.mem_image] at hd
      obtain ⟨z, -, φ, -, ψ, ⟨-, hψ⟩, rfl⟩ := hd
      exact abs_pos.mpr (sub_ne_zero.mpr hψ)
    · simp only [Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff] at hd
      obtain ⟨φ, -, φ', ⟨-, hne⟩, rfl⟩ := hd
      exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  -- a positive lower bound `d₀` of `D`
  obtain ⟨d₀, hd₀, hd₀D⟩ : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d ∈ D, d₀ ≤ d := by
    by_cases hne : hD.toFinset.Nonempty
    · refine ⟨hD.toFinset.min' hne, hDpos _ (hD.mem_toFinset.mp (Finset.min'_mem _ _)),
        fun d hd => Finset.min'_le _ _ (hD.mem_toFinset.mpr hd)⟩
    · refine ⟨1, one_pos, fun d hd => absurd ⟨d, hD.mem_toFinset.mpr hd⟩ hne⟩
  refine ⟨min (1 / 16) (d₀ / 4), lt_min (by norm_num) (by positivity),
    (min_le_left _ _).trans_lt (by norm_num), fun z hz φ hφ m ψ hm hzψ hlt => ?_,
    fun φ hφ φ' hφ' hne => ?_⟩
  · by_contra hne
    have hle : min (1 / 16) (d₀ / 4) ≤ 1 / 16 := min_le_left _ _
    have hmem : |ψ - φ| ∈ D := Or.inl (by
      simp only [Set.mem_iUnion, Set.mem_image]
      exact ⟨z, hz, φ, hφ, ψ, ⟨⟨by linarith, m, hm, hzψ⟩, hne⟩, rfl⟩)
    have := hd₀D _ hmem
    have hle' : min (1 / 16) (d₀ / 4) ≤ d₀ / 4 := min_le_right _ _
    linarith
  · have hmem : |φ - φ'| ∈ D := Or.inr (by
      simp only [Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨φ, hφ, φ', ⟨hφ', Ne.symm hne⟩, rfl⟩)
    have := hd₀D _ hmem
    have hle' : min (1 / 16) (d₀ / 4) ≤ d₀ / 4 := min_le_right _ _
    linarith

end Complex
