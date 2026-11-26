/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.EulerMass
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.EulerTwistSystem
import K3Twists.Analysis.Matrix.StarWord
import K3Twists.GroupTheory.GroupAction.MassComparison.FixedWord
import K3Twists.GroupTheory.GroupAction.TwistSystem.Bipartite

/-!
# The growth bounds on the library's instances

The bipartite bound, the fixed-word formula and the bipartite joint spectral radius, applied to
instances of the library, so that their hypotheses are checked to be satisfiable:

* the Euler-count system of `𝒪_X` and `𝒪_X(H)` on a K3 surface of Picard rank one, two centres of
  count `d + 2`, has `e^η ≤ ρ_{d+2} < d + 3`;
* the fixed-word formula holds for the point class under every word of the lattice mass instance
  `eulerMass`;
* the single twists of the `D₄` diagram, a star with three leaves, have joint spectral radius the
  golden ratio, as for `A₂`: the valence of the hub does not matter;
* the star word with three leaves grows at `(5 + √21)/2`, the larger root of `t² - 5t + 1`.

Built by `lake test`.
-/

namespace K3TwistsTest.GrowthBoundModel

open AlgebraicGeometry.K3.PicardRankOne MukaiVector Filter Topology Real Matrix

/-- **The bipartite bound on the Euler-count system**: `e^η ≤ ρ_{d+2}`. -/
example (d : ℤ) (hd : 0 ≤ d) :
    exp (eulerTwistSystem d).homExponent ≤ ((d + 2 : ℝ) + √((d + 2 : ℝ) ^ 2 + 4)) / 2 := by
  refine (eulerTwistSystem d).exp_homExponent_le_of_bipartite (eulerTwistSystem_lowerBound d)
    (eulerTwistSystem_isSpherical d) (eulerTwistSystem_directedConnected d hd)
    (fun i => decide (i = 0)) (fun i k hik hp => ?_) (by
      have : (0 : ℝ) ≤ d := by exact_mod_cast hd
      linarith) (fun i k hik => ?_)
  · fin_cases i <;> fin_cases k <;> simp_all
  · have hpair : ((eulerTwistSystem d).h ((eulerTwistSystem d).S i)
        ((eulerTwistSystem d).S k) : ℤ) = d + 2 := by
      change ((pairing d (lineCentre d i) (lineCentre d k)).natAbs : ℤ) = d + 2
      fin_cases i <;> fin_cases k
      · exact absurd rfl hik
      · simp only [Fin.zero_eta, Fin.mk_one]
        rw [pairing_lineCentre_zero_one, Int.natCast_natAbs, abs_neg, abs_of_nonneg (by omega)]
      · simp only [Fin.zero_eta, Fin.mk_one]
        rw [pairing_comm, pairing_lineCentre_zero_one, Int.natCast_natAbs, abs_neg,
          abs_of_nonneg (by omega)]
      · exact absurd rfl hik
    have : ((eulerTwistSystem d).h ((eulerTwistSystem d).S i) ((eulerTwistSystem d).S k) : ℝ) =
        d + 2 := by exact_mod_cast hpair
    rw [this]

/-- **The fixed-word formula on the lattice mass instance**, for the point class. -/
example (d : ℤ) (hd : 1 ≤ d) (g : mukaiIsometries d) (w : List (Fin 2)) :
    limsup (fun n : ℕ => (eulerMass d hd).mass g ((eulerClassTwistSystem d).word w ^ n •
        ClassSum.single MukaiVector.point) ^ (n : ℝ)⁻¹) atTop =
      max 1 (limsup (fun n : ℕ => ((eulerClassTwistSystem d).centreCount
        ((eulerClassTwistSystem d).word w ^ n • ClassSum.single MukaiVector.point) : ℝ) ^
          (n : ℝ)⁻¹) atTop) := by
  refine (eulerClassTwistSystem_isTwistSystem d hd).limsup_mass_pow g w ?_
  refine lt_of_lt_of_le one_pos (one_le_hom_smul_lineGenerator d (by omega) g ?_)
  intro h
  have := congrArg MukaiVector.s h
  simp [MukaiVector.point] at this

/-- The `D₄` diagram: a hub `0` joined once to each of three leaves. -/
def d4 : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if (i = 0 ∧ j ≠ 0) ∨ (i ≠ 0 ∧ j = 0) then 1 else 0

/-- **The single twists of `D₄` have joint spectral radius the golden ratio.** -/
example : jointSpectralRadius (graphTransvection d4) = (1 + √5) / 2 := by
  have h := jointSpectralRadius_graphTransvection_bipartite (G := d4) (s := 1)
    (fun i j => by unfold d4; split_ifs <;> norm_num) (fun i => decide (i = 0))
    (fun i j hp => by fin_cases i <;> fin_cases j <;> simp_all [d4])
    (fun i j => by unfold d4; split_ifs <;> norm_num) le_rfl (i₀ := 0) (j₀ := 1)
    (by simp [d4]) (by simp [d4])
  norm_num at h
  exact h

/-- The star word with three leaves grows at `(5 + √21)/2`, a root of `t² - 5t + 1`. -/
example : Matrix.sl2Rate (3 + 2) = (5 + √21) / 2 ∧
    Matrix.sl2Rate (3 + 2) ^ 2 - (3 + 2) * Matrix.sl2Rate (3 + 2) + 1 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.sl2Rate]
    norm_num
  · have := (Matrix.BipartiteCompression.starRate_root (d := 3) (by norm_num)).1
    exact_mod_cast this

end K3TwistsTest.GrowthBoundModel
