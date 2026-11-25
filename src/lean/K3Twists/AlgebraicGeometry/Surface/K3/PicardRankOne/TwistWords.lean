/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.PicardRankOne
import K3Twists.Combinatorics.Quiver.Kronecker.RealRoots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt

/-!
# The examples of the mass section

* `standard_H_formula`: for a standard autoequivalence `(- ⊗ L^u) f^*[s]` the nine total Hom
  dimensions `2 + d(nu + (i - j)b)²` of the generator sum to `H_n = 18 + 12ν + 9du²n²`, `ν = db²`.
* The word `Θ = T_S T_B` with `S = 𝒪_X` and `B = T_L² 𝒪_X`: the two classes agree, so `Θ` acts
  trivially on the Mukai lattice (`theta_acts_trivially`), yet the total Hom from `B` grows at
  least like `M(M - 1)^{2n}` with `M = h(S, B) = 2q²`, `q = h⁰(L) = d + 2`
  (`theta_lower_bound`): the point-mass multiplier is at least `(M - 1)² > 1` while the Mukai
  spectral radius is one.
* The word `Ψ = T_{𝒪_X} T_L` of the example with two rates: on the plane of `v(𝒪_X)` and `v(L)`
  it acts by a matrix of trace `(d + 2)² - 2` and determinant one (`psi_action`), with an
  eigenvalue `ρ > 1` (`psi_eigenvalue`), and its eigenlines are irrational because
  `(d + 2)² - 4 = d(d + 4)` is not a square (`psi_discriminant_not_square`).
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open Finset Quiver.Kronecker

/-! ### Standard words -/

/-- **The generator orbit of a standard word.** `Σ_{i,j} (2 + d(nu + (i - j)b)²) =
18 + 12db² + 9du²n²` over `i, j ∈ {0, 1, 2}`. -/
theorem standard_H_formula {R : Type*} [CommRing R] (d n u b : R) :
    ∑ i : Fin 3, ∑ j : Fin 3, (2 + d * (n * u + ((i : ℕ) - (j : ℕ) : R) * b) ^ 2) =
      18 + 12 * (d * b ^ 2) + 9 * d * u ^ 2 * n ^ 2 := by
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat]
  ring

/-! ### The word `Θ = T_S T_B` -/

/-- `Θ = T_S T_B` acts trivially on Mukai vectors when `v(B) = v(S)` is a root: the two
reflections cancel. -/
theorem theta_acts_trivially {R : Type*} [CommRing R] {d : R} {s b : MukaiVector R}
    (hs : MukaiVector.IsRoot d s) (hsb : b = s) (v : MukaiVector R) :
    BilinearForm.reflect (MukaiVector.mukaiForm d) s
      (BilinearForm.reflect (MukaiVector.mukaiForm d) b v) = v := by
  rw [hsb]; exact BilinearForm.reflect_reflect (MukaiVector.mukaiForm d) s hs v

/-- `h(S, B) = 1 + (q² - 1) + q² = 2q²` from `dim Hom^j(S, B) = 1, q² - 1, q²` (`j = 0, 1, 2`). -/
lemma theta_hom_SB (q : ℤ) : 1 + (q ^ 2 - 1) + q ^ 2 = 2 * q ^ 2 := by ring

/-- **The lower bound for `Θ = T_S T_B`.** Let `hS, hB` be the total Hom dimensions from `S` and
from `B`, and `TS, TB` the two twists. The twist triangles give
`hS(T_B D) ≥ M hB(D) - hS(D)` and `hB(T_B D) = hB(D)` (because `T_B⁻¹ B = B[1]`), and the same
with `S` and `B` exchanged. Starting from `D₀ = S` with `hS(D₀) = 2 ≤ hB(D₀) = M`, `M ≥ 2`, each
half-step multiplies the larger test by at least `M - 1`, so `hB(Θⁿ S) ≥ M(M - 1)^{2n}`. -/
theorem theta_lower_bound {Obj : Type*} (hS hB : Obj → ℝ) (TS TB : Obj → Obj) {M : ℝ}
    (hM : 2 ≤ M)
    (hTB_S : ∀ D, M * hB D - hS D ≤ hS (TB D)) (hTB_B : ∀ D, hB (TB D) = hB D)
    (hTS_B : ∀ D, M * hS D - hB D ≤ hB (TS D)) (hTS_S : ∀ D, hS (TS D) = hS D)
    (D₀ : Obj) (h0 : hS D₀ ≤ hB D₀) (hB0 : M ≤ hB D₀) (n : ℕ) :
    M * (M - 1) ^ (2 * n) ≤ hB ((TS ∘ TB)^[n] D₀) ∧
      hS ((TS ∘ TB)^[n] D₀) ≤ hB ((TS ∘ TB)^[n] D₀) := by
  induction n with
  | zero => simpa using ⟨hB0, h0⟩
  | succ n ih =>
    obtain ⟨hbig, hord⟩ := ih
    set D := (TS ∘ TB)^[n] D₀ with hD
    have hstep : (TS ∘ TB)^[n + 1] D₀ = TS (TB D) := by
      rw [Function.iterate_succ_apply']; rfl
    rw [hstep]
    have hpow : 0 ≤ M * (M - 1) ^ (2 * n) := by
      have : (0 : ℝ) ≤ M - 1 := by linarith
      positivity
    -- after `T_B`: the `S`-test is at least `(M - 1) hB(D)`
    have h1 : (M - 1) * hB D ≤ hS (TB D) := by linarith [hTB_S D]
    -- after `T_S`: the `B`-test is at least `(M - 1) hS(T_B D)`
    have h2 : (M - 1) * hS (TB D) ≤ hB (TS (TB D)) := by
      have := hTS_B (TB D)
      rw [hTB_B] at this
      have hle : hB D ≤ hS (TB D) := by nlinarith
      nlinarith
    have hM1 : (0 : ℝ) ≤ M - 1 := by linarith
    constructor
    · calc M * (M - 1) ^ (2 * (n + 1)) = (M - 1) * ((M - 1) * (M * (M - 1) ^ (2 * n))) := by ring
        _ ≤ (M - 1) * ((M - 1) * hB D) := by gcongr
        _ ≤ (M - 1) * hS (TB D) := by gcongr
        _ ≤ hB (TS (TB D)) := h2
    · rw [hTS_S]
      have hpos : 0 ≤ hS (TB D) := by
        have : 0 ≤ hB D := le_trans hpow hbig
        nlinarith
      nlinarith

/-! ### The word `Ψ = T_{𝒪_X} T_L` -/

/-- `v(𝒪_X)` and `v(L)`, `L = 𝒪_X(H)`, pair to `-(d + 2)`. -/
lemma pairing_O_L {R : Type*} [CommRing R] (d : R) :
    MukaiVector.pairing d (MukaiVector.lineBundle d 0) (MukaiVector.lineBundle d 1) = -(d + 2) := by
  rw [MukaiVector.pairing_lineBundle]; ring

/-- `Ψ = T_{𝒪_X} T_L` on the plane of `a = v(𝒪_X)` and `b = v(L)`:
`Ψ a = ((d + 2)² - 1) a - (d + 2) b` and `Ψ b = (d + 2) a - b`, a matrix of trace
`(d + 2)² - 2` and determinant one. -/
theorem psi_action {R : Type*} [CommRing R] (d : R) :
    let a := MukaiVector.lineBundle d 0
    let b := MukaiVector.lineBundle d 1
    let ρ := BilinearForm.reflect (MukaiVector.mukaiForm d)
    ρ a (ρ b a) = ((d + 2) ^ 2 - 1) • a + (-(d + 2)) • b ∧
      ρ a (ρ b b) = (d + 2) • a + (-1 : R) • b ∧
      ((d + 2) ^ 2 - 1) + (-1) = (d + 2) ^ 2 - 2 ∧
      ((d + 2) ^ 2 - 1) * (-1) - (d + 2) * (-(d + 2)) = 1 := by
  refine ⟨?_, ?_, by ring, by ring⟩ <;>
    ext <;> simp [MukaiVector.bilinearFormReflect_apply, MukaiVector.pairing,
      MukaiVector.lineBundle] <;> ring

/-- The trace `t = (d + 2)² - 2` exceeds `2` for `d ≥ 1`, so the characteristic polynomial
`x² - tx + 1` has a root `ρ > 1` (and `ρ⁻¹ < 1`). -/
theorem psi_eigenvalue {d : ℝ} (hd : 1 ≤ d) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ^ 2 - ((d + 2) ^ 2 - 2) * ρ + 1 = 0 := by
  set t := (d + 2) ^ 2 - 2 with ht
  have ht2 : 2 < t := by rw [ht]; nlinarith
  have hdisc : 0 ≤ t ^ 2 - 4 := by nlinarith
  refine ⟨(t + √(t ^ 2 - 4)) / 2, ?_, ?_⟩
  · have := Real.sqrt_nonneg (t ^ 2 - 4)
    linarith
  · have h := Real.sq_sqrt hdisc
    ring_nf
    ring_nf at h
    nlinarith [h]

/-- The discriminant `(d + 2)² - 4 = d(d + 4)` is not a perfect square for `d ≥ 1`: the
eigenlines of `Ψ` are irrational, so `v(𝒪_x)` has a nonzero expanding component. -/
theorem psi_discriminant_not_square {d : ℤ} (hd : 1 ≤ d) : ¬ IsSquare (d * (d + 4)) := by
  have h := not_isSquare_sq_sub_four (g := d + 2) (by rw [abs_of_nonneg (by linarith)]; linarith)
  rwa [show (d + 2) ^ 2 - 4 = d * (d + 4) by ring] at h

end AlgebraicGeometry.K3.PicardRankOne
