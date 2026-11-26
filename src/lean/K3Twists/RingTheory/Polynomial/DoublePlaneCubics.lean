/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RingTheory.IntegralClosure.Away
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# The cubics of a block family on the double plane

On a K3 surface of Picard rank one with `H² = 2` (a double plane), write `T_j` for the spherical
twist by `𝒪(jH)`. The study computes the action of the word `W_s = T₀T₁T₃ˢ` on the standard
cohomology of line bundles by the integer matrix `M_s = M₁ + (s - 1) u vᵀ`, `u = (4, 3, 3)`,
`v = (11, 6, 1)`, and identifies the multiplier of `W_s` with the Perron root of its
characteristic polynomial `P_s(t) = t³ - (65s - 8)t² - (9s - 8)t - (16s - 1)`. That
identification is geometry and is not formalized; this file proves the arithmetic of the family
from Mathlib alone.

## Main results

* `charpoly_blockMatrix`, `det_blockMatrix`, `trace_blockMatrix`, `blockMatrix_eq`: `P_s` is the
  characteristic polynomial of `M_s`, `det M_s = 16s - 1`, `tr M_s = 65s - 8`, and `M_s` is the
  rank-one pencil `M₁ + (s - 1) u vᵀ`.
* `pos_of_aeval_cubic`, `eq_of_aeval_cubic`, `exists_aeval_cubic_eq_zero`: for `s ≥ 1`, `P_s` has
  exactly one real root, and it is positive. A real root of `P_s` is therefore its Perron root:
  allowing "any root" of `P_s` gains nothing.
* `irreducible_map_zmod_nineteen`, `irreducible_cubic_of_mod_nineteen`: for `s ≡ 1 (mod 19)` the
  reduction of `P_s` modulo `19` is `t³ - 57t² - t - 15`, which has no root in `ℤ/19`, so `P_s` is
  irreducible over `ℚ`.
* `irreducible_cubic`: for every `s ≥ 1`, `P_s` is irreducible over `ℚ`, by the rational root
  theorem: an integer root would divide `16s - 1`, while `P_s` is negative at every integer up to
  `16s - 1`.
* `exists_dvd_of_prime`, `exists_prime_dvd_not_dvd`: every prime `p ∉ {2, 19}` divides some
  `16s - 1` with `s ≡ 1 (mod 19)` (Chinese remainder theorem), so the norms `16s - 1` of the roots
  have prime divisors outside every finite set.
* `not_isIntegral_inv_of_aeval_cubic`: for `s ≥ 1` the roots of `P_s` are algebraic integers but
  not algebraic units.
-/

open Polynomial

namespace Polynomial.DoublePlane

/-! ### The cubics -/

/-- `P_s(t) = t³ - (65s - 8)t² - (9s - 8)t - (16s - 1)`. -/
noncomputable def cubic (s : ℕ) : ℤ[X] :=
  X ^ 3 - C (65 * (s : ℤ) - 8) * X ^ 2 - C (9 * (s : ℤ) - 8) * X - C (16 * (s : ℤ) - 1)

lemma natDegree_cubic (s : ℕ) : (cubic s).natDegree = 3 := by
  unfold cubic
  compute_degree!

lemma monic_cubic (s : ℕ) : (cubic s).Monic := by
  unfold cubic
  monicity!

lemma coeff_zero_cubic (s : ℕ) : (cubic s).coeff 0 = -(16 * (s : ℤ) - 1) := by
  simp [cubic, coeff_X]

lemma aeval_cubic {A : Type*} [CommRing A] (s : ℕ) (x : A) :
    aeval x (cubic s) = x ^ 3 - (65 * (s : A) - 8) * x ^ 2 - (9 * (s : A) - 8) * x
      - (16 * (s : A) - 1) := by
  simp [cubic, map_ofNat]

/-- The roots of `P_s` are algebraic integers. -/
lemma isIntegral_of_aeval_cubic {A : Type*} [CommRing A] (s : ℕ) {x : A}
    (hx : aeval x (cubic s) = 0) : IsIntegral ℤ x :=
  ⟨cubic s, monic_cubic s, hx⟩

/-! ### Real roots -/

/-- For `s ≥ 1` every real root of `P_s` is positive: for `x ≤ 0` both `x³` and
`-(65s - 8)x² - (9s - 8)x - (16s - 1)` are negative, the quadratic having negative
discriminant. -/
theorem pos_of_aeval_cubic {s : ℕ} (hs : 1 ≤ s) {x : ℝ} (hx : aeval x (cubic s) = 0) :
    0 < x := by
  rw [aeval_cubic] at hx
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  by_contra h
  replace h : x ≤ 0 := not_lt.1 h
  have hx3 : x ^ 3 ≤ 0 := by
    have : x ^ 3 = x * x ^ 2 := by ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg x)
  nlinarith [sq_nonneg (2 * (65 * (s : ℝ) - 8) * x + (9 * s - 8)), sq_nonneg x]

/-- For `s ≥ 1`, `P_s` has at most one real root. -/
theorem eq_of_aeval_cubic {s : ℕ} (hs : 1 ≤ s) {x y : ℝ} (hx : aeval x (cubic s) = 0)
    (hy : aeval y (cubic s) = 0) : x = y := by
  have hx0 := pos_of_aeval_cubic hs hx
  have hy0 := pos_of_aeval_cubic hs hy
  rw [aeval_cubic] at hx hy
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  set a : ℝ := 65 * (s : ℝ) - 8 with ha
  set b : ℝ := 9 * (s : ℝ) - 8 with hb
  set c : ℝ := 16 * (s : ℝ) - 1 with hc
  have ha0 : 0 < a := by rw [ha]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  have hc0 : 0 < c := by rw [hc]; linarith
  have key : a * x ^ 2 * y ^ 2 * (y - x) + b * x * y * ((y - x) * (y + x))
      + c * ((y - x) * (y ^ 2 + x * y + x ^ 2)) = 0 := by
    linear_combination (-(y ^ 3)) * hx + x ^ 3 * hy
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exfalso
    have hd : 0 < y - x := sub_pos.mpr hxy
    have : 0 < a * x ^ 2 * y ^ 2 * (y - x) + b * x * y * ((y - x) * (y + x))
        + c * ((y - x) * (y ^ 2 + x * y + x ^ 2)) := by positivity
    linarith
  · exact hxy
  · exfalso
    have hd : 0 < x - y := sub_pos.mpr hxy
    have : 0 < a * x ^ 2 * y ^ 2 * (x - y) + b * x * y * ((x - y) * (y + x))
        + c * ((x - y) * (y ^ 2 + x * y + x ^ 2)) := by positivity
    nlinarith

/-- For `s ≥ 1`, `P_s` has a real root, in `(0, 100s)`. -/
theorem exists_aeval_cubic_eq_zero {s : ℕ} (hs : 1 ≤ s) : ∃ x : ℝ, aeval x (cubic s) = 0 := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  let f : ℝ → ℝ := fun x => x ^ 3 - (65 * (s : ℝ) - 8) * x ^ 2 - (9 * (s : ℝ) - 8) * x
    - (16 * (s : ℝ) - 1)
  have hf : Continuous f := by fun_prop
  have h0 : f 0 ≤ 0 := by simp only [f]; nlinarith
  have h1 : 0 ≤ f (100 * s) := by
    simp only [f]
    nlinarith [sq_nonneg (s : ℝ), mul_pos (by linarith : (0 : ℝ) < s) (by linarith : (0 : ℝ) < s)]
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (by nlinarith : (0 : ℝ) ≤ 100 * s) hf.continuousOn
    ⟨h0, h1⟩
  exact ⟨x, by rw [aeval_cubic]; exact hx⟩

/-! ### Irreducibility -/

lemma cubic_mod_nineteen_ne_zero : ∀ x : ZMod 19, x ^ 3 - 57 * x ^ 2 - x - 15 ≠ 0 := by
  decide

/-- For `s ≡ 1 (mod 19)`, `P_s` is irreducible modulo `19`: it has no root in `ℤ/19`. -/
theorem irreducible_map_zmod_nineteen {s : ℕ} (hs : s % 19 = 1) :
    Irreducible ((cubic s).map (Int.castRingHom (ZMod 19))) := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hs' : (s : ZMod 19) = 1 := by
    rw [← ZMod.natCast_mod s 19, hs]
    simp
  have hdeg : ((cubic s).map (Int.castRingHom (ZMod 19))).natDegree = 3 := by
    rw [(monic_cubic s).natDegree_map, natDegree_cubic]
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  rw [mem_roots ((monic_cubic s).map _).ne_zero, IsRoot.def, eval_map, ← algebraMap_int_eq,
    ← aeval_def, aeval_cubic, hs'] at hx
  exact cubic_mod_nineteen_ne_zero x (by linear_combination hx)

/-- For `s ≡ 1 (mod 19)`, `P_s` is irreducible over `ℚ`, by reduction modulo `19`. -/
theorem irreducible_cubic_of_mod_nineteen {s : ℕ} (hs : s % 19 = 1) :
    Irreducible ((cubic s).map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hZ : Irreducible (cubic s) :=
    (monic_cubic s).irreducible_of_irreducible_map (Int.castRingHom (ZMod 19)) _
      (irreducible_map_zmod_nineteen hs)
  rw [← algebraMap_int_eq]
  exact ((monic_cubic s).irreducible_iff_irreducible_map_fraction_map (K := ℚ)).1 hZ

/-- For `s ≥ 1`, `P_s` has no integer root. -/
lemma aeval_cubic_int_ne_zero {s : ℕ} (hs : 1 ≤ s) (m : ℤ) : aeval m (cubic s) ≠ 0 := by
  intro h
  rw [aeval_cubic] at h
  have hs' : (1 : ℤ) ≤ s := by exact_mod_cast hs
  have hdvd : m ∣ 16 * (s : ℤ) - 1 :=
    ⟨m ^ 2 - (65 * s - 8) * m - (9 * s - 8), by linear_combination -h⟩
  rcases le_or_gt m 0 with hm | hm
  · nlinarith [sq_nonneg (2 * (65 * (s : ℤ) - 8) * m + (9 * s - 8)), sq_nonneg m,
      mul_nonpos_of_nonpos_of_nonneg hm (sq_nonneg m)]
  · have hle : m ≤ 16 * (s : ℤ) - 1 := Int.le_of_dvd (by omega) hdvd
    have h1 : m ^ 2 * (m - (65 * s - 8)) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (by omega)
    nlinarith

/-- **`P_s` is irreducible over `ℚ` for every `s ≥ 1`**, by the rational root theorem: a rational
root of the monic `P_s` is an integer, and `P_s` has no integer root. -/
theorem irreducible_cubic {s : ℕ} (hs : 1 ≤ s) :
    Irreducible ((cubic s).map (Int.castRingHom ℚ)) := by
  have hdeg : ((cubic s).map (Int.castRingHom ℚ)).natDegree = 3 := by
    rw [(monic_cubic s).natDegree_map, natDegree_cubic]
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [mem_roots ((monic_cubic s).map _).ne_zero, IsRoot.def, eval_map, ← algebraMap_int_eq,
    ← aeval_def] at hr
  obtain ⟨m, hm⟩ := isInteger_of_is_root_of_monic (monic_cubic s) hr
  rw [← hm] at hr
  apply aeval_cubic_int_ne_zero hs m
  have : aeval (algebraMap ℤ ℚ m) (cubic s) = algebraMap ℤ ℚ (aeval m (cubic s)) := by
    rw [aeval_algebraMap_apply]
  rw [this] at hr
  simpa using hr

/-! ### Prime divisors of the norms -/

/-- Every prime `p ∉ {2, 19}` divides `16s - 1` for some `s ≥ 1` with `s ≡ 1 (mod 19)`. -/
theorem exists_dvd_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp19 : p ≠ 19) :
    ∃ s : ℕ, 1 ≤ s ∧ s % 19 = 1 ∧ (p : ℤ) ∣ 16 * (s : ℤ) - 1 := by
  have hcop : Nat.Coprime 19 p := (Nat.coprime_primes (by norm_num) hp).2 (Ne.symm hp19)
  haveI := Fact.mk hp
  have h16 : (16 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((16 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have h2 : p ∣ 2 ^ 4 := by norm_num; exact h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  obtain ⟨s, hs19, hsp⟩ := Nat.chineseRemainder hcop 1 ((16 : ZMod p)⁻¹).val
  have hs19' : s % 19 = 1 := hs19
  refine ⟨s, ?_, hs19', ?_⟩
  · rcases Nat.eq_zero_or_pos s with h | h
    · simp [h] at hs19'
    · exact h
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have : (s : ZMod p) = (((16 : ZMod p)⁻¹).val : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff s _ p).2 hsp
    rw [this, ZMod.natCast_zmod_val]
    field_simp
    ring

/-- For every `N > 0` some prime not dividing `N` divides some `16s - 1`, `s ≥ 1`,
`s ≡ 1 (mod 19)`. -/
theorem exists_prime_dvd_not_dvd (N : ℕ) (hN : 0 < N) :
    ∃ s : ℕ, 1 ≤ s ∧ s % 19 = 1 ∧
      ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ 16 * (s : ℤ) - 1 ∧ ¬ p ∣ N := by
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (N + 20)
  have hpN : ¬ p ∣ N := fun h => by have := Nat.le_of_dvd hN h; omega
  obtain ⟨s, hs1, hs19, hdvd⟩ := exists_dvd_of_prime hp (by omega) (by omega)
  exact ⟨s, hs1, hs19, p, hp, hdvd, hpN⟩

/-! ### Units -/

/-- **The roots of `P_s` are not algebraic units**, for `s ≥ 1`: `P_s` is irreducible over `ℚ`
with constant term `-(16s - 1)`, which is not `±1`. -/
theorem not_isIntegral_inv_of_aeval_cubic {K : Type*} [Field K] [CharZero K] {s : ℕ}
    (hs : 1 ≤ s) {x : K} (hx : aeval x (cubic s) = 0) : ¬ IsIntegral ℤ x⁻¹ := by
  intro hinv
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [aeval_cubic] at hx
    have : (16 * (s : K) - 1) ≠ 0 := by
      have : (16 * (s : ℤ) - 1 : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    exact this (by linear_combination -hx)
  obtain ⟨k, hk⟩ := coeff_zero_dvd_pow (monic_cubic s) (irreducible_cubic hs) hx0 hx one_ne_zero
    (mem_integralClosureAway_of_isIntegral_int hinv)
  rw [coeff_zero_cubic, Nat.cast_one, one_pow, neg_dvd] at hk
  have := Int.le_of_dvd one_pos hk
  omega

/-! ### The block matrix -/

/-- The integer matrix `M_s = M₁ + (s - 1) u vᵀ` of the word `T₀T₁T₃ˢ` on the double plane, with
`u = (4, 3, 3)` and `v = (11, 6, 1)`. -/
def blockMatrix (s : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![39 + 44 * (s - 1), 20 + 24 * (s - 1), 3 + 4 * (s - 1);
     30 + 33 * (s - 1), 15 + 18 * (s - 1), 2 + 3 * (s - 1);
     36 + 33 * (s - 1), 20 + 18 * (s - 1), 3 + 3 * (s - 1)]

/-- `M_s` is the rank-one pencil `M₁ + (s - 1) u vᵀ`: an affine family in `s`, not the power of a
fixed matrix. -/
theorem blockMatrix_eq (s : ℤ) :
    blockMatrix s = blockMatrix 1 + (s - 1) • Matrix.vecMulVec ![4, 3, 3] ![11, 6, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMatrix, Matrix.vecMulVec] <;> ring

/-- `det M_s = 16s - 1`, affine in `s`. -/
theorem det_blockMatrix (s : ℤ) : (blockMatrix s).det = 16 * s - 1 := by
  rw [Matrix.det_fin_three]
  simp [blockMatrix]
  ring

/-- `tr M_s = 65s - 8`. -/
theorem trace_blockMatrix (s : ℤ) : (blockMatrix s).trace = 65 * s - 8 := by
  simp [blockMatrix, Matrix.trace, Fin.sum_univ_three]
  ring

/-- **`P_s` is the characteristic polynomial of `M_s`.** -/
theorem charpoly_blockMatrix (s : ℕ) : (blockMatrix s).charpoly = cubic s := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [blockMatrix, cubic]
  ring

end Polynomial.DoublePlane
