/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Matrix.SingularReduction
import K3Twists.NumberTheory.SUnitSpectral
import K3Twists.RingTheory.Polynomial.DoublePlaneCubics

/-!
# The letter-matrix obstruction on the double plane

On a K3 surface of Picard rank one with `H² = 2`, write `T_j` for the spherical twist by `𝒪(jH)`
and `λ(w)` for the point-mass multiplier of a word `w` in the six signed letters
`T₀^{±1}, T₁^{±1}, T₃^{±1}`. The study computes `λ(W_s)` for `W_s = T₀T₁T₃ˢ` as the Perron root of
the cubic `P_s` (`Polynomial.DoublePlane.cubic`), the characteristic polynomial of the block matrix
`M_s` (`Polynomial.DoublePlane.blockMatrix`). That computation needs the derived category of the
surface and twist functors, which the library does not have: here it is the hypothesis `hroot`,
"`λ(W_s)` is a root of `P_s`", for `s ≥ 1` with `s ≡ 1 (mod 19)`. Since `P_s` has exactly one
real root (`Polynomial.DoublePlane.eq_of_aeval_cubic`), the hypothesis already fixes `λ(W_s)` to be
the Perron root.

**Theorem** (`no_letter_matrices`). No complex matrices on the six signed letters, of any size and
possibly singular, have `ρ(A_{a₁} ⋯ A_{a_j}) = λ(a₁ ⋯ a_j)` for every spelling of every word, when
`λ` factors through a group containing the three twists. No hypothesis `λ(1) ≠ 0` is needed: the
empty word gives `λ(1) = ρ(1)`.

The proof is the S-unit theorem for spectral moduli (`Matrix.spectral_moduli_norms_divide_pow`):
`P_s` is irreducible with constant term `-(16s - 1)`, and the primes dividing the norms `16s - 1`,
`s ≡ 1 (mod 19)`, are not contained in any finite set. Singular letters are first replaced by
invertible ones (`Matrix.singular_reduction`); that step is the only one that uses the group and
the inverse letters.

For invertible letters much less is used (`no_invertible_letter_matrices`): only the positive
spellings `W_s` with `s ≡ 1 (mod 19)`, only that `λ(W_s)` is the modulus of some eigenvalue of
`A_{W_s}`, and only the entries of the inverse letter matrices.

The obstruction belongs to this alphabet: on two line bundles fixed `SL₂` letter matrices are
exact, and `M_s` itself is an exact integer model of the single word `W_s`, of determinant
`16s - 1`.

## The unit test

An integer matrix of determinant `±1` has eigenvalue moduli that are algebraic units
(`Matrix.isIntegral_norm_inv_of_mem_spectrum_of_isIntegral`), and `λ(W_s)` is not one
(`Polynomial.DoublePlane.not_isIntegral_inv_of_aeval_cubic`). So no unimodular exact linear model
reproduces `λ(W_s)` (`spectralRadius_ne_of_isUnit_det`): neither the action on the numerical
lattice, which is unimodular, nor a product of integer transvections. Given the lower bound
`ρ(W on N(X)) ≤ λ(W)` (Kikuta–Shiraishi–Takahashi; Ikeda), the inequality is strict
(`spectralRadius_lt_of_isUnit_det`). A non-unit excludes only unimodular models: `M_s` is an exact
integer model with determinant `16s - 1`.

## Main results

* `no_invertible_letter_matrices`, `no_letter_matrices`.
* `not_isIntegral_inv_of_root`, `spectralRadius_ne_of_isUnit_det`,
  `spectralRadius_lt_of_isUnit_det`.
-/

open Polynomial Polynomial.DoublePlane

namespace AlgebraicGeometry.K3.PicardRankOne.DoublePlane

/-- The six signed letters `T₀^{±1}, T₁^{±1}, T₃^{±1}`: the index `0, 1, 2` stands for
`T₀, T₁, T₃`, and `true` for the positive twist. -/
abbrev Letter := Fin 3 × Bool

/-- The spelling `W_s = T₀T₁T₃ˢ`, leftmost letter first. -/
def word (s : ℕ) : List Letter := [(0, true), (1, true)] ++ List.replicate s (2, true)

/-- **The obstruction for invertible letters.** Let `λ` be any real function on words such that
`λ(W_s)` is a root of `P_s` for `s ≥ 1`, `s ≡ 1 (mod 19)`. Then no invertible complex matrices on
the six letters have, for these `s`, an eigenvalue of `A_{W_s}` of modulus `λ(W_s)`. -/
theorem no_invertible_letter_matrices (lam : List Letter → ℝ)
    (hroot : ∀ s, 1 ≤ s → s % 19 = 1 → aeval (lam (word s)) (cubic s) = 0)
    {n : Type*} [Fintype n] [DecidableEq n] (A : Letter → Matrix n n ℂ)
    (hA : ∀ a, IsUnit (A a))
    (hW : ∀ s, 1 ≤ s → s % 19 = 1 → ∃ z ∈ spectrum ℂ ((word s).map A).prod, ‖z‖ = lam (word s)) :
    False :=
  Matrix.no_invertible_family A hA word (fun s => lam (word s)) cubic (fun s => 1 ≤ s ∧ s % 19 = 1)
    monic_cubic (fun s hs => irreducible_cubic_of_mod_nineteen hs.2)
    (fun s hs => hroot s hs.1 hs.2)
    (fun N hN => by
      obtain ⟨s, h1, h19, p, hp, hdvd, hpN⟩ := exists_prime_dvd_not_dvd N hN
      exact ⟨s, ⟨h1, h19⟩, p, hp, by rw [coeff_zero_cubic]; exact (dvd_neg).mpr hdvd, hpN⟩)
    (fun s hs => hW s hs.1 hs.2)

/-- The letters as elements of a group containing the twists `t 0 = T₀`, `t 1 = T₁`, `t 2 = T₃`. -/
def toGroup {G : Type*} [Group G] (t : Fin 3 → G) (a : Letter) : G :=
  if a.2 then t a.1 else (t a.1)⁻¹

lemma toGroup_inv {G : Type*} [Group G] (t : Fin 3 → G) (a : Letter) :
    toGroup t (a.1, !a.2) = (toGroup t a)⁻¹ := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [toGroup]

lemma prod_map_toGroup_word {G : Type*} [Group G] (t : Fin 3 → G) (s : ℕ) :
    ((word s).map (toGroup t)).prod = t 0 * t 1 * t 2 ^ s := by
  simp [word, toGroup, List.prod_replicate, mul_assoc]

/-- **No fixed letter matrices on the double plane.** Let `λ` factor through a group `G`
containing the three twists, with `λ(T₀T₁T₃ˢ)` a root of `P_s` for `s ≥ 1`, `s ≡ 1 (mod 19)`.
Then no complex matrices `A_a` on the six signed letters, of any size and possibly singular,
satisfy `ρ(A_{a₁} ⋯ A_{a_j}) = λ(a₁ ⋯ a_j)` for every word. -/
theorem no_letter_matrices {G : Type*} [Group G] (t : Fin 3 → G) (lam : G → ℝ)
    (hroot : ∀ s, 1 ≤ s → s % 19 = 1 → aeval (lam (t 0 * t 1 * t 2 ^ s)) (cubic s) = 0)
    {n : Type*} [Fintype n] [DecidableEq n] (A : Letter → Matrix n n ℂ) :
    ¬ ∀ w : List Letter,
      spectralRadius ℂ (w.map A).prod = ENNReal.ofReal (lam (w.map (toGroup t)).prod) := by
  intro h6
  obtain ⟨m, C, hCu, hC⟩ := Matrix.singular_reduction (toGroup t) (fun a => (a.1, !a.2))
    (toGroup_inv t) A lam h6
  refine no_invertible_letter_matrices (fun w => lam (w.map (toGroup t)).prod) (fun s hs h19 => ?_)
    C hCu (fun s hs h19 => ?_)
  · rw [prod_map_toGroup_word]
    exact hroot s hs h19
  · have hpos : 0 < lam ((word s).map (toGroup t)).prod := by
      rw [prod_map_toGroup_word]
      exact pos_of_aeval_cubic hs (hroot s hs h19)
    exact Matrix.exists_mem_spectrum_norm_eq _ hpos (hC (word s))

/-! ### The unit test -/

/-- For `s ≥ 1`, a real root `x` of `P_s` is not an algebraic unit: `x⁻¹` is not an algebraic
integer. -/
theorem not_isIntegral_inv_of_root {s : ℕ} (hs : 1 ≤ s) {x : ℝ} (hx : aeval x (cubic s) = 0) :
    ¬ IsIntegral ℤ ((x : ℂ))⁻¹ := by
  have hxC : aeval (x : ℂ) (cubic s) = 0 := by
    rw [← Complex.coe_algebraMap, aeval_algebraMap_apply, hx, map_zero]
  exact not_isIntegral_inv_of_aeval_cubic hs hxC

/-- **No unimodular exact linear model.** For `s ≥ 1` and a real root `x` of `P_s`, no integer
matrix of determinant `±1` has spectral radius `x`. -/
theorem spectralRadius_ne_of_isUnit_det {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℤ} (hM : IsUnit M.det) {s : ℕ} (hs : 1 ≤ s) {x : ℝ}
    (hx : aeval x (cubic s) = 0) :
    spectralRadius ℂ (M.map (Int.cast : ℤ → ℂ)) ≠ ENNReal.ofReal x := by
  intro h
  obtain ⟨z, hz, hzx⟩ := Matrix.exists_mem_spectrum_norm_eq _ (pos_of_aeval_cubic hs hx) h
  exact Matrix.norm_ne_of_not_isIntegral_inv hM (not_isIntegral_inv_of_root hs hx) hz hzx

/-- **The lower bound is strict.** For `s ≥ 1`, a real root `x` of `P_s` and an integer matrix `M`
of determinant `±1` with `ρ(M) ≤ x` (for the action of `W_s` on the numerical lattice, the lower
bound of Kikuta–Shiraishi–Takahashi and Ikeda), the inequality is strict. -/
theorem spectralRadius_lt_of_isUnit_det {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℤ} (hM : IsUnit M.det) {s : ℕ} (hs : 1 ≤ s) {x : ℝ}
    (hx : aeval x (cubic s) = 0)
    (hle : spectralRadius ℂ (M.map (Int.cast : ℤ → ℂ)) ≤ ENNReal.ofReal x) :
    spectralRadius ℂ (M.map (Int.cast : ℤ → ℂ)) < ENNReal.ofReal x :=
  lt_of_le_of_ne hle (spectralRadius_ne_of_isUnit_det hM hs hx)

end AlgebraicGeometry.K3.PicardRankOne.DoublePlane
