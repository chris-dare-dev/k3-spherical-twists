/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.LetterObstruction

/-!
# Models for the letter-matrix obstruction

* The hypotheses of `no_letter_matrices` are satisfiable, so the theorem is not vacuous: in
  `G = Multiplicative ℤ` with `t = (1, 1, 1)` the words `T₀T₁T₃ˢ` go to `s`, and `λ(s)` can be
  taken to be the real root of `P_s`.
* For each single `s` the cubic is realized: the real root of `P_s` is an eigenvalue of the
  integer matrix `M_s`, of determinant `16s - 1`. The obstruction is about one assignment of
  matrices to the letters for all `s` at once.
* The S-unit theorem with an explicit `N`: integer letters of determinant `±1` have `N = 1`, so an
  algebraic spectral modulus of their products has a unit norm.
-/

open Polynomial Polynomial.DoublePlane AlgebraicGeometry.K3.PicardRankOne.DoublePlane

/-- The hypotheses of `no_letter_matrices` are satisfiable, for every `s ≥ 1`. -/
example : ∃ (t : Fin 3 → Multiplicative ℤ) (lam : Multiplicative ℤ → ℝ),
    ∀ s, 1 ≤ s → aeval (lam (t 0 * t 1 * t 2 ^ s)) (cubic s) = 0 := by
  classical
  refine ⟨![1, 1, Multiplicative.ofAdd 1], fun g => if h : 1 ≤ Multiplicative.toAdd g then
    (exists_aeval_cubic_eq_zero (s := (Multiplicative.toAdd g).toNat) (by omega)).choose else 1,
    fun s hs => ?_⟩
  have e : (![1, 1, Multiplicative.ofAdd 1] : Fin 3 → Multiplicative ℤ) 0 *
      (![1, 1, Multiplicative.ofAdd 1] : Fin 3 → Multiplicative ℤ) 1 *
      (![1, 1, Multiplicative.ofAdd 1] : Fin 3 → Multiplicative ℤ) 2 ^ s =
      Multiplicative.ofAdd (s : ℤ) := by
    simp [← ofAdd_nsmul]
  rw [e]
  have hs1 : 1 ≤ Multiplicative.toAdd (Multiplicative.ofAdd (s : ℤ)) := by simp; omega
  dsimp only
  rw [dite_eq_left hs1]
  have := (exists_aeval_cubic_eq_zero (s := (Multiplicative.toAdd
    (Multiplicative.ofAdd (s : ℤ))).toNat) (by simp; omega)).choose_spec
  simpa using this

/-- The real root of `P_s` is an eigenvalue of the integer matrix `M_s`. -/
example {s : ℕ} (hs : 1 ≤ s) : ∃ x : ℝ, aeval x (cubic s) = 0 ∧
    (x : ℂ) ∈ spectrum ℂ ((blockMatrix s).map (Int.cast : ℤ → ℂ)) := by
  obtain ⟨x, hx⟩ := exists_aeval_cubic_eq_zero hs
  refine ⟨x, hx, ?_⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    show (blockMatrix s).map (Int.cast : ℤ → ℂ) = (blockMatrix s).map (Int.castRingHom ℂ) from rfl,
    Matrix.charpoly_map, charpoly_blockMatrix, IsRoot.def, eval_map, ← algebraMap_int_eq,
    ← aeval_def]
  rw [← Complex.coe_algebraMap, aeval_algebraMap_apply, hx, map_zero]

/-- Integer letters of determinant `±1` have the S-unit theorem with `N = 1`: an algebraic
spectral modulus of their products is a root of an irreducible monic `P` with `P(0) = ±1`. -/
example {ι n : Type*} [Fintype n] [DecidableEq n] (A : ι → Matrix n n ℤ)
    (hA : ∀ a, IsUnit (A a).det) (w : List ι) {z : ℂ}
    (hz : z ∈ spectrum ℂ (w.map fun a => (A a).map (Int.castRingHom ℂ)).prod) {P : ℤ[X]}
    (hPm : P.Monic) (hPirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hroot : aeval ((‖z‖ : ℝ) : ℂ) P = 0) : IsUnit (P.coeff 0) := by
  have hAu : ∀ a, IsUnit ((A a).map (Int.castRingHom ℂ)) := fun a => by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hA a).map _
  have hinv : ∀ a i j, ((A a).map (Int.castRingHom ℂ))⁻¹ i j ∈ integralClosureAway 1 ℂ := by
    intro a i j
    rw [Matrix.inv_map_eq_map_inv _ (hA a), Matrix.map_apply]
    exact mem_integralClosureAway_of_isIntegral_int
      (by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (A a)⁻¹ i j))
  obtain ⟨k, hk⟩ := Matrix.spectral_moduli_norms_divide_pow_of_mem _ hAu one_ne_zero hinv w hz
    hPm hPirr hroot
  rw [Nat.cast_one, one_pow] at hk
  exact isUnit_of_dvd_one hk
