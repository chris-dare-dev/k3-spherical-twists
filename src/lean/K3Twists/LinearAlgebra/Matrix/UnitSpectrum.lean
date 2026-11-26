/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RingTheory.IntegralClosure.Away
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Eigenvalues and eigenvalue moduli of matrices with integral entries

For a complex matrix `M` whose entries lie in a subring `R ⊆ ℂ`, every eigenvalue is integral
over `R`: it is a root of the monic characteristic polynomial, which has coefficients in `R`.
With the entries of `M⁻¹` and of the complex conjugate `(M̄)⁻¹` in `R`, the inverse modulus
`|z|⁻¹` of every eigenvalue is integral over `R`, since `|z|⁻² = z⁻¹ z̄⁻¹`.

Taking for `R` the algebraic integers gives the **unit test**: if the entries of `M` and of `M⁻¹`
are algebraic integers (an integer matrix with determinant `±1`, or the specialization of a
matrix over `ℤ[q, q⁻¹]` with unit determinant at an algebraic unit `q`), every eigenvalue and every
eigenvalue modulus is an algebraic unit. So a real number `x` with `x⁻¹` not an algebraic integer
is the modulus of no eigenvalue of such a matrix.

## Main results

* `Matrix.isIntegral_of_mem_spectrum`: eigenvalues are integral over the ring of entries.
* `Matrix.inv_mem_spectrum_inv`, `Matrix.map_mem_spectrum`: eigenvalues of `M⁻¹` and of the
  image of `M` under a ring endomorphism.
* `Matrix.isIntegral_norm_inv_of_mem_spectrum`: the inverse modulus is integral over `R`.
* `Matrix.isIntegral_norm_of_mem_spectrum_of_isIntegral`,
  `Matrix.isIntegral_norm_inv_of_mem_spectrum_of_isIntegral`: the unit test.
* `Matrix.norm_ne_of_not_isIntegral_inv`: a real number whose inverse is not an algebraic integer
  is not the modulus of an eigenvalue of an integer matrix with determinant `±1`.
-/

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Entries

variable {K : Type*} [Field K]

/-- **Eigenvalues are integral over the ring of entries.** If every entry of `M` lies in the
subring `R`, every eigenvalue of `M` is integral over `R`: it is a root of the characteristic
polynomial of `M` read over `R`. -/
theorem isIntegral_of_mem_spectrum {R : Subalgebra ℤ K} {M : Matrix n n K}
    (hM : ∀ i j, M i j ∈ R) {z : K} (hz : z ∈ spectrum K M) : IsIntegral R z := by
  rw [mem_spectrum_iff_isRoot_charpoly] at hz
  let B : Matrix n n R := fun i j => ⟨M i j, hM i j⟩
  have hB : B.map (algebraMap R K) = M := by ext i j; rfl
  refine ⟨B.charpoly, B.charpoly_monic, ?_⟩
  rw [← hB, charpoly_map] at hz
  simpa [IsRoot.def, eval_map] using hz

/-- The eigenvalues of `M⁻¹` are the inverses of those of `M`, for invertible `M`. -/
lemma inv_mem_spectrum_inv {M : Matrix n n K} (hM : IsUnit M) {z : K} (hz : z ∈ spectrum K M) :
    z⁻¹ ∈ spectrum K M⁻¹ := by
  obtain ⟨u, rfl⟩ := hM
  rw [← coe_units_inv]
  exact spectrum.inv₀_mem_inv_iff.mpr hz

/-- A ring endomorphism `σ` maps the eigenvalues of `M` to eigenvalues of `M.map σ`. -/
lemma map_mem_spectrum (σ : K →+* K) {M : Matrix n n K} {z : K} (hz : z ∈ spectrum K M) :
    σ z ∈ spectrum K (M.map σ) := by
  rw [mem_spectrum_iff_isRoot_charpoly] at hz ⊢
  rw [charpoly_map, IsRoot.def, eval_map, eval₂_at_apply, hz.eq_zero, map_zero]

/-- An eigenvalue of an invertible matrix is nonzero. -/
lemma ne_zero_of_mem_spectrum {M : Matrix n n K} (hM : IsUnit M) {z : K}
    (hz : z ∈ spectrum K M) : z ≠ 0 := by
  rintro rfl
  exact (spectrum.zero_notMem_iff K).2 hM hz

/-- Products of matrices map under a ring endomorphism letter by letter. -/
lemma list_prod_map_map {ι : Type*} (σ : K →+* K) (A : ι → Matrix n n K) (w : List ι) :
    ((w.map A).prod).map σ = (w.map fun a => (A a).map σ).prod := by
  have := map_list_prod (σ.mapMatrix (m := n)) (w.map A)
  simpa [List.map_map, Function.comp_def] using this

/-- A product of invertible matrices is invertible. -/
lemma isUnit_list_prod_map {ι : Type*} (A : ι → Matrix n n K) (hA : ∀ a, IsUnit (A a))
    (w : List ι) : IsUnit (w.map A).prod := by
  induction w with
  | nil => simp
  | cons a w ih => simpa [List.map_cons, List.prod_cons] using (hA a).mul ih

/-- The entries of an inverse product lie in `R` if those of the inverse letters do. -/
lemma list_prod_inv_mem {ι : Type*} {R : Subalgebra ℤ K} (A : ι → Matrix n n K)
    (h : ∀ a i j, (A a)⁻¹ i j ∈ R) (w : List ι) : ∀ i j, ((w.map A).prod)⁻¹ i j ∈ R := by
  induction w with
  | nil =>
    intro i j
    rw [List.map_nil, List.prod_nil, inv_one, Matrix.one_apply]
    split_ifs
    exacts [R.one_mem, R.zero_mem]
  | cons a w ih =>
    intro i j
    rw [List.map_cons, List.prod_cons, mul_inv_rev, Matrix.mul_apply]
    exact R.sum_mem fun k _ => R.mul_mem (ih i k) (h a k j)

end Entries

/-- The inverse of the image of a matrix with unit determinant under a ring homomorphism is the
image of its inverse. -/
lemma inv_map_eq_map_inv {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {M : Matrix n n R} (hM : IsUnit M.det) : (M.map f)⁻¹ = (M⁻¹).map f := by
  apply inv_eq_left_inv
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, nonsing_inv_mul M hM,
    map_one]

section Complex

open ComplexConjugate

/-- **The inverse modulus is integral over the entries.** If `M` is invertible and the entries of
`M⁻¹` and of `(M̄)⁻¹` lie in `R`, then `|z|⁻¹` is integral over `R` for every eigenvalue `z`:
`|z|⁻² = z⁻¹ z̄⁻¹`, and `z⁻¹`, `z̄⁻¹` are eigenvalues of `M⁻¹`, `(M̄)⁻¹`. -/
theorem isIntegral_norm_inv_of_mem_spectrum {R : Subalgebra ℤ ℂ} {M : Matrix n n ℂ}
    (hM : IsUnit M) (hinv : ∀ i j, M⁻¹ i j ∈ R) (hinv' : ∀ i j, (M.map conj)⁻¹ i j ∈ R)
    {z : ℂ} (hz : z ∈ spectrum ℂ M) : IsIntegral R (((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have hM' : IsUnit (M.map conj) := hM.map ((starRingEnd ℂ).mapMatrix (m := n))
  have hz1 : IsIntegral R z⁻¹ := isIntegral_of_mem_spectrum hinv (inv_mem_spectrum_inv hM hz)
  have hz2 : IsIntegral R (conj z)⁻¹ :=
    isIntegral_of_mem_spectrum hinv' (inv_mem_spectrum_inv hM' (map_mem_spectrum _ hz))
  have hsq : (((‖z‖ : ℝ) : ℂ))⁻¹ ^ 2 = z⁻¹ * (conj z)⁻¹ := by
    rw [← mul_inv, Complex.mul_conj', inv_pow]
  exact IsIntegral.of_pow two_pos (hsq ▸ hz1.mul hz2)

/-- Complex conjugation maps algebraic integers to algebraic integers. -/
lemma isIntegral_conj {x : ℂ} (hx : IsIntegral ℤ x) : IsIntegral ℤ (conj x) :=
  hx.map (starRingEnd ℂ).toIntAlgHom

/-- **The unit test, moduli.** If the entries of `M` are algebraic integers, so is the modulus of
every eigenvalue. -/
theorem isIntegral_norm_of_mem_spectrum_of_isIntegral {M : Matrix n n ℂ}
    (hM : ∀ i j, IsIntegral ℤ (M i j)) {z : ℂ} (hz : z ∈ spectrum ℂ M) :
    IsIntegral ℤ (((‖z‖ : ℝ) : ℂ)) := by
  have h1 : IsIntegral ℤ z :=
    isIntegral_trans z (isIntegral_of_mem_spectrum (R := integralClosure ℤ ℂ) hM hz)
  have h2 : IsIntegral ℤ (conj z) := isIntegral_conj h1
  have hsq : (((‖z‖ : ℝ) : ℂ)) ^ 2 = z * conj z := by rw [Complex.mul_conj']
  exact IsIntegral.of_pow two_pos (hsq ▸ h1.mul h2)

/-- **The unit test, inverse moduli.** If `M` is invertible and the entries of `M⁻¹` are algebraic
integers, the inverse modulus of every eigenvalue is an algebraic integer. -/
theorem isIntegral_norm_inv_of_mem_spectrum_of_isIntegral {M : Matrix n n ℂ} (hM : IsUnit M)
    (hinv : ∀ i j, IsIntegral ℤ (M⁻¹ i j)) {z : ℂ} (hz : z ∈ spectrum ℂ M) :
    IsIntegral ℤ (((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have hinv' : ∀ i j, (M.map conj)⁻¹ i j ∈ integralClosure ℤ ℂ := by
    have hconj : (M.map conj)⁻¹ = (M⁻¹).map conj :=
      inv_map_eq_map_inv (starRingEnd ℂ) ((isUnit_iff_isUnit_det M).1 hM)
    intro i j
    rw [hconj, map_apply]
    exact isIntegral_conj (hinv i j)
  exact isIntegral_trans _ (isIntegral_norm_inv_of_mem_spectrum (R := integralClosure ℤ ℂ) hM
    hinv hinv' hz)

/-- **No unimodular integer model.** If `x⁻¹` is not an algebraic integer, `x` is not the
modulus of an eigenvalue of an integer matrix with determinant `±1`. -/
theorem norm_ne_of_not_isIntegral_inv {M : Matrix n n ℤ} (hM : IsUnit M.det) {x : ℝ}
    (hx : ¬ IsIntegral ℤ ((x : ℂ))⁻¹) {z : ℂ} (hz : z ∈ spectrum ℂ (M.map (Int.cast : ℤ → ℂ))) :
    ‖z‖ ≠ x := by
  rintro rfl
  set M' : Matrix n n ℂ := M.map (Int.castRingHom ℂ)
  have hM' : IsUnit M' := by
    rw [isUnit_iff_isUnit_det, show M' = (Int.castRingHom ℂ).mapMatrix M from rfl,
      ← RingHom.map_det]
    exact hM.map _
  have hinv : ∀ i j, IsIntegral ℤ (M'⁻¹ i j) := by
    intro i j
    rw [inv_map_eq_map_inv (Int.castRingHom ℂ) hM, map_apply]
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := M⁻¹ i j)
  exact hx (isIntegral_norm_inv_of_mem_spectrum_of_isIntegral hM' hinv hz)

end Complex

end Matrix
