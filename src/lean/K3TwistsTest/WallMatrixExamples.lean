/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.WallMatrix
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.WallMatrix
import K3Twists.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.Matrix.Cartan.Realisation

/-!
# Wall matrices: counterexamples and examples

Regression tests for the wall-matrix modules.

**Pairwise pairings do not decide anisotropy.** For two spheres, a pairing `g ≥ 3` excludes an
isotropic sum (`Quiver.Kronecker.noIsotropicSphereSum_cartanMatrix`). For three spheres with every
pairwise pairing at least `3` it does not: among the `35` triples of pairings in `[3, 7]`, a
computation outside Lean (Hilbert symbols and a search for nonnegative isotropic vectors, agreeing
with each other) finds exactly four with an isotropic sum,

  `(4, 5, 6)` with `(4, 35, 3)`, `(5, 5, 5)` with `(3, 5, 41)`, `(5, 6, 7)` with `(5, 4, 59)`,
  `(6, 6, 7)` with `(3, 4, 47)`,

and the other `31` anisotropic. The four isotropic sums are checked below by `decide`; the
anisotropy of the other `31` triples is not checked in Lean.

**Anisotropy is not closed under orthogonal sums.** The Mukai Gram matrix
`[-2] ⊕ [[-2, 3], [3, -2]]` (one sphere, and two spheres of pairing `3`) has anisotropic blocks,
but its sum has the isotropic vector `(1, 1, 1)`: `-2 - 2 - 2 + 2·3 = 0`.

Built by `lake test`.
-/

namespace K3TwistsTest.WallMatrixExamples

open Matrix Quiver.Kronecker

/-! ### Three spheres with an isotropic sum -/

/-- A Kronecker pair of pairing two and a third sphere: `(1, 1, 1)` is isotropic. -/
example : ¬(!![2, -2, -1; -2, 2, 0; -1, 0, 2] : Matrix (Fin 3) (Fin 3) ℤ).NoIsotropicSphereSum :=
  not_noIsotropicSphereSum ![1, 1, 1] (by decide) (by decide) (by decide) (by decide)

/-- Pairings `4, 0, 1`: `(1, 1, 2)` is isotropic. -/
example : ¬(!![2, -4, 0; -4, 2, -1; 0, -1, 2] : Matrix (Fin 3) (Fin 3) ℤ).NoIsotropicSphereSum :=
  not_noIsotropicSphereSum ![1, 1, 2] (by decide) (by decide) (by decide) (by decide)

/-- Pairings `(4, 5, 6)`: `(4, 35, 3)` is isotropic. -/
theorem ex_four_five_six :
    ¬(!![2, -4, -5; -4, 2, -6; -5, -6, 2] : Matrix (Fin 3) (Fin 3) ℤ).NoIsotropicSphereSum :=
  not_noIsotropicSphereSum ![4, 35, 3] (by decide) (by decide) (by decide) (by decide)

/-- Pairings `(5, 5, 5)`: `(3, 5, 41)` is isotropic. -/
theorem ex_five_five_five :
    ¬(!![2, -5, -5; -5, 2, -5; -5, -5, 2] : Matrix (Fin 3) (Fin 3) ℤ).NoIsotropicSphereSum :=
  not_noIsotropicSphereSum ![3, 5, 41] (by decide) (by decide) (by decide) (by decide)

/-- Pairings `(5, 6, 7)`: `(5, 4, 59)` is isotropic. -/
example : ¬(!![2, -5, -6; -5, 2, -7; -6, -7, 2] : Matrix (Fin 3) (Fin 3) ℤ).NoIsotropicSphereSum :=
  not_noIsotropicSphereSum ![5, 4, 59] (by decide) (by decide) (by decide) (by decide)

/-- Pairings `(6, 6, 7)`: `(3, 4, 47)` is isotropic. -/
example : ¬(!![2, -6, -6; -6, 2, -7; -6, -7, 2] : Matrix (Fin 3) (Fin 3) ℤ).NoIsotropicSphereSum :=
  not_noIsotropicSphereSum ![3, 4, 47] (by decide) (by decide) (by decide) (by decide)

example := pairwise_three_not_sufficient

/-! ### An orthogonal sum of anisotropic blocks -/

/-- The wall matrix of `[-2] ⊕ [[-2, 3], [3, -2]]` is its negative. -/
example : -(!![-2, 0, 0; 0, -2, 3; 0, 3, -2] : Matrix (Fin 3) (Fin 3) ℤ) =
    !![2, 0, 0; 0, 2, -3; 0, -3, 2] := by
  decide

/-- The single sphere is anisotropic. -/
example : (!![2] : Matrix (Fin 1) (Fin 1) ℤ).NoIsotropicSphereSum := by
  intro a _ ha _ h
  apply ha
  funext i
  fin_cases i
  simp [dotProduct, mulVec] at h
  simpa using h

/-- Two spheres of pairing `3` are anisotropic. -/
example : (cartanMatrix (3 : ℤ)).NoIsotropicSphereSum :=
  noIsotropicSphereSum_cartanMatrix (by norm_num)

/-- Their orthogonal sum has the isotropic sum `(1, 1, 1)`. -/
theorem isotropic_block :
    ¬(!![2, 0, 0; 0, 2, -3; 0, -3, 2] : Matrix (Fin 3) (Fin 3) ℤ).NoIsotropicSphereSum :=
  not_noIsotropicSphereSum ![1, 1, 1] (by decide) (by decide) (by decide) (by decide)

/-! ### Two spheres -/

example : ¬(cartanMatrix (2 : ℤ)).NoIsotropicSphereSum :=
  not_noIsotropicSphereSum_cartanMatrix_two

/-- Off the integers, indefinite does not mean anisotropic: at `g = 5/2` the rank-two wall is
negative at `(1, 1)` and isotropic at `(2, 1)`. -/
example : (∃ x : Fin 2 → ℚ, x ⬝ᵥ cartanMatrix (5 / 2 : ℚ) *ᵥ x < 0) ∧
    ∃ x : Fin 2 → ℚ, x ≠ 0 ∧ x ⬝ᵥ cartanMatrix (5 / 2 : ℚ) *ᵥ x = 0 := by
  refine ⟨⟨![1, 1], ?_⟩, ⟨![2, 1], fun h => by simpa using congr_fun h 0, ?_⟩⟩
  · rw [dotProduct_mulVec_cartanMatrix]; norm_num
  · rw [dotProduct_mulVec_cartanMatrix]; norm_num

/-! ### The density statement is not vacuous

Every hypothesis of `Matrix.ExistsPosIsotropicOfIsotropic` holds for the rank-two wall at
`g = 5/2`, and so does its conclusion, with the positive integer vector `(2, 1)`. -/

example : (cartanMatrix (5 / 2 : ℚ)).IsSymm ∧ (cartanMatrix (5 / 2 : ℚ)).IsZMatrix ∧
    (∀ i, 0 < cartanMatrix (5 / 2 : ℚ) i i) ∧ (cartanMatrix (5 / 2 : ℚ)).det ≠ 0 ∧
    (∃ x : Fin 2 → ℚ, (∀ i, 0 < x i) ∧ x ⬝ᵥ cartanMatrix (5 / 2 : ℚ) *ᵥ x < 0) ∧
    (∃ v : Fin 2 → ℚ, v ≠ 0 ∧ v ⬝ᵥ cartanMatrix (5 / 2 : ℚ) *ᵥ v = 0) ∧
    ∃ a : Fin 2 → ℤ, (∀ i, 0 < a i) ∧
      (fun i => (a i : ℚ)) ⬝ᵥ cartanMatrix (5 / 2 : ℚ) *ᵥ (fun i => (a i : ℚ)) = 0 := by
  refine ⟨cartanMatrix_isSymm _, isZMatrix_cartanMatrix (by norm_num), fun i => ?_, ?_,
    ⟨![1, 1], fun i => by fin_cases i <;> norm_num, ?_⟩,
    ⟨![2, 1], fun h => by simpa using congr_fun h 0, ?_⟩, ⟨![2, 1], fun i => ?_, ?_⟩⟩
  · fin_cases i <;> simp [cartanMatrix]
  · simp [cartanMatrix, det_fin_two]; norm_num
  · rw [dotProduct_mulVec_cartanMatrix]; norm_num
  · rw [dotProduct_mulVec_cartanMatrix]; norm_num
  · fin_cases i <;> norm_num
  · rw [dotProduct_mulVec_cartanMatrix]; norm_num

/-! ### Cartan matrices -/

/-- `E₈` is a finite-type Cartan matrix, so Mathlib builds its root system. -/
example : (CartanMatrix.isFiniteCartan_E_eight.toRootPairing ℚ).IsRootSystem :=
  inferInstance

/-- The inverse of the `E₈` Cartan matrix is nonnegative. -/
example : ∀ i j, 0 ≤ ((CartanMatrix.E 8).map ((↑) : ℤ → ℚ))⁻¹ i j := by
  have hS := CartanMatrix.E_isSymm 8
  have hZ := (CartanMatrix.isSimplyLaced_E 8).isZMatrix
  have hPD : (CartanMatrix.E 8).PosDef := (hZ.posDef_iff_int_certificate hS).mpr
    ⟨![92, 136, 182, 270, 220, 168, 114, 58], by decide,
      fun i => by simp [CartanMatrix.E_eight_mulVec_certificate]⟩
  exact (hZ.map_intCast.inv_nonneg_of_posDef (hS.map _) (hS.posDef_map_intCast_iff.mpr hPD)).1

/-- Positive weights for a finite-type Cartan matrix. -/
example : ∃ p : Fin 8 → ℤ, (∀ i, 0 < p i) ∧ ∀ i, 0 < (CartanMatrix.E 8 *ᵥ p) i :=
  CartanMatrix.isFiniteCartan_E_eight.exists_certificate

/-! ### Walls of the library -/

/-- The curve wall recovers `selfPairing_wallClass_eq_kroneckerForm` from the Tits identity. -/
example (a b : ℤ) :
    Mukai.selfPairing AlgebraicGeometry.K3.EllipticWithSection.intersection
      (AlgebraicGeometry.K3.EllipticWithSection.wallClass a b) = -2 * kroneckerForm 2 a b := by
  rw [AlgebraicGeometry.K3.EllipticWithSection.selfPairing_wallClass_eq_neg_dotProduct,
    dotProduct_mulVec_cartanMatrix_eq_kroneckerForm]
  ring

/-- At `d = 1` the wall of `𝒪_X` and `𝒪_X(-H)[1]` has pairing `3`. -/
example : AlgebraicGeometry.K3.PicardRankOne.wallMatrix (1 : ℤ)
    ![MukaiVector.lineBundle 1 0, -MukaiVector.lineBundle 1 (-1)] = cartanMatrix 3 := by
  rw [(AlgebraicGeometry.K3.PicardRankOne.structureSheaf_shift_wall le_rfl).1]
  norm_num

end K3TwistsTest.WallMatrixExamples
