/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Matrix.ZMatrix.Integer
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Finite and affine Cartan matrices from certificates

Mathlib's `Matrix.IsFiniteCartan` asks for a positive diagonal `d` with `diag(d) M` positive
definite over `ℤ`. With the integer M-matrix criterion of
`K3Twists.LinearAlgebra.Matrix.ZMatrix.Integer` this is decided by one integer vector:

* `Matrix.isFiniteCartan_of_certificate`: a symmetric integer Z-matrix with diagonal `2` and a
  certificate `p ≥ 0`, `Ap ≥ 1`, is a finite-type Cartan matrix (no determinant, no minors);
* `Matrix.IsFiniteCartan.exists_certificate`: conversely every finite-type Cartan matrix, also
  a non-symmetric one, has positive integer weights `p` with `Mp > 0`;
* `CartanMatrix.isFiniteCartan_E_six`, `isFiniteCartan_E_seven`, `isFiniteCartan_E_eight`: the
  certificate is `p = 2ρ^∨`, the sum of the positive coroots in the basis of simple coroots, with
  `Ap = 2·𝟙` exactly (Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, Plates V–VII);
* `CartanMatrix.E_nine_mulVec_null`: Mathlib's `E 9`, which continues the `E` series, is the
  affine `Ẽ₈`; its null vector `δ` is the highest root of `E₈` with `1` at the extra node, so it
  has no certificate (`CartanMatrix.E_nine_no_certificate`), is positive semidefinite and not
  positive definite (`CartanMatrix.E_nine_posSemidef_and_not_posDef`), and its isotropic integer
  vectors are `ℤδ` (`CartanMatrix.E_nine_isotropic_eq_zsmul`).

The `Z` sign pattern of a simply-laced matrix is read off Mathlib's `Matrix.IsSimplyLaced`
(`Matrix.IsSimplyLaced.isZMatrix`).
-/

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A simply-laced matrix (off-diagonal entries `0` or `-1`) is a Z-matrix. -/
lemma IsSimplyLaced.isZMatrix {ι : Type*} {A : Matrix ι ι ℤ} (h : A.IsSimplyLaced) :
    A.IsZMatrix := fun i j hij => by
  rcases h hij with h | h <;> simp [h]

/-- **Finite type from a certificate.** A symmetric integer Z-matrix with diagonal `2` and a
nonnegative integer vector `p` with `Ap ≥ 1` is a finite-type Cartan matrix in Mathlib's sense
(with `d = 1`). -/
theorem isFiniteCartan_of_certificate {A : Matrix ι ι ℤ} (hA : A.IsSymm) (hd : ∀ i, A i i = 2)
    (hZ : A.IsZMatrix) {p : ι → ℤ} (hp : ∀ i, 0 ≤ p i) (hAp : ∀ i, 1 ≤ (A *ᵥ p) i) :
    A.IsFiniteCartan := by
  have hPD : A.PosDef :=
    (hZ.posDef_iff_int_certificate hA).mpr ⟨p, hZ.int_certificate_pos hp hAp, hAp⟩
  exact ⟨hd, hZ, fun i j => by rw [hA.apply i j], ⟨1, fun _ => one_pos, by simpa using hPD⟩⟩

/-- **Positive weights for every finite-type Cartan matrix.** If `M` is a finite-type Cartan
matrix, symmetric or not, some `p ∈ ℤ^ι` with `p > 0` has `Mp > 0`. The symmetrization
`diag(d) M` is a positive definite symmetric Z-matrix, so it has an integer certificate. -/
theorem IsFiniteCartan.exists_certificate {M : Matrix ι ι ℤ} (hM : M.IsFiniteCartan) :
    ∃ p : ι → ℤ, (∀ i, 0 < p i) ∧ ∀ i, 0 < (M *ᵥ p) i := by
  obtain ⟨d, hd, hdM⟩ := hM.exists_posDef
  have hS : (diagonal d * M).IsSymm := isHermitian_iff_isSymm.mp hdM.isHermitian
  have hZ : (diagonal d * M).IsZMatrix := fun i j hij => by
    rw [diagonal_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hd i).le (hM.offDiag_nonpos i j hij)
  obtain ⟨p, hp, hAp⟩ := (hZ.posDef_iff_int_certificate hS).mp hdM
  refine ⟨p, hp, fun i => ?_⟩
  have h := hAp i
  rw [← mulVec_mulVec, mulVec_diagonal] at h
  by_contra hneg
  push Not at hneg
  nlinarith [hd i]

end Matrix

namespace CartanMatrix

open Matrix

/-- `2ρ^∨` for `E₆` (Bourbaki's labels, as in Mathlib's `E 6`): `E₆ (2ρ^∨) = 2·𝟙`. -/
theorem E_six_mulVec_certificate : E 6 *ᵥ ![16, 22, 30, 42, 30, 16] = fun _ => 2 := by
  rw [E_six_eq]; decide

/-- `2ρ^∨` for `E₇`: `E₇ (2ρ^∨) = 2·𝟙`. -/
theorem E_seven_mulVec_certificate : E 7 *ᵥ ![34, 49, 66, 96, 75, 52, 27] = fun _ => 2 := by
  rw [E_seven_eq]; decide

/-- `2ρ^∨` for `E₈`: `E₈ (2ρ^∨) = 2·𝟙`. -/
theorem E_eight_mulVec_certificate :
    E 8 *ᵥ ![92, 136, 182, 270, 220, 168, 114, 58] = fun _ => 2 := by
  rw [E_eight_eq]; decide

/-- `E₆` is a finite-type Cartan matrix, from its certificate `2ρ^∨`. -/
theorem isFiniteCartan_E_six : (E 6).IsFiniteCartan :=
  isFiniteCartan_of_certificate (E_isSymm 6) (E_diag 6) (isSimplyLaced_E 6).isZMatrix
    (p := ![16, 22, 30, 42, 30, 16]) (by decide) fun i => by simp [E_six_mulVec_certificate]

/-- `E₇` is a finite-type Cartan matrix, from its certificate `2ρ^∨`. -/
theorem isFiniteCartan_E_seven : (E 7).IsFiniteCartan :=
  isFiniteCartan_of_certificate (E_isSymm 7) (E_diag 7) (isSimplyLaced_E 7).isZMatrix
    (p := ![34, 49, 66, 96, 75, 52, 27]) (by decide) fun i => by simp [E_seven_mulVec_certificate]

/-- `E₈` is a finite-type Cartan matrix, from its certificate `2ρ^∨`. -/
theorem isFiniteCartan_E_eight : (E 8).IsFiniteCartan :=
  isFiniteCartan_of_certificate (E_isSymm 8) (E_diag 8) (isSimplyLaced_E 8).isZMatrix
    (p := ![92, 136, 182, 270, 220, 168, 114, 58]) (by decide)
    fun i => by simp [E_eight_mulVec_certificate]

/-- `E 9` is the matrix of the affine diagram `Ẽ₈`: the `E₈` diagram with a ninth node joined to
the end of its long arm. -/
theorem E_nine_eq :
    E 9 = !![ 2,  0, -1,  0,  0,  0,  0,  0,  0;
              0,  2,  0, -1,  0,  0,  0,  0,  0;
             -1,  0,  2, -1,  0,  0,  0,  0,  0;
              0, -1, -1,  2, -1,  0,  0,  0,  0;
              0,  0,  0, -1,  2, -1,  0,  0,  0;
              0,  0,  0,  0, -1,  2, -1,  0,  0;
              0,  0,  0,  0,  0, -1,  2, -1,  0;
              0,  0,  0,  0,  0,  0, -1,  2, -1;
              0,  0,  0,  0,  0,  0,  0, -1,  2] := by
  decide

/-- **The null vector of `Ẽ₈`**: the labels `2, 3, 4, 6, 5, 4, 3, 2` of the highest root of
`E₈`, and `1` at the extra node. -/
theorem E_nine_mulVec_null : E 9 *ᵥ ![2, 3, 4, 6, 5, 4, 3, 2, 1] = 0 := by
  decide

/-- **The affine obstruction for `Ẽ₈`**: no `p` has `(E 9) p > 0`. -/
theorem E_nine_no_certificate (p : Fin 9 → ℤ) : ¬∀ i, 0 < (E 9 *ᵥ p) i :=
  (E_isSymm 9).no_certificate_of_null (by decide) (by decide) E_nine_mulVec_null p

/-- `Ẽ₈` is of affine type: positive semidefinite and not positive definite. -/
theorem E_nine_posSemidef_and_not_posDef : (E 9).PosSemidef ∧ ¬(E 9).PosDef :=
  (isSimplyLaced_E 9).isZMatrix.posSemidef_and_not_posDef_of_int_null (E_isSymm 9)
    (by decide) E_nine_mulVec_null

theorem isIndecomposable_E_nine : (E 9).IsIndecomposable := by
  simp only [E_nine_eq, reduceIsIndecomposable]

/-- The isotropic integer vectors of `Ẽ₈` are the multiples of its null vector `δ`. -/
theorem E_nine_isotropic_eq_zsmul {x : Fin 9 → ℤ} (hx : x ⬝ᵥ E 9 *ᵥ x = 0) :
    x = x 8 • ![2, 3, 4, 6, 5, 4, 3, 2, 1] :=
  (isSimplyLaced_E 9).isZMatrix.isotropic_int_eq_zsmul_of_eq_one (E_isSymm 9)
    isIndecomposable_E_nine (by decide) E_nine_mulVec_null (k := 8) rfl hx

end CartanMatrix
