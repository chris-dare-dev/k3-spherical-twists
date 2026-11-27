/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.Index
import K3Twists.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Integer certificates for the Cartan matrix of a fibre

For a connected exceptional fibre `F` (`Mukai.FundamentalCycle`) the Cartan matrix
`A = -Gram(Cᵢ)` (`Mukai.FundamentalCycle.cartan`) has diagonal `2`, is a Z-matrix because
distinct curves meet nonnegatively, is symmetric for a symmetric form, and is positive definite
because the curves span a negative definite lattice: `dᵀAd = -(Σ dᵢ Cᵢ)² > 0` for `d ≠ 0`.

By the integer M-matrix criterion (`Matrix.IsZMatrix.posDef_iff_int_certificate`) it has an
**integer certificate**, a vector `p ∈ ℤ^ι` with `p > 0` and `Ap ≥ 1` componentwise
(`Mukai.FundamentalCycle.exists_cartan_certificate`), and it is a finite-type Cartan matrix in
Mathlib's sense (`Mukai.FundamentalCycle.isFiniteCartan_cartan`). Nothing about the
classification of the fibre is used.

## Main results

* `Mukai.FundamentalCycle.cartan_posDef`: the Cartan matrix of a fibre is positive definite.
* `Mukai.FundamentalCycle.exists_cartan_certificate`: it has an integer certificate.
* `Mukai.FundamentalCycle.isFiniteCartan_cartan`: it is a finite-type Cartan matrix.
-/

open Matrix

namespace Mukai.FundamentalCycle

variable {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {ι : Type*} [Fintype ι]
variable (F : FundamentalCycle b ι)

/-- The diagonal of the Cartan matrix of a fibre is `2`: `-Cᵢ² = 2`. -/
theorem cartan_apply_self (i : ι) : F.cartan i i = 2 := by
  simp [F.curve_self i]

/-- The Cartan matrix of a fibre is a Z-matrix: distinct curves meet nonnegatively. -/
theorem cartan_isZMatrix : F.cartan.IsZMatrix := fun i j hij => by
  simpa using F.curve_nonneg i j hij

/-- The Cartan matrix of a fibre is symmetric when the form is. -/
theorem cartan_isSymm (hb : ∀ x y, b x y = b y x) : F.cartan.IsSymm :=
  LinearMap.BilinForm.wallMatrix_isSymm hb F.curve

/-- **The Cartan matrix of a fibre is positive definite**: `dᵀAd = -(Σ dᵢ Cᵢ)² > 0` for `d ≠ 0`,
since the curves span a negative definite lattice. -/
theorem cartan_posDef (hb : ∀ x y, b x y = b y x) : F.cartan.PosDef := by
  refine (F.cartan_isSymm hb).posDef_iff_dotProduct_mulVec_pos.2 fun d hd => ?_
  have h := F.negDef d hd
  rw [LinearMap.BilinForm.apply_sum_smul_self] at h
  change -(d ⬝ᵥ F.cartan *ᵥ d) < 0 at h
  linarith

/-- **An integer certificate for the Cartan matrix of a fibre**: some `p ∈ ℤ^ι` with `p > 0` and
`Ap ≥ 1` componentwise. -/
theorem exists_cartan_certificate (hb : ∀ x y, b x y = b y x) :
    ∃ p : ι → ℤ, (∀ i, 0 < p i) ∧ ∀ i, 1 ≤ (F.cartan *ᵥ p) i := by
  classical
  exact (F.cartan_isZMatrix.posDef_iff_int_certificate (F.cartan_isSymm hb)).1 (F.cartan_posDef hb)

/-- The Cartan matrix of a fibre is a finite-type Cartan matrix in Mathlib's sense, from its
integer certificate. -/
theorem isFiniteCartan_cartan [DecidableEq ι] (hb : ∀ x y, b x y = b y x) :
    F.cartan.IsFiniteCartan := by
  obtain ⟨p, hp, hAp⟩ := F.exists_cartan_certificate hb
  exact isFiniteCartan_of_certificate (F.cartan_isSymm hb) F.cartan_apply_self F.cartan_isZMatrix
    (fun i => (hp i).le) hAp

end Mukai.FundamentalCycle
