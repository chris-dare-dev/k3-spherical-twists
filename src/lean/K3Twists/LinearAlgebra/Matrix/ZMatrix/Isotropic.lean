/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Matrix.ZMatrix.Integer
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Isotropic sums of spherical vertices

Let `A` be the wall matrix of a configuration of stable objects of one phase,
`Aᵢⱼ = χ(Sᵢ, Sⱼ) = -⟨v(Sᵢ), v(Sⱼ)⟩` (the Mukai sign convention, in which a spherical object
has `Aᵢᵢ = 2` and an object with isotropic class has `Aᵢᵢ = 0`). Then
`v(Σ aᵢ Sᵢ)² = -aᵀAa`, so an iterated extension of the `Sᵢ` with multiplicities `a` has an
isotropic class exactly when `aᵀAa = 0`.

* `Matrix.NoIsotropicSphereSum A`: no nonzero `a ∈ ℕ^ι`, supported on the vertices with
  `Aᵢᵢ = 2`, has `aᵀAa = 0`. It holds vacuously when no vertex has `Aᵢᵢ = 2`. A positive definite
  matrix has it (`Matrix.noIsotropicSphereSum_of_posDef`).
* `Matrix.pairwise_three_not_sufficient`: pairwise pairings at least `3` do not give it. The
  wall of three spheres with pairings `4, 5, 6` has the isotropic sum `(4, 35, 3)`.
* `LinearMap.BilinForm.wallMatrix`, `LinearMap.BilinForm.apply_sum_smul_self`: the wall matrix of
  a family of classes and the Tits identity `B(Σ aᵢ sᵢ, Σ aᵢ sᵢ) = -aᵀAa`.
* `LinearMap.BilinForm.isotropic_param`: one isotropic vector `v` parametrizes isotropic vectors,
  `w(u) = B(u, u)·v − 2B(u, v)·u`.
* `Matrix.ExistsPosIsotropicOfIsotropic`: the open density statement, as a `Prop`: for a
  nondegenerate symmetric Z-matrix over `ℚ` with positive diagonal that is negative somewhere on
  the open positive orthant, a nonzero rational isotropic vector should force a strictly positive
  integer isotropic vector. It is not proved here.

For two spherical vertices `NoIsotropicSphereSum` agrees with `ℚ`-anisotropy of their span:
`Quiver.Kronecker.noIsotropicSphereSum_cartanMatrix_iff_anisotropic`. For three or more their
agreement is the statement `Matrix.ExistsPosIsotropicOfIsotropic` would supply for nondegenerate
walls.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- **No isotropic sum of spheres.** No nonzero nonnegative integer vector supported on the
vertices with `Aᵢᵢ = 2` (the spherical vertices of a wall matrix) has `aᵀAa = 0`. -/
def NoIsotropicSphereSum (A : Matrix ι ι ℤ) : Prop :=
  ∀ a : ι → ℤ, (∀ i, 0 ≤ a i) → a ≠ 0 → (∀ i, A i i ≠ 2 → a i = 0) → a ⬝ᵥ A *ᵥ a ≠ 0

/-- A witness against `NoIsotropicSphereSum`. -/
lemma not_noIsotropicSphereSum {A : Matrix ι ι ℤ} (a : ι → ℤ) (ha : ∀ i, 0 ≤ a i) (ha0 : a ≠ 0)
    (hsupp : ∀ i, A i i ≠ 2 → a i = 0) (hiso : a ⬝ᵥ A *ᵥ a = 0) : ¬A.NoIsotropicSphereSum :=
  fun h => h a ha ha0 hsupp hiso

/-- A positive definite integer matrix has no isotropic sum of spheres. -/
lemma noIsotropicSphereSum_of_posDef {A : Matrix ι ι ℤ} (hA : A.IsSymm) (h : A.PosDef) :
    A.NoIsotropicSphereSum :=
  fun a _ ha _ => (hA.posDef_iff_dotProduct_mulVec_pos.mp h a ha).ne'

/-- **Pairwise pairings at least `3` do not make a wall of three spheres anisotropic.** The wall
matrix with diagonal `2` and off-diagonal entries `-4, -5, -6` has the isotropic sum
`(4, 35, 3)`. -/
theorem pairwise_three_not_sufficient :
    ¬∀ A : Matrix (Fin 3) (Fin 3) ℤ, (∀ i, A i i = 2) → (∀ i j, i ≠ j → A i j ≤ -3) →
      A.NoIsotropicSphereSum := by
  intro h
  refine not_noIsotropicSphereSum (A := !![2, -4, -5; -4, 2, -6; -5, -6, 2]) ![4, 35, 3]
    (by decide) (by decide) (by decide) (by decide) (h _ (by decide) ?_)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- **The open density statement.** For every symmetric Z-matrix `A` over `ℚ` with positive
diagonal and `det A ≠ 0` that is negative somewhere on the open positive orthant, a nonzero
rational isotropic vector should force a strictly positive integer isotropic vector.

This is a statement, not a theorem: it is not proved here. Its hypotheses can hold together (the
rank-two wall of pairing `5/2`). With it, `NoIsotropicSphereSum` would agree with
`ℚ`-anisotropy for nondegenerate walls that are indefinite on the orthant, and with Meyer's
theorem (an indefinite rational form in five or more variables is isotropic; Serre, *A Course in
Arithmetic*, Chapter IV, §3) it would make `NoIsotropicSphereSum` fail for every such
wall with five or more spheres. The expected proof uses only symmetry, nondegeneracy, a rational
isotropic vector and the sign change on the orthant, through `isotropic_param`; the Z-matrix
hypothesis is expected to be unnecessary. -/
def ExistsPosIsotropicOfIsotropic : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ), A.IsSymm → A.IsZMatrix → (∀ i, 0 < A i i) →
    A.det ≠ 0 → (∃ x : Fin n → ℚ, (∀ i, 0 < x i) ∧ x ⬝ᵥ A *ᵥ x < 0) →
    (∃ v : Fin n → ℚ, v ≠ 0 ∧ v ⬝ᵥ A *ᵥ v = 0) →
    ∃ a : Fin n → ℤ, (∀ i, 0 < a i) ∧ (fun i => (a i : ℚ)) ⬝ᵥ A *ᵥ (fun i => (a i : ℚ)) = 0

end Matrix

namespace LinearMap.BilinForm

open Matrix

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type*}

/-- **The wall matrix** of a family `s` for a bilinear form `B`: `Aᵢⱼ = -B(sᵢ, sⱼ)`.

Sign convention: for the Mukai pairing of a K3 surface, `χ(E, F) = -⟨v(E), v(F)⟩`, so this is
the matrix of Euler characteristics `χ(Sᵢ, Sⱼ)`. A spherical object has `Aᵢᵢ = 2`, and two stable
objects of one phase have `Aᵢⱼ = -dim Ext¹(Sᵢ, Sⱼ) ≤ 0` for `i ≠ j`. -/
def wallMatrix (B : LinearMap.BilinForm R M) (s : ι → M) : Matrix ι ι R :=
  Matrix.of fun i j => -B (s i) (s j)

@[simp]
lemma wallMatrix_apply (B : LinearMap.BilinForm R M) (s : ι → M) (i j : ι) :
    B.wallMatrix s i j = -B (s i) (s j) :=
  rfl

lemma wallMatrix_isSymm {B : LinearMap.BilinForm R M} (hB : ∀ x y, B x y = B y x) (s : ι → M) :
    (B.wallMatrix s).IsSymm := by
  ext i j
  simp [hB (s i) (s j)]

/-- **The Tits identity.** `B(Σ aᵢ sᵢ, Σ aᵢ sᵢ) = -aᵀAa` for the wall matrix `A` of `s`: the
square of the class of an iterated extension with multiplicities `a` is read off the wall
matrix. -/
theorem apply_sum_smul_self [Fintype ι] (B : LinearMap.BilinForm R M) (s : ι → M) (a : ι → R) :
    B (∑ i, a i • s i) (∑ i, a i • s i) = -(a ⬝ᵥ B.wallMatrix s *ᵥ a) := by
  rw [Matrix.dotProduct_mulVec_self_eq_sum]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    wallMatrix_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Isotropic vectors from one.** If `v` is isotropic for a bilinear form `B` and
`B(v, u) = B(u, v)`, then `w(u) = B(u, u)·v − 2B(u, v)·u` is isotropic. (This is a map, not a
density statement: it does not say that `w(u) ≠ 0`.) -/
theorem isotropic_param (B : LinearMap.BilinForm R M) (u v : M) (hv : B v v = 0)
    (hsym : B v u = B u v) :
    B (B u u • v - (2 * B u v) • u) (B u u • v - (2 * B u v) • u) = 0 := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv, hsym]
  ring

end LinearMap.BilinForm
