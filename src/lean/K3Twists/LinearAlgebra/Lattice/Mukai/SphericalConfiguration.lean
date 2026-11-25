/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.BilinearForm.Gram
import K3Twists.LinearAlgebra.Matrix.ZMatrix.Isotropic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Isotropic sums of spherical classes

Let `G` be the Gram matrix of the classes `v(Sᵢ)` of a family of stable spherical objects of one
phase, `G i j = ⟨v(Sᵢ), v(Sⱼ)⟩` for the Mukai pairing, so that `G i i = -2`. An iterated extension
of the `Sᵢ` with multiplicities `a i ∈ ℕ` has the class `Σ aᵢ v(Sᵢ)`, of square `aᵀGa` (the Tits
identity, `BilinearForm.apply_sum_smul_sum_smul`). The family has an **isotropic sphere sum**
(`Matrix.IsotropicSphereSum G`) when some nonzero `a ∈ ℕ^ι` has `aᵀGa = 0`.

The vectors are finitely supported, so the index type may be infinite: the stable spherical objects
of one phase are not assumed to be finitely many. Only the zero set of the form matters, so the
predicate does not see the sign of `G`: it holds for the Gram matrix exactly when it holds for the
wall matrix `-G` (`Matrix.isotropicSphereSum_neg`). For a wall matrix whose vertices are all
spherical (diagonal `2`) it is the negation of `Matrix.NoIsotropicSphereSum`
(`Matrix.noIsotropicSphereSum_iff_not_isotropicSphereSum`).

## Per phase, not per wall

Anisotropy (no isotropic sphere sum) is not closed under orthogonal sums: `[-2]` and
`[[-2, 3], [3, -2]]` are each anisotropic, and their orthogonal sum has the isotropic sum
`(1, 1, 1)`, since `-2 - 2 - 2 + 2·3 = 0` (`Matrix.isotropic_block`). So a statement about one
phase at a wall does not follow from statements about the phases' blocks separately, and an
anisotropy hypothesis for a whole wall is strictly stronger than one per phase.

## Main definitions

* `Matrix.IsotropicSphereSum`: some nonzero finitely supported `a : ι →₀ ℕ` has `aᵀGa = 0`.

## Main results

* `Matrix.isotropicSphereSum_iff_of_fintype`: over a finite index type, with `a : ι → ℕ`.
* `Matrix.isotropicSphereSum_neg`, `Matrix.isotropicSphereSum_submatrix_equiv`: independence of
  the sign and of the indexing.
* `Matrix.noIsotropicSphereSum_iff_not_isotropicSphereSum`: the relation to
  `Matrix.NoIsotropicSphereSum` for a wall matrix of spheres.
* `Matrix.not_isotropicSphereSum_of_isEmpty`: a phase with no stable sphere is anisotropic.
* `Matrix.isotropic_block`: anisotropy is not closed under orthogonal sums.

## Tags

spherical object, Gram matrix, isotropic vector, wall, Tits form
-/

namespace Matrix

open Finsupp

variable {ι κ : Type*}

/-- **An isotropic sphere sum.** Some nonzero finitely supported `a : ι →₀ ℕ` has
`aᵀGa = Σᵢ Σⱼ aᵢ Gᵢⱼ aⱼ = 0`.

For the Gram matrix `G i j = ⟨v(Sᵢ), v(Sⱼ)⟩` of the classes of stable spherical objects of one
phase, this says that an iterated extension of them with multiplicities `a` has an isotropic class.
The multiplicities are natural numbers: with integer multiplicities two spheres of pairing `-2`
would already have the isotropic vector `(1, -1)`. -/
def IsotropicSphereSum (G : Matrix ι ι ℤ) : Prop :=
  ∃ a : ι →₀ ℕ, a ≠ 0 ∧ (a.sum fun i m => a.sum fun j n => (m : ℤ) * G i j * n) = 0

/-- The double sum over the support is the dot product over a finite index type. -/
theorem sum_sum_eq_dotProduct_mulVec [Fintype ι] (G : Matrix ι ι ℤ) (a : ι →₀ ℕ) :
    (a.sum fun i m => a.sum fun j n => (m : ℤ) * G i j * n) =
      (fun i => (a i : ℤ)) ⬝ᵥ G *ᵥ (fun i => (a i : ℤ)) := by
  rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Over a finite index type, an isotropic sphere sum is a nonzero `a : ι → ℕ` with
`aᵀGa = 0`. -/
theorem isotropicSphereSum_iff_of_fintype [Fintype ι] (G : Matrix ι ι ℤ) :
    G.IsotropicSphereSum ↔
      ∃ a : ι → ℕ, a ≠ 0 ∧ (fun i => (a i : ℤ)) ⬝ᵥ G *ᵥ (fun i => (a i : ℤ)) = 0 := by
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨a, fun h0 => ha (Finsupp.ext fun i => congrFun h0 i), ?_⟩
    rwa [← sum_sum_eq_dotProduct_mulVec]
  · rintro ⟨a, ha, h⟩
    refine ⟨Finsupp.equivFunOnFinite.symm a, fun h0 => ha (funext fun i => ?_), ?_⟩
    · simpa using DFunLike.congr_fun h0 i
    · rw [sum_sum_eq_dotProduct_mulVec]
      simpa using h

/-- The predicate does not see the sign of the matrix: it holds for a Gram matrix exactly when it
holds for the wall matrix `-G`. -/
@[simp]
theorem isotropicSphereSum_neg (G : Matrix ι ι ℤ) :
    (-G).IsotropicSphereSum ↔ G.IsotropicSphereSum := by
  have key : ∀ a : ι →₀ ℕ,
      (a.sum fun i m => a.sum fun j n => (m : ℤ) * (-G) i j * n) =
        -(a.sum fun i m => a.sum fun j n => (m : ℤ) * G i j * n) := fun a => by
    simp only [Matrix.neg_apply, mul_neg, neg_mul, Finsupp.sum, Finset.sum_neg_distrib]
  simp only [IsotropicSphereSum, key, neg_eq_zero]

private theorem equivMapDomain_ne_zero {α β : Type*} (f : α ≃ β) {a : α →₀ ℕ} (ha : a ≠ 0) :
    a.equivMapDomain f ≠ 0 := fun h =>
  ha (Finsupp.ext fun i => by simpa using DFunLike.congr_fun h (f i))

/-- Reindexing along an equivalence. -/
theorem isotropicSphereSum_submatrix_equiv (G : Matrix ι ι ℤ) (e : κ ≃ ι) :
    (G.submatrix e e).IsotropicSphereSum ↔ G.IsotropicSphereSum := by
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨a.equivMapDomain e, equivMapDomain_ne_zero e ha, ?_⟩
    rw [← h, Finsupp.sum_equivMapDomain]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [Finsupp.sum_equivMapDomain]
    rfl
  · rintro ⟨a, ha, h⟩
    refine ⟨a.equivMapDomain e.symm, equivMapDomain_ne_zero e.symm ha, ?_⟩
    rw [← h, Finsupp.sum_equivMapDomain]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [Finsupp.sum_equivMapDomain]
    simp

/-- **A phase with no stable sphere has no isotropic sphere sum.** -/
theorem not_isotropicSphereSum_of_isEmpty [IsEmpty ι] (G : Matrix ι ι ℤ) :
    ¬G.IsotropicSphereSum := by
  rintro ⟨a, ha, -⟩
  exact ha (Subsingleton.elim _ _)

/-- **The relation to `NoIsotropicSphereSum`.** For a wall matrix all of whose vertices are
spherical (`Aᵢᵢ = 2`), having no isotropic sum of spheres is the negation of
`IsotropicSphereSum`. Without the hypothesis on the diagonal the two differ: `NoIsotropicSphereSum`
only sees the vertices with `Aᵢᵢ = 2`, and holds vacuously for a Gram matrix (diagonal `-2`). -/
theorem noIsotropicSphereSum_iff_not_isotropicSphereSum [Fintype ι] {A : Matrix ι ι ℤ}
    (hA : ∀ i, A i i = 2) : A.NoIsotropicSphereSum ↔ ¬A.IsotropicSphereSum := by
  rw [isotropicSphereSum_iff_of_fintype]
  constructor
  · rintro h ⟨a, ha, hiso⟩
    exact h (fun i => a i) (fun i => by positivity)
      (fun h0 => ha (funext fun i => by simpa using congrFun h0 i))
      (fun i hi => absurd (hA i) hi) hiso
  · intro h a ha0 ha _ hiso
    refine h ⟨fun i => (a i).toNat, fun h0 => ha (funext fun i => ?_), ?_⟩
    · have := congrFun h0 i
      simp only [Pi.zero_apply, Int.toNat_eq_zero] at this
      exact le_antisymm this (ha0 i)
    · have : (fun i => ((a i).toNat : ℤ)) = a := funext fun i => Int.toNat_of_nonneg (ha0 i)
      rw [this]
      exact hiso

/-- **Anisotropy is not closed under orthogonal sums.** The Gram matrix `[-2] ⊕ [[-2, 3], [3, -2]]`
has the isotropic sphere sum `(1, 1, 1)`, while each block has none (a single sphere, and two
spheres of pairing `3`). -/
theorem isotropic_block : (!![(-2 : ℤ), 0, 0; 0, -2, 3; 0, 3, -2]).IsotropicSphereSum :=
  (isotropicSphereSum_iff_of_fintype _).mpr
    ⟨fun _ => 1, fun h => by simpa using congrFun h 0, by decide⟩

end Matrix
