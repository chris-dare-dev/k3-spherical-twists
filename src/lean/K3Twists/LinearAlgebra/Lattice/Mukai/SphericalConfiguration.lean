/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.Quiver.Kronecker.RealRoots
import K3Twists.LinearAlgebra.BilinearForm.Gram
import K3Twists.LinearAlgebra.Matrix.ZMatrix.Isotropic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Multiset
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

## One and two spheres

A single sphere has no isotropic sum (`Matrix.noIsotropic_one`). Two spheres of pairing `g` have
one exactly when `g = 2` (`Matrix.isotropicSphereSum_two_iff`): for `|g| ≥ 3` because
`x² - gxy + y²` has no rational zero (`Matrix.noIsotropic_two`), for `g ≤ 1` because the form is
positive on the nonnegative quadrant, while at `g = 2`, the wall of a `(-2)`-curve, `(1, 1)` is
isotropic (`Matrix.isotropic_two`). Negative pairings are covered too: with natural coefficients
`[[-2, -2], [-2, -2]]` is anisotropic, although `(1, -1)` is an isotropic integer vector. For three
spheres pairwise pairings of at least `3` do not suffice (`Matrix.pairwise_three_not_sufficient`).

## The lattice core of a lost carrier

If an isotropic nonzero class is a sum, with natural coefficients, of the classes of the stable
objects of one phase, and the stable spherical ones among them have no isotropic sum, then some
constituent is not spherical (`BilinearForm.exists_nonspherical_constituent`). The form used by
`WallStep` is `BilinearForm.isotropicSphereSum_gram_of_list`: a nonempty list of spheres whose
classes add up to an isotropic class gives an isotropic sphere sum of their Gram matrix.

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
* `Matrix.noIsotropic_one`, `Matrix.isotropicSphereSum_two_iff`, `Matrix.noIsotropic_two`,
  `Matrix.isotropic_two`: one and two spheres.
* `BilinearForm.apply_finsupp_sum_self`: the Tits identity for finitely supported coefficients.
* `BilinearForm.isotropicSphereSum_gram_of_list`,
  `BilinearForm.exists_nonspherical_constituent`: the lattice core.

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

/-! ### One and two spheres -/

/-- **One sphere has no isotropic sum.** -/
theorem noIsotropic_one (G : Matrix (Fin 1) (Fin 1) ℤ) (hG : G 0 0 = -2) :
    ¬G.IsotropicSphereSum := by
  rw [isotropicSphereSum_iff_of_fintype]
  rintro ⟨a, ha, h⟩
  apply ha
  funext i
  fin_cases i
  simp only [dotProduct, mulVec, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    hG] at h
  simpa using h

/-- **Two spheres of pairing `g` have an isotropic sum exactly when `g = 2`.** -/
theorem isotropicSphereSum_two_iff (g : ℤ) :
    (!![(-2 : ℤ), g; g, -2]).IsotropicSphereSum ↔ g = 2 := by
  rw [isotropicSphereSum_iff_of_fintype]
  constructor
  · rintro ⟨a, ha, h⟩
    simp only [dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one] at h
    have h2 : 2 * ((a 0 : ℤ) ^ 2 + a 1 ^ 2 - g * a 0 * a 1) = 0 := by linear_combination -h
    have hq : (a 0 : ℤ) ^ 2 + a 1 ^ 2 = g * a 0 * a 1 := by
      linear_combination (mul_eq_zero.mp h2).resolve_left two_ne_zero
    have hne : (a 0 : ℤ) ≠ 0 ∨ (a 1 : ℤ) ≠ 0 := by
      by_contra h0
      push Not at h0
      exact ha (funext fun i => by fin_cases i <;> simp_all)
    by_contra hg
    rcases le_or_gt g 1 with hg1 | hg1
    · have h0 : (0 : ℤ) ≤ a 0 * a 1 := by positivity
      rcases hne with h' | h' <;> nlinarith [sq_pos_of_ne_zero h', sq_nonneg ((a 0 : ℤ) - a 1)]
    · have hg3 : 3 ≤ |g| := by rw [abs_of_pos (by lia)]; lia
      have hqℚ : (a 0 : ℚ) ^ 2 + (a 1 : ℚ) ^ 2 = (g : ℚ) * a 0 * a 1 := by exact_mod_cast hq
      obtain ⟨h0, h1⟩ := Quiver.Kronecker.no_null_vector (g := -g) (by rwa [abs_neg])
        (x := (a 0 : ℚ)) (y := (a 1 : ℚ)) (by push_cast; linarith)
      rcases hne with h' | h'
      · exact h' (by exact_mod_cast h0)
      · exact h' (by exact_mod_cast h1)
  · rintro rfl
    exact ⟨fun _ => 1, fun h => by simpa using congrFun h 0, by decide⟩

/-- **Two spheres of pairing `|g| ≥ 3` have no isotropic sum.** In Picard rank one a wall group
has at most two sphere types (Bayer–Bridgeland, arXiv:1310.8266, Lemma 3.3 and Proposition 3.4). -/
theorem noIsotropic_two {g : ℤ} (hg : 3 ≤ |g|) :
    ¬(!![(-2 : ℤ), g; g, -2]).IsotropicSphereSum := by
  rw [isotropicSphereSum_two_iff]
  rintro rfl
  norm_num at hg

/-- **At pairing two, `(1, 1)` is isotropic**: the wall of a `(-2)`-curve. -/
theorem isotropic_two : (!![(-2 : ℤ), 2; 2, -2]).IsotropicSphereSum :=
  (isotropicSphereSum_two_iff 2).mpr rfl

end Matrix

namespace BilinearForm

open Matrix Finsupp

variable {M ι : Type*} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)

/-- **The Tits identity for finitely supported coefficients.** -/
theorem apply_finsupp_sum_self (c : ι → M) (a : ι →₀ ℕ) :
    B (a.sum fun i n => (n : ℤ) • c i) (a.sum fun i n => (n : ℤ) • c i) =
      a.sum fun i m => a.sum fun j n => (m : ℤ) * gram B c i j * n := by
  simp only [Finsupp.sum, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    smul_eq_mul, gram_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- An isotropic nonzero sum of the family, with natural coefficients, is an isotropic sphere sum
of its Gram matrix. -/
theorem isotropicSphereSum_gram_of_finsupp (c : ι → M) (a : ι →₀ ℕ) (ha : a ≠ 0)
    (h : B (a.sum fun i n => (n : ℤ) • c i) (a.sum fun i n => (n : ℤ) • c i) = 0) :
    (gram B c).IsotropicSphereSum :=
  ⟨a, ha, by rwa [← apply_finsupp_sum_self]⟩

/-- The sum of a multiset of classes is the sum weighted by multiplicities. -/
theorem multiset_sum_map_eq [DecidableEq ι] (c : ι → M) (s : Multiset ι) :
    (s.map c).sum = (Multiset.toFinsupp s).sum fun i n => (n : ℤ) • c i := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
      Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; exact add_smul _ _ _),
      Finsupp.sum_single_index (by simp)]
    simp

/-- **The lattice core, list form.** If the classes of a nonempty list of members of the family
add up to an isotropic class, the Gram matrix of the family has an isotropic sphere sum. -/
theorem isotropicSphereSum_gram_of_list (c : ι → M) (L : List ι) (hL : L ≠ [])
    (h : B (L.map c).sum (L.map c).sum = 0) : (gram B c).IsotropicSphereSum := by
  classical
  refine isotropicSphereSum_gram_of_finsupp B c (Multiset.toFinsupp L) ?_ ?_
  · rw [Ne, ← Multiset.toFinsupp_zero, Multiset.toFinsupp.injective.eq_iff]
    simpa using hL
  · rwa [← multiset_sum_map_eq, Multiset.map_coe, Multiset.sum_coe]

/-- **There is always a non-spherical constituent.** Let an isotropic nonzero class `f` be a sum,
with natural coefficients `a`, of the classes `c i` of the stable objects of one phase, and let
the spherical ones (`sph`) have no isotropic sphere sum. Then some constituent that occurs in `f`
is not spherical. -/
theorem exists_nonspherical_constituent (c : ι → M) (sph : ι → Prop) (a : ι →₀ ℕ) {f : M}
    (hf : B f f = 0) (hf0 : f ≠ 0) (hsum : f = a.sum fun i n => (n : ℤ) • c i)
    (han : ¬(gram B fun i : {i // sph i} => c i).IsotropicSphereSum) :
    ∃ i, a i ≠ 0 ∧ ¬sph i := by
  by_contra hne
  push Not at hne
  have hsupp : ∀ i ∈ a.support, sph i := fun i hi => hne i (Finsupp.mem_support_iff.mp hi)
  have hsub : (a.subtypeDomain sph).sum (fun i n => (n : ℤ) • c i) =
      a.sum fun i n => (n : ℤ) • c i :=
    Finsupp.sum_subtypeDomain_index (p := sph) (v := a) (h := fun i n => (n : ℤ) • c i) hsupp
  have hne0 : a.subtypeDomain sph ≠ 0 := fun h0 => by
    apply hf0
    rw [hsum, ← hsub, h0, Finsupp.sum_zero_index]
  have key : B ((a.subtypeDomain sph).sum fun i n => (n : ℤ) • c i)
      ((a.subtypeDomain sph).sum fun i n => (n : ℤ) • c i) = 0 := by
    rw [hsub, ← hsum, hf]
  exact han (isotropicSphereSum_gram_of_finsupp B (fun i : {i // sph i} => c i) _ hne0 key)

end BilinearForm
