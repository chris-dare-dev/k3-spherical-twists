/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ZMatrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Symmetric Z-matrices and the ground-state identity

A *Z-matrix* is a square matrix whose off-diagonal entries are nonpositive. Mathlib's
`Mathlib/LinearAlgebra/Matrix/ZMatrix.lean` proves a spectral bound for such matrices without
naming them; this file adds the predicate `Matrix.IsZMatrix` and derives the theory of a
*symmetric* Z-matrix from one identity, with **no hypothesis on the diagonal** and no
definiteness hypothesis.

**The ground-state (Picone) identity** (`Matrix.IsSymm.picone`). For a symmetric matrix `A` over
a commutative ring and vectors `p`, `y`, with `x = p y` the coordinatewise product,

  `2 xᵀAx = 2 Σᵢ (Ap)ᵢ pᵢ yᵢ² − Σᵢⱼ Aᵢⱼ pᵢ pⱼ (yᵢ − yⱼ)²`.

It is the discrete ground-state transform (a Doob transform of the matrix by `p`). For a Z-matrix
and `p > 0` the double sum is nonpositive term by term (its diagonal terms vanish), so
`xᵀAx ≥ Σᵢ (Ap)ᵢ xᵢ²/pᵢ` (`Matrix.IsZMatrix.sum_div_le_dotProduct_mulVec`). Over an ordered field
this gives:

* the **M-matrix criterion** in both directions: a symmetric Z-matrix is positive definite iff
  some `p > 0` has `Ap > 0` (`Matrix.IsZMatrix.posDef_iff_exists_certificate`). This is one of
  the equivalent characterisations of a nonsingular M-matrix (Berman–Plemmons, *Nonnegative
  Matrices in the Mathematical Sciences*, Chapter 6, Theorem 2.3); here it needs no
  diagonal-dominance lemma and no minimizer;
* **inverse positivity**: if `A` is positive definite, `Ax ≥ 0` forces `x ≥ 0`
  (`Matrix.IsZMatrix.nonneg_of_mulVec_nonneg`), so `A⁻¹ ≥ 0` and `A⁻¹𝟙 > 0`
  (`Matrix.IsZMatrix.inv_nonneg_of_posDef`);
* **positive semidefiniteness from a positive null vector**
  (`Matrix.IsZMatrix.posSemidef_of_null`): `δ > 0` with `Aδ = 0` makes `A` positive
  semidefinite; it is a consequence, not an input;
* the **affine obstruction** (`Matrix.IsSymm.no_certificate_of_null`): a nonzero `δ ≥ 0` with
  `Aδ = 0` forbids `Ap > 0` for every `p`, for any symmetric matrix over an ordered ring, with
  no sign pattern and no definiteness;
* Mathlib's spectral bound in this language: a positive definite Z-matrix with diagonal at
  most `μ` has its eigenvalues below `2μ` (`Matrix.IsZMatrix.eigenvalue_lt_two_mul`);
* the **affine kernel** (`Matrix.IsZMatrix.isotropic_eq_smul`): for an indecomposable symmetric
  Z-matrix (Mathlib's `Matrix.IsIndecomposable`) with a positive null vector `δ`, the isotropic
  vectors are exactly the multiples of `δ`; and a loop vertex (`Aᵢᵢ = 0`) of such a matrix has
  no neighbour (`Matrix.IsZMatrix.loop_isolated`), so it is the only vertex
  (`Matrix.IsZMatrix.eq_of_loop`).

In the language of generalized Cartan matrices (Kac, *Infinite-dimensional Lie algebras*,
Chapter 4) a symmetric matrix over an ordered field is of *finite type* if it is positive
definite (`Matrix.PosDef`), of *affine type* if it is positive semidefinite and not positive
definite, and *indefinite* otherwise; for an indecomposable symmetric Z-matrix these agree with
Kac's types defined by the sign of `Au` for some `u > 0` (Kac, Theorem 4.3, and the
characterization of symmetrizable matrices of finite and affine type in the same chapter).
The certificates above give the finite case and the affine case with a positive null vector;
the converse for the affine case and the indefinite case need the Perron–Frobenius theorem and
are not formalized here.
-/

open Finset

namespace Matrix

/-- A **Z-matrix**: every off-diagonal entry is nonpositive. Nothing is assumed of the
diagonal. -/
def IsZMatrix {ι R : Type*} [Zero R] [LE R] (A : Matrix ι ι R) : Prop :=
  ∀ i j, i ≠ j → A i j ≤ 0

variable {ι : Type*} [Fintype ι]

/-! ### The ground-state identity over a commutative ring -/

section CommRing

variable {R : Type*} [CommRing R] {A : Matrix ι ι R}

/-- The quadratic form of a matrix as a double sum. -/
lemma dotProduct_mulVec_self_eq_sum (A : Matrix ι ι R) (x : ι → R) :
    x ⬝ᵥ A *ᵥ x = ∑ i, ∑ j, A i j * x i * x j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma IsSymm.dotProduct_mulVec_sub (hA : A.IsSymm) (u v : ι → R) :
    (u - v) ⬝ᵥ A *ᵥ (u - v) = u ⬝ᵥ A *ᵥ u - 2 * (u ⬝ᵥ A *ᵥ v) + v ⬝ᵥ A *ᵥ v := by
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hA.dotProduct_mulVec_comm (x := v) (y := u)]
  ring

/-- **The ground-state (Picone) identity.** For a symmetric matrix `A` over a commutative ring
and vectors `p`, `y`, with `p * y` the coordinatewise product,
`2 (p y)ᵀ A (p y) = 2 Σᵢ (Ap)ᵢ pᵢ yᵢ² − Σᵢⱼ Aᵢⱼ pᵢ pⱼ (yᵢ − yⱼ)²`.
Symmetry is the only hypothesis. -/
theorem IsSymm.picone (hA : A.IsSymm) (p y : ι → R) :
    2 * ((p * y) ⬝ᵥ A *ᵥ (p * y)) =
      2 * ∑ i, (A *ᵥ p) i * p i * y i ^ 2 - ∑ i, ∑ j, A i j * p i * p j * (y i - y j) ^ 2 := by
  have hsym : ∀ i j, A i j = A j i := fun i j => (hA.apply i j).symm
  rw [dotProduct_mulVec_self_eq_sum]
  simp only [Pi.mul_apply]
  have e1 : ∑ i, ∑ j, A i j * p i * p j * y j ^ 2 = ∑ i, ∑ j, A i j * p i * p j * y i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring
  have h1 : ∑ i, (A *ᵥ p) i * p i * y i ^ 2 = ∑ i, ∑ j, A i j * p i * p j * y i ^ 2 := by
    simp only [mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : ∑ i, ∑ j, A i j * p i * p j * (y i - y j) ^ 2 =
      ∑ i, ∑ j, A i j * p i * p j * y i ^ 2 - 2 * ∑ i, ∑ j, A i j * (p i * y i) * (p j * y j)
        + ∑ i, ∑ j, A i j * p i * p j * y j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, h3, e1]; ring

end CommRing

/-! ### Over an ordered ring -/

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {A : Matrix ι ι R}

/-- The `|x|` inequality: for a Z-matrix, `|x|ᵀA|x| ≤ xᵀAx`. Symmetry is not needed. -/
lemma IsZMatrix.abs_dotProduct_mulVec_abs_le (hZ : A.IsZMatrix) (x : ι → R) :
    |x| ⬝ᵥ A *ᵥ |x| ≤ x ⬝ᵥ A *ᵥ x := by
  rw [dotProduct_mulVec_self_eq_sum, dotProduct_mulVec_self_eq_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  simp only [Pi.abs_apply]
  by_cases hij : i = j
  · subst hij
    rw [mul_assoc, mul_assoc, abs_mul_abs_self]
  · have h1 := hZ i j hij
    have h2 : x i * x j ≤ |x i| * |x j| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith

/-- For a Z-matrix and `x ≥ 0`, the coordinate `(Ax)ᵢ` is nonpositive as soon as its diagonal
term `Aᵢᵢ xᵢ` is: at a zero of `x`, or at a loop vertex. -/
lemma IsZMatrix.mulVec_apply_nonpos (hZ : A.IsZMatrix) {x : ι → R} (hx : ∀ j, 0 ≤ x j)
    {i : ι} (hi : A i i * x i ≤ 0) : (A *ᵥ x) i ≤ 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_nonpos fun j _ => ?_
  by_cases hij : i = j
  · subst hij; exact hi
  · exact mul_nonpos_of_nonpos_of_nonneg (hZ i j hij) (hx j)

/-- A nonnegative vector `x` of a Z-matrix with `Ax > 0` is positive. -/
lemma IsZMatrix.pos_of_nonneg_of_mulVec_pos (hZ : A.IsZMatrix) {x : ι → R}
    (hx : ∀ i, 0 ≤ x i) (hAx : ∀ i, 0 < (A *ᵥ x) i) (i : ι) : 0 < x i := by
  refine (hx i).lt_of_ne fun h => ?_
  have := hZ.mulVec_apply_nonpos hx (i := i) (by simp [← h])
  linarith [hAx i]

/-- A loop vertex (`Aᵢᵢ = 0`) of a Z-matrix admits no certificate: `(Ap)ᵢ ≤ 0` for every
`p ≥ 0`. -/
lemma IsZMatrix.no_certificate_of_loop (hZ : A.IsZMatrix) {i : ι} (hi : A i i = 0)
    {p : ι → R} (hp : ∀ j, 0 ≤ p j) : ¬0 < (A *ᵥ p) i :=
  not_lt.mpr (hZ.mulVec_apply_nonpos hp (by simp [hi]))

/-- **The affine obstruction.** A nonzero null vector `δ ≥ 0` of a symmetric matrix forbids any
`p` with `Ap > 0`: `δᵀAp = pᵀAδ = 0`, while `δᵀAp > 0`. No sign pattern, no definiteness, no
positivity of `p`. -/
theorem IsSymm.no_certificate_of_null (hA : A.IsSymm) {δ : ι → R} (hδ : ∀ i, 0 ≤ δ i)
    (hδ0 : δ ≠ 0) (hAδ : A *ᵥ δ = 0) (p : ι → R) : ¬∀ i, 0 < (A *ᵥ p) i := by
  intro hAp
  have h0 : δ ⬝ᵥ A *ᵥ p = 0 := by
    rw [hA.dotProduct_mulVec_comm, hAδ, dotProduct_zero]
  obtain ⟨k, hk⟩ : ∃ k, δ k ≠ 0 := by
    by_contra h
    push Not at h
    exact hδ0 (funext h)
  have : 0 < δ ⬝ᵥ A *ᵥ p :=
    Finset.sum_pos' (fun i _ => mul_nonneg (hδ i) (hAp i).le)
      ⟨k, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hδ k) (Ne.symm hk)) (hAp k)⟩
  linarith

/-- In a Z-matrix with a positive null vector, a loop vertex (`Aᵢᵢ = 0`) has no neighbour:
its whole row vanishes. -/
lemma IsZMatrix.loop_isolated (hZ : A.IsZMatrix) {δ : ι → R} (hδ : ∀ i, 0 < δ i)
    (hAδ : A *ᵥ δ = 0) {i : ι} (hi : A i i = 0) (j : ι) : A i j = 0 := by
  have h0 : ∑ k, A i k * δ k = 0 := by
    simpa [mulVec, dotProduct] using congr_fun hAδ i
  have hterm : ∀ k, A i k * δ k ≤ 0 := fun k => by
    by_cases hik : i = k
    · subst hik; rw [hi, zero_mul]
    · exact mul_nonpos_of_nonpos_of_nonneg (hZ i k hik) (hδ k).le
  have := (Finset.sum_eq_zero_iff_of_nonpos (fun k _ => hterm k)).mp h0 j (Finset.mem_univ _)
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h (hδ j).ne'

/-- An indecomposable Z-matrix with a positive null vector and a loop vertex `i` has `i` as its
only vertex: it is the `1 × 1` zero matrix. -/
lemma IsZMatrix.eq_of_loop (hZ : A.IsZMatrix) (hconn : A.IsIndecomposable) {δ : ι → R}
    (hδ : ∀ i, 0 < δ i) (hAδ : A *ᵥ δ = 0) {i : ι} (hi : A i i = 0) (j : ι) : j = i := by
  rw [isIndecomposable_iff_reflTransGen] at hconn
  induction hconn i j with
  | refl => rfl
  | tail _ hab ih =>
    subst ih
    by_contra hne
    exact hab (hZ.loop_isolated hδ hAδ hi _)

end OrderedRing

section Star

variable {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]
  {A : Matrix ι ι R}

lemma IsSymm.posDef_iff_dotProduct_mulVec_pos (hA : A.IsSymm) :
    A.PosDef ↔ ∀ x, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x := by
  rw [posDef_iff_dotProduct_mulVec]
  simp only [star_trivial]
  exact ⟨fun h => h.2, fun h => ⟨isHermitian_iff_isSymm.mpr hA, h⟩⟩

lemma IsSymm.posSemidef_iff_dotProduct_mulVec_nonneg (hA : A.IsSymm) :
    A.PosSemidef ↔ ∀ x, 0 ≤ x ⬝ᵥ A *ᵥ x := by
  rw [posSemidef_iff_dotProduct_mulVec]
  simp only [star_trivial]
  exact ⟨fun h => h.2, fun h => ⟨isHermitian_iff_isSymm.mpr hA, h⟩⟩

end Star

/-- A matrix with a nonzero null vector is not positive definite. -/
lemma not_posDef_of_mulVec_eq_zero {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
    {A : Matrix ι ι R} {δ : ι → R} (hδ0 : δ ≠ 0) (hAδ : A *ᵥ δ = 0) : ¬A.PosDef := by
  intro hPD
  have := (posDef_iff_dotProduct_mulVec.mp hPD).2 hδ0
  rw [hAδ, dotProduct_zero] at this
  exact lt_irrefl 0 this

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R]
  [TrivialStar R] {A : Matrix ι ι R}

/-- **Inverse positivity.** A positive definite symmetric Z-matrix is monotone: `Ax ≥ 0` forces
`x ≥ 0`, for every `x`. The proof compares `x` with `|x|`. -/
theorem IsZMatrix.nonneg_of_mulVec_nonneg (hZ : A.IsZMatrix) (hA : A.IsSymm) (hPD : A.PosDef)
    {x : ι → R} (hAx : ∀ i, 0 ≤ (A *ᵥ x) i) (i : ι) : 0 ≤ x i := by
  have hyx : |x| - x = 0 := by
    by_contra hne
    have h1 := hA.posDef_iff_dotProduct_mulVec_pos.mp hPD _ hne
    rw [hA.dotProduct_mulVec_sub] at h1
    have h2 := hZ.abs_dotProduct_mulVec_abs_le x
    have h3 : x ⬝ᵥ A *ᵥ x ≤ |x| ⬝ᵥ A *ᵥ x := by
      simp only [dotProduct, Pi.abs_apply]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (le_abs_self _) (hAx j)
    linarith
  have := congr_fun hyx i
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero, Pi.abs_apply] at this
  rw [← this]
  exact abs_nonneg _

/-- **Mathlib's spectral bound for Z-matrices**
(`Matrix.lt_two_mul_of_mul_diagonal_posDef_of_for_le_of_hasEigen`), for `IsZMatrix`: every
eigenvalue of a positive definite Z-matrix with diagonal at most `μ` is less than `2μ`. A
positive definite wall matrix of spheres (diagonal `2`) has its eigenvalues below `4`. -/
theorem IsZMatrix.eigenvalue_lt_two_mul [DecidableEq ι] (hZ : A.IsZMatrix) (hPD : A.PosDef)
    {μ : R} (hμ : ∀ i, A i i ≤ μ) {ρ : R} (hρ : Module.End.HasEigenvalue A.toLin' ρ) :
    ρ < 2 * μ :=
  lt_two_mul_of_mul_diagonal_posDef_of_for_le_of_hasEigen A 1 (by simpa using hPD)
    (fun _ => one_pos) μ ρ (fun i j => by
      split_ifs with h
      · exact h ▸ hμ i
      · exact hZ i j h) hρ

end OrderedRing

/-! ### Over an ordered field -/

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {A : Matrix ι ι 𝕜}

/-- **The ground-state lower bound.** For a symmetric Z-matrix and `p > 0`,
`Σᵢ (Ap)ᵢ xᵢ²/pᵢ ≤ xᵀAx`. -/
theorem IsZMatrix.sum_div_le_dotProduct_mulVec (hZ : A.IsZMatrix) (hA : A.IsSymm)
    {p : ι → 𝕜} (hp : ∀ i, 0 < p i) (x : ι → 𝕜) :
    ∑ i, (A *ᵥ p) i * x i ^ 2 / p i ≤ x ⬝ᵥ A *ᵥ x := by
  have key := hA.picone p (fun i => x i / p i)
  have hx : p * (fun i => x i / p i) = x := funext fun i => by
    simp only [Pi.mul_apply]
    field_simp [(hp i).ne']
  rw [hx] at key
  have hD : ∑ i, ∑ j, A i j * p i * p j * (x i / p i - x j / p j) ^ 2 ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · have h1 := hZ i j hij
      have h2 : 0 ≤ p i * p j * (x i / p i - x j / p j) ^ 2 :=
        mul_nonneg (mul_nonneg (hp i).le (hp j).le) (sq_nonneg _)
      nlinarith
  have hS : ∑ i, (A *ᵥ p) i * p i * (x i / p i) ^ 2 = ∑ i, (A *ᵥ p) i * x i ^ 2 / p i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [(hp i).ne']
  rw [hS] at key
  linarith

/-- A certificate `p > 0`, `Ap ≥ 0` makes the form nonnegative. -/
theorem IsZMatrix.dotProduct_mulVec_nonneg_of_certificate (hZ : A.IsZMatrix) (hA : A.IsSymm)
    {p : ι → 𝕜} (hp : ∀ i, 0 < p i) (hAp : ∀ i, 0 ≤ (A *ᵥ p) i) (x : ι → 𝕜) :
    0 ≤ x ⬝ᵥ A *ᵥ x :=
  le_trans (Finset.sum_nonneg fun i _ => div_nonneg (mul_nonneg (hAp i) (sq_nonneg _)) (hp i).le)
    (hZ.sum_div_le_dotProduct_mulVec hA hp x)

/-- A certificate `p > 0`, `Ap > 0` makes the form positive on nonzero vectors. -/
theorem IsZMatrix.dotProduct_mulVec_pos_of_certificate (hZ : A.IsZMatrix) (hA : A.IsSymm)
    {p : ι → 𝕜} (hp : ∀ i, 0 < p i) (hAp : ∀ i, 0 < (A *ᵥ p) i) {x : ι → 𝕜} (hx : x ≠ 0) :
    0 < x ⬝ᵥ A *ᵥ x := by
  refine lt_of_lt_of_le ?_ (hZ.sum_div_le_dotProduct_mulVec hA hp x)
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  exact Finset.sum_pos' (fun i _ => div_nonneg (mul_nonneg (hAp i).le (sq_nonneg _)) (hp i).le)
    ⟨k, Finset.mem_univ _, div_pos (mul_pos (hAp k) (by positivity)) (hp k)⟩

/-- **The affine kernel.** Let `A` be an indecomposable symmetric Z-matrix with a positive null
vector `δ`. Then every isotropic vector is a multiple of `δ`. No hypothesis on the diagonal and
no definiteness hypothesis: `A` is positive semidefinite by `IsZMatrix.posSemidef_of_null`. -/
theorem IsZMatrix.isotropic_eq_smul (hZ : A.IsZMatrix) (hA : A.IsSymm)
    (hconn : A.IsIndecomposable) {δ : ι → 𝕜} (hδ : ∀ i, 0 < δ i) (hAδ : A *ᵥ δ = 0)
    {x : ι → 𝕜} (hx : x ⬝ᵥ A *ᵥ x = 0) : ∃ c : 𝕜, x = c • δ := by
  set y : ι → 𝕜 := fun i => x i / δ i with hy
  have key := hA.picone δ y
  have hxy : δ * y = x := funext fun i => by
    simp only [Pi.mul_apply, hy]
    field_simp [(hδ i).ne']
  rw [hxy, hx, hAδ] at key
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, zero_sub] at key
  have hterm : ∀ i j, A i j * δ i * δ j * (y i - y j) ^ 2 ≤ 0 := fun i j => by
    by_cases hij : i = j
    · subst hij; simp
    · have h1 := hZ i j hij
      have h2 : 0 ≤ δ i * δ j * (y i - y j) ^ 2 :=
        mul_nonneg (mul_nonneg (hδ i).le (hδ j).le) (sq_nonneg _)
      nlinarith
  have hsum : ∑ i, ∑ j, A i j * δ i * δ j * (y i - y j) ^ 2 = 0 := by linarith
  have hinner : ∀ i, ∑ j, A i j * δ i * δ j * (y i - y j) ^ 2 = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => Finset.sum_nonpos fun j _ => hterm i j)).mp
      hsum i (Finset.mem_univ _)
  have hedge : ∀ i j, A i j ≠ 0 → y i = y j := fun i j hA0 => by
    have h := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hterm i j)).mp (hinner i) j
      (Finset.mem_univ _)
    have hne : A i j * δ i * δ j ≠ 0 :=
      mul_ne_zero (mul_ne_zero hA0 (hδ i).ne') (hδ j).ne'
    have : (y i - y j) ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left hne
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  rw [isIndecomposable_iff_reflTransGen] at hconn
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨0, funext fun i => isEmptyElim i⟩
  · refine ⟨y i₀, funext fun j => ?_⟩
    have hj : y j = y i₀ := by
      induction hconn i₀ j with
      | refl => rfl
      | tail _ hab ih => rw [← ih]; exact (hedge _ _ hab).symm
    rw [← hxy]
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hj]
    ring

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- The converse half of the M-matrix criterion: a certificate `p > 0`, `Ap > 0` makes a
symmetric Z-matrix positive definite. -/
theorem IsZMatrix.posDef_of_certificate (hZ : A.IsZMatrix) (hA : A.IsSymm) {p : ι → 𝕜}
    (hp : ∀ i, 0 < p i) (hAp : ∀ i, 0 < (A *ᵥ p) i) : A.PosDef :=
  hA.posDef_iff_dotProduct_mulVec_pos.mpr fun _ hx =>
    hZ.dotProduct_mulVec_pos_of_certificate hA hp hAp hx

/-- A certificate `p > 0`, `Ap ≥ 0` makes a symmetric Z-matrix positive semidefinite. -/
theorem IsZMatrix.posSemidef_of_certificate (hZ : A.IsZMatrix) (hA : A.IsSymm) {p : ι → 𝕜}
    (hp : ∀ i, 0 < p i) (hAp : ∀ i, 0 ≤ (A *ᵥ p) i) : A.PosSemidef :=
  hA.posSemidef_iff_dotProduct_mulVec_nonneg.mpr
    (hZ.dotProduct_mulVec_nonneg_of_certificate hA hp hAp)

/-- **Positive semidefiniteness from a positive null vector.** -/
theorem IsZMatrix.posSemidef_of_null (hZ : A.IsZMatrix) (hA : A.IsSymm) {δ : ι → 𝕜}
    (hδ : ∀ i, 0 < δ i) (hAδ : A *ᵥ δ = 0) : A.PosSemidef :=
  hZ.posSemidef_of_certificate hA hδ fun i => by simp [hAδ]

/-- **Affine type from a positive null vector**: a nonempty symmetric Z-matrix with a positive
null vector is positive semidefinite and not positive definite. -/
theorem IsZMatrix.posSemidef_and_not_posDef_of_null [Nonempty ι] (hZ : A.IsZMatrix)
    (hA : A.IsSymm) {δ : ι → 𝕜} (hδ : ∀ i, 0 < δ i) (hAδ : A *ᵥ δ = 0) :
    A.PosSemidef ∧ ¬A.PosDef := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨hZ.posSemidef_of_null hA hδ hAδ,
    not_posDef_of_mulVec_eq_zero (fun h => (hδ i).ne' (congr_fun h i)) hAδ⟩

/-- **The M-matrix criterion.** A symmetric Z-matrix over an ordered field is positive definite
if and only if some `p > 0` has `Ap > 0`. -/
theorem IsZMatrix.posDef_iff_exists_certificate [DecidableEq ι] (hZ : A.IsZMatrix)
    (hA : A.IsSymm) : A.PosDef ↔ ∃ p : ι → 𝕜, (∀ i, 0 < p i) ∧ ∀ i, 0 < (A *ᵥ p) i := by
  refine ⟨fun hPD => ?_, fun ⟨p, hp, hAp⟩ => hZ.posDef_of_certificate hA hp hAp⟩
  have hinj : Function.Injective A.mulVec := by
    intro u v huv
    by_contra hne
    have := hA.posDef_iff_dotProduct_mulVec_pos.mp hPD (u - v) (sub_ne_zero.mpr hne)
    simp [mulVec_sub, huv] at this
  obtain ⟨p, hp⟩ := (mulVec_surjective_iff_isUnit.mpr (mulVec_injective_iff_isUnit.mp hinj))
    (fun _ => 1)
  have hAp : ∀ i, 0 < (A *ᵥ p) i := fun i => by rw [hp]; exact one_pos
  exact ⟨p, hZ.pos_of_nonneg_of_mulVec_pos
    (fun i => hZ.nonneg_of_mulVec_nonneg hA hPD (fun j => (hAp j).le) i) hAp, hAp⟩

/-- **Inverse nonnegativity.** The inverse of a positive definite symmetric Z-matrix has
nonnegative entries, and `A⁻¹𝟙 > 0`. -/
theorem IsZMatrix.inv_nonneg_of_posDef [DecidableEq ι] (hZ : A.IsZMatrix) (hA : A.IsSymm)
    (hPD : A.PosDef) : (∀ i j, 0 ≤ A⁻¹ i j) ∧ ∀ i, 0 < (A⁻¹ *ᵥ fun _ => 1) i := by
  have hinj : Function.Injective A.mulVec := by
    intro u v huv
    by_contra hne
    have := hA.posDef_iff_dotProduct_mulVec_pos.mp hPD (u - v) (sub_ne_zero.mpr hne)
    simp [mulVec_sub, huv] at this
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp (mulVec_injective_iff_isUnit.mp hinj)
  have hAA : ∀ v, A *ᵥ (A⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have h := hZ.nonneg_of_mulVec_nonneg hA hPD (x := A⁻¹ *ᵥ Pi.single j 1)
      (fun k => by rw [hAA]; by_cases hk : k = j <;> simp [hk]) i
    simpa [mulVec_single_one] using h
  · have h1 := hZ.nonneg_of_mulVec_nonneg hA hPD (x := A⁻¹ *ᵥ fun _ => 1)
      (fun k => by rw [hAA]; exact zero_le_one)
    exact hZ.pos_of_nonneg_of_mulVec_pos h1 (fun k => by rw [hAA]; exact one_pos) i

end Field

end Matrix
