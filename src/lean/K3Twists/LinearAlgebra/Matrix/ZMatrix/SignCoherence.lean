/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Matrix.ZMatrix

/-!
# Sign coherence of the roots of a positive semidefinite symmetric Z-matrix

Let `G` be a symmetric integer Z-matrix (off-diagonal entries `≤ 0`) with even diagonal, whose
quadratic form `q(x) = xᵀGx` is nonnegative on `ℤⁿ`, and such that every isotropic vector is zero
or has full support. Then every **root**, a vector with `q(x) = 2`, has all coordinates of one sign
(`Matrix.IsZMatrix.signCoherent`).

The proof uses only the splitting `x = x⁺ - x⁻` into vectors of disjoint supports: the cross term
`x⁺ᵀGx⁻` is a sum of off-diagonal entries times nonnegative numbers, so `q(x) ≥ q(x⁺) + q(x⁻)`. The
form is even (`Matrix.IsSymm.even_dotProduct_mulVec`), so if both `x⁺` and `x⁻` are nonzero, each
has `q ≥ 2` (it is not isotropic, since its support is not full), and `q(x) ≥ 4`.

For an affine Cartan matrix the hypotheses hold with the null vector `δ > 0`: isotropic vectors are
the multiples of `δ`. Then the lemma says that the real roots of the affine root system are
positive or negative in the basis of simple roots, with no highest root and no Coxeter-group
positivity (Kac, *Infinite dimensional Lie algebras*, §5.1, gives the general statement through
the Weyl group). For a positive definite matrix it is the corresponding statement for a finite
root system.

## Main results

* `Matrix.IsSymm.dotProduct_mulVec_add_single`: `q(x + t eₖ) = q(x) + 2t (Gx)ₖ + t² Gₖₖ`.
* `Matrix.IsSymm.even_dotProduct_mulVec`: `q` is even when the diagonal is.
* `Matrix.IsZMatrix.dotProduct_mulVec_posPart_negPart`: `q(x) ≥ q(x⁺) + q(x⁻)`.
* `Matrix.IsZMatrix.signCoherent`: sign coherence of roots.
-/

open Finset

namespace Matrix

variable {ι : Type*} [Fintype ι]

section CommRing

variable [DecidableEq ι]

variable {R : Type*} [CommRing R] {A : Matrix ι ι R}

/-- Changing one coordinate: `(x + t eₖ)ᵀA(x + t eₖ) = xᵀAx + 2t (Ax)ₖ + t² Aₖₖ` for symmetric
`A`. -/
lemma IsSymm.dotProduct_mulVec_add_single (hA : A.IsSymm) (x : ι → R) (k : ι) (t : R) :
    (x + Pi.single k t) ⬝ᵥ A *ᵥ (x + Pi.single k t) =
      x ⬝ᵥ A *ᵥ x + 2 * t * (A *ᵥ x) k + t ^ 2 * A k k := by
  have h1 : x ⬝ᵥ A *ᵥ Pi.single k t = t * (A *ᵥ x) k := by
    rw [hA.dotProduct_mulVec_comm, single_dotProduct]
  have h2 : Pi.single k t ⬝ᵥ A *ᵥ Pi.single k t = t ^ 2 * A k k := by
    rw [single_dotProduct]
    simp [mulVec_single]
    ring
  simp only [mulVec_add, dotProduct_add, add_dotProduct, h1, h2, single_dotProduct]
  ring

end CommRing

/-- **The form of a symmetric integer matrix with even diagonal is even.** -/
lemma IsSymm.even_dotProduct_mulVec [DecidableEq ι] {A : Matrix ι ι ℤ} (hA : A.IsSymm)
    (hd : ∀ i, Even (A i i)) (x : ι → ℤ) : Even (x ⬝ᵥ A *ᵥ x) := by
  have key : ∀ s : Finset ι, Even ((∑ k ∈ s, Pi.single k (x k)) ⬝ᵥ A *ᵥ
      (∑ k ∈ s, Pi.single k (x k))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, add_comm, hA.dotProduct_mulVec_add_single]
      obtain ⟨m, hm⟩ := hd k
      refine (ih.add ?_).add ?_
      · exact ⟨x k * (A *ᵥ ∑ k ∈ s, Pi.single k (x k)) k,
          by ring⟩
      · exact ⟨x k ^ 2 * m, by rw [hm]; ring⟩
  simpa [Finset.univ_sum_single] using key Finset.univ

/-- **Disjoint supports.** For a Z-matrix and `x = x⁺ - x⁻` with `x⁺ = max x 0`,
`x⁻ = max (-x) 0`, the cross term is nonpositive: `x⁺ᵀ A x⁻ ≤ 0`. -/
lemma IsZMatrix.posPart_dotProduct_mulVec_negPart_nonpos {A : Matrix ι ι ℤ} (hZ : A.IsZMatrix)
    (x : ι → ℤ) : (fun i => max (x i) 0) ⬝ᵥ A *ᵥ (fun i => max (-x i) 0) ≤ 0 := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
  rcases eq_or_ne i j with rfl | hij
  · rcases le_total (x i) 0 with h | h
    · simp [max_eq_right h]
    · simp [max_eq_right (neg_nonpos.mpr h)]
  · exact mul_nonpos_of_nonneg_of_nonpos (le_max_right _ _)
      (mul_nonpos_of_nonpos_of_nonneg (hZ i j hij) (le_max_right _ _))

/-- **`q(x) ≥ q(x⁺) + q(x⁻)`** for a symmetric Z-matrix. -/
lemma IsZMatrix.dotProduct_mulVec_posPart_negPart {A : Matrix ι ι ℤ} (hZ : A.IsZMatrix)
    (hA : A.IsSymm) (x : ι → ℤ) :
    (fun i => max (x i) 0) ⬝ᵥ A *ᵥ (fun i => max (x i) 0) +
        (fun i => max (-x i) 0) ⬝ᵥ A *ᵥ (fun i => max (-x i) 0) ≤ x ⬝ᵥ A *ᵥ x := by
  have hx : x = (fun i => max (x i) 0) - fun i => max (-x i) 0 := by
    ext i
    simp only [Pi.sub_apply]
    rcases le_total (x i) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
  conv_rhs => rw [hx, hA.dotProduct_mulVec_sub]
  linarith [hZ.posPart_dotProduct_mulVec_negPart_nonpos x]

/-- **Sign coherence (roots of a positive semidefinite Z-matrix).** Let `A` be a symmetric integer
Z-matrix with even diagonal, with `xᵀAx ≥ 0` for all `x`, and such that every isotropic vector is
zero or has full support. Then every root, `xᵀAx = 2`, has all coordinates `≥ 0` or all `≤ 0`. -/
theorem IsZMatrix.signCoherent [DecidableEq ι] {A : Matrix ι ι ℤ} (hZ : A.IsZMatrix) (hA : A.IsSymm)
    (hd : ∀ i, Even (A i i)) (hpsd : ∀ x, 0 ≤ x ⬝ᵥ A *ᵥ x)
    (hiso : ∀ x, x ⬝ᵥ A *ᵥ x = 0 → x = 0 ∨ ∀ i, x i ≠ 0) {x : ι → ℤ}
    (hx : x ⬝ᵥ A *ᵥ x = 2) : (∀ i, 0 ≤ x i) ∨ ∀ i, x i ≤ 0 := by
  by_contra hcon
  simp only [not_or, not_forall, not_le] at hcon
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hcon
  -- each part is not isotropic: it is nonzero and vanishes somewhere
  have two_le : ∀ y : ι → ℤ, ∀ a b : ι, y a ≠ 0 → y b = 0 → 2 ≤ y ⬝ᵥ A *ᵥ y := by
    intro y a b ha hb
    have hne : y ⬝ᵥ A *ᵥ y ≠ 0 := by
      intro h0
      rcases hiso y h0 with h | h
      · exact ha (by simp [h])
      · exact h b hb
    obtain ⟨r, hr⟩ := hA.even_dotProduct_mulVec hd y
    have := hpsd y
    omega
  have hp2 := two_le (fun k => max (x k) 0) j i (by simp; omega) (by simp; omega)
  have hm2 := two_le (fun k => max (-x k) 0) i j (by simp; omega) (by simp; omega)
  have := hZ.dotProduct_mulVec_posPart_negPart hA x
  omega

end Matrix
