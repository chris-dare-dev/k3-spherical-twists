/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Group.Even
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Isotropic vectors of a rank-two wall

A symmetric `2 × 2` matrix `A = [[a, b], [b, c]]` over a field has a nonzero isotropic vector,
`xᵀ A x = 0`, exactly when `-det A = b² - ac` is a square
(`Matrix.exists_isotropic_iff_isSquare_neg_det`). The identity behind it is
`a (xᵀ A x) = (a x₀ + b x₁)² - (b² - ac) x₁²`; no hypothesis on the characteristic is needed.

For the wall matrix `[[2, -g], [-g, 2]]` of two spherical classes of pairing `g` (the symmetric
Cartan matrix of the `g`-Kronecker quiver), `-det A = g² - 4` is the negated Gram determinant of the
two classes. So the span of two spherical classes is anisotropic over a field exactly when `g² - 4`
is not a square there; over `ℚ` and for integers `|g| ≥ 3` it is not
(`Quiver.Kronecker.no_null_vector`).

## Main results

* `Matrix.isSquare_neg_det_of_isotropic`: a nonzero isotropic vector makes `-det A` a square.
* `Matrix.exists_isotropic_of_isSquare_neg_det`: conversely, `-det A = s²` gives the isotropic
  vector `(s - b, a)`, or `(1, 0)` when `a = 0`.
* `Matrix.exists_isotropic_iff_isSquare_neg_det`: the two together.
-/

namespace Matrix

variable {K : Type*} [Field K]

/-- The form of a `2 × 2` matrix: `xᵀ A x = a x₀² + (b + b') x₀ x₁ + c x₁²`. -/
lemma dotProduct_mulVec_fin_two (A : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → K) :
    x ⬝ᵥ A *ᵥ x = A 0 0 * x 0 ^ 2 + (A 0 1 + A 1 0) * x 0 * x 1 + A 1 1 * x 1 ^ 2 := by
  simp only [dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- **A nonzero isotropic vector of a symmetric `2 × 2` matrix makes `-det A` a square.** With
`A = [[a, b], [b, c]]`, `a (xᵀ A x) = (a x₀ + b x₁)² - (b² - ac) x₁²`, and `x₁ ≠ 0` unless `a = 0`,
in which case `-det A = b²`. -/
theorem isSquare_neg_det_of_isotropic {A : Matrix (Fin 2) (Fin 2) K} (hA : A.IsSymm)
    {x : Fin 2 → K} (hx : x ≠ 0) (h : x ⬝ᵥ A *ᵥ x = 0) : IsSquare (-A.det) := by
  have hb : A 1 0 = A 0 1 := hA.apply 0 1
  rw [det_fin_two, hb]
  rw [dotProduct_mulVec_fin_two, hb] at h
  by_cases ha : A 0 0 = 0
  · exact ⟨A 0 1, by rw [ha]; ring⟩
  have hx1 : x 1 ≠ 0 := by
    intro h1
    rw [h1] at h
    have h0 : x 0 = 0 := by
      have : A 0 0 * x 0 ^ 2 = 0 := by linear_combination h
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 this).resolve_left ha)
    exact hx (funext fun i => by fin_cases i <;> simp [h0, h1])
  refine ⟨(A 0 0 * x 0 + A 0 1 * x 1) / x 1, ?_⟩
  field_simp
  linear_combination (-A 0 0) * h

/-- **Conversely**, if `-det A = s²` for a symmetric `A = [[a, b], [b, c]]`, then `(s - b, a)` is
isotropic, and nonzero when `a ≠ 0`; when `a = 0` the vector `(1, 0)` is. -/
theorem exists_isotropic_of_isSquare_neg_det {A : Matrix (Fin 2) (Fin 2) K} (hA : A.IsSymm)
    (h : IsSquare (-A.det)) : ∃ x : Fin 2 → K, x ≠ 0 ∧ x ⬝ᵥ A *ᵥ x = 0 := by
  have hb : A 1 0 = A 0 1 := hA.apply 0 1
  obtain ⟨s, hs⟩ := h
  rw [det_fin_two, hb] at hs
  by_cases ha : A 0 0 = 0
  · refine ⟨![1, 0], fun h0 => one_ne_zero (congrFun h0 0), ?_⟩
    rw [dotProduct_mulVec_fin_two]
    simp [ha]
  · refine ⟨![s - A 0 1, A 0 0], fun h0 => ha (by simpa using congrFun h0 1), ?_⟩
    rw [dotProduct_mulVec_fin_two, hb]
    simp only [cons_val_zero, cons_val_one]
    linear_combination (-A 0 0) * hs

/-- **A symmetric `2 × 2` matrix over a field is isotropic iff minus its determinant is a
square.** -/
theorem exists_isotropic_iff_isSquare_neg_det {A : Matrix (Fin 2) (Fin 2) K} (hA : A.IsSymm) :
    (∃ x : Fin 2 → K, x ≠ 0 ∧ x ⬝ᵥ A *ᵥ x = 0) ↔ IsSquare (-A.det) :=
  ⟨fun ⟨_, hx, h⟩ => isSquare_neg_det_of_isotropic hA hx h,
    exists_isotropic_of_isSquare_neg_det hA⟩

end Matrix
