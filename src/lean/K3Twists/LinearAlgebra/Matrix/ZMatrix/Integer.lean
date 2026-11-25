/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Matrix.ZMatrix
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Integer symmetric Z-matrices: certificates and the `ℤδ` kernel

For a symmetric integer matrix, positive definiteness and positive semidefiniteness over `ℤ`
(Mathlib's `Matrix.PosDef`, as `Matrix.IsFiniteCartan` uses it) agree with the same notions over
`ℚ`, by clearing denominators (`Matrix.IsSymm.posDef_map_intCast_iff`,
`Matrix.IsSymm.posSemidef_map_intCast_iff`). From the ordered-field theory of
`K3Twists.LinearAlgebra.Matrix.ZMatrix`:

* `Matrix.IsZMatrix.posDef_iff_int_certificate`: a symmetric integer Z-matrix is positive
  definite iff some `p ∈ ℤ^ι`, `p > 0`, has `Ap ≥ 1`; every nonnegative integer certificate is
  positive (`Matrix.IsZMatrix.int_certificate_pos`);
* `Matrix.IsZMatrix.posSemidef_and_not_posDef_of_int_null`: a positive integer null vector gives
  affine type;
* `Matrix.IsZMatrix.isotropic_int_eq_zsmul`: for an indecomposable symmetric integer Z-matrix
  with a positive *primitive* null vector `δ`, the isotropic integer vectors are exactly `ℤδ`.

No hypothesis on the diagonal is used.
-/

open Finset

namespace Matrix

variable {ι : Type*}

/-- The rational image of an integer Z-matrix is a Z-matrix. -/
lemma IsZMatrix.map_intCast {A : Matrix ι ι ℤ} (hZ : A.IsZMatrix) :
    (A.map ((↑) : ℤ → ℚ)).IsZMatrix := fun i j hij => by
  simpa using hZ i j hij

/-- A rational vector and an integer multiple of it with integer coordinates. -/
private lemma intCast_eq_smul {x : ι → ℚ} {d : ℤ} {y : ι → ℤ} (hy : ∀ i, (y i : ℚ) = d * x i) :
    (fun i => (y i : ℚ)) = (d : ℚ) • x :=
  funext fun i => by simp [hy]

variable [Fintype ι]

/-- **Clearing denominators.** Every rational vector has a positive integer multiple with integer
coordinates. -/
lemma exists_pos_int_mul_eq_intCast (x : ι → ℚ) :
    ∃ d : ℤ, 0 < d ∧ ∃ y : ι → ℤ, ∀ i, (y i : ℚ) = d * x i := by
  classical
  refine ⟨∏ i, ((x i).den : ℤ), Finset.prod_pos fun i _ => by exact_mod_cast (x i).den_pos,
    fun i => (∏ j, ((x j).den : ℤ)) / (x i).den * (x i).num, fun i => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => ((x j).den : ℤ)) (Finset.mem_univ i)
  have hden : ((x i).den : ℤ) ≠ 0 := by exact_mod_cast (x i).den_ne_zero
  dsimp only
  rw [hk, Int.mul_ediv_cancel_left _ hden]
  push_cast
  rw [← Rat.mul_den_eq_num (x i)]
  ring

lemma intCast_dotProduct_mulVec (A : Matrix ι ι ℤ) (x : ι → ℤ) :
    ((x ⬝ᵥ A *ᵥ x : ℤ) : ℚ) = (fun i => (x i : ℚ)) ⬝ᵥ A.map (↑) *ᵥ fun i => (x i : ℚ) := by
  simp [dotProduct_mulVec_self_eq_sum]

lemma intCast_mulVec_apply (A : Matrix ι ι ℤ) (x : ι → ℤ) (i : ι) :
    (((A *ᵥ x) i : ℤ) : ℚ) = (A.map (↑) *ᵥ fun j => (x j : ℚ)) i := by
  simp [mulVec, dotProduct]

/-- The quadratic form scales by `d²`. -/
lemma smul_dotProduct_mulVec_smul {R : Type*} [CommRing R] (A : Matrix ι ι R) (d : R)
    (x : ι → R) : (d • x) ⬝ᵥ A *ᵥ (d • x) = d ^ 2 * (x ⬝ᵥ A *ᵥ x) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

variable {A : Matrix ι ι ℤ}

/-- Over `ℚ` and over `ℤ` the form of a symmetric integer matrix is positive definite together. -/
theorem IsSymm.posDef_map_intCast_iff (hA : A.IsSymm) :
    (A.map ((↑) : ℤ → ℚ)).PosDef ↔ A.PosDef := by
  rw [(hA.map _).posDef_iff_dotProduct_mulVec_pos, hA.posDef_iff_dotProduct_mulVec_pos]
  constructor
  · intro h x hx
    have := h (fun i => (x i : ℚ)) fun h0 => hx (funext fun i => by simpa using congr_fun h0 i)
    rw [← intCast_dotProduct_mulVec] at this
    exact_mod_cast this
  · intro h x hx
    obtain ⟨d, hd, y, hy⟩ := exists_pos_int_mul_eq_intCast x
    have hy0 : y ≠ 0 := by
      intro h0
      apply hx
      funext i
      have := hy i
      simp only [h0, Pi.zero_apply, Int.cast_zero, zero_eq_mul] at this
      exact this.resolve_left (by exact_mod_cast hd.ne')
    have h1 : (0 : ℚ) < ((y ⬝ᵥ A *ᵥ y : ℤ) : ℚ) := by exact_mod_cast h y hy0
    rw [intCast_dotProduct_mulVec, intCast_eq_smul hy, smul_dotProduct_mulVec_smul] at h1
    exact pos_of_mul_pos_right h1 (by positivity)

/-- Over `ℚ` and over `ℤ` the form of a symmetric integer matrix is positive semidefinite
together. -/
theorem IsSymm.posSemidef_map_intCast_iff (hA : A.IsSymm) :
    (A.map ((↑) : ℤ → ℚ)).PosSemidef ↔ A.PosSemidef := by
  rw [(hA.map _).posSemidef_iff_dotProduct_mulVec_nonneg,
    hA.posSemidef_iff_dotProduct_mulVec_nonneg]
  constructor
  · intro h x
    have := h fun i => (x i : ℚ)
    rw [← intCast_dotProduct_mulVec] at this
    exact_mod_cast this
  · intro h x
    obtain ⟨d, hd, y, hy⟩ := exists_pos_int_mul_eq_intCast x
    have h1 : (0 : ℚ) ≤ ((y ⬝ᵥ A *ᵥ y : ℤ) : ℚ) := by exact_mod_cast h y
    rw [intCast_dotProduct_mulVec, intCast_eq_smul hy, smul_dotProduct_mulVec_smul] at h1
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℚ) < (d : ℚ) ^ 2)

/-- Every nonnegative integer certificate `p ≥ 0`, `Ap ≥ 1` of a Z-matrix is positive. -/
lemma IsZMatrix.int_certificate_pos (hZ : A.IsZMatrix) {p : ι → ℤ} (hp : ∀ i, 0 ≤ p i)
    (hAp : ∀ i, 1 ≤ (A *ᵥ p) i) (i : ι) : 0 < p i :=
  hZ.pos_of_nonneg_of_mulVec_pos hp (fun j => by linarith [hAp j]) i

/-- **The integer certificate.** A symmetric integer Z-matrix is positive definite iff some
`p ∈ ℤ^ι` with `p > 0` has `Ap ≥ 1`. -/
theorem IsZMatrix.posDef_iff_int_certificate [DecidableEq ι] (hZ : A.IsZMatrix)
    (hA : A.IsSymm) : A.PosDef ↔ ∃ p : ι → ℤ, (∀ i, 0 < p i) ∧ ∀ i, 1 ≤ (A *ᵥ p) i := by
  rw [← hA.posDef_map_intCast_iff, hZ.map_intCast.posDef_iff_exists_certificate (hA.map _)]
  constructor
  · rintro ⟨p, hp, hAp⟩
    obtain ⟨d, hd, q, hq⟩ := exists_pos_int_mul_eq_intCast p
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    refine ⟨q, fun i => ?_, fun i => ?_⟩
    · have : (0 : ℚ) < q i := by rw [hq]; exact mul_pos hdq (hp i)
      exact_mod_cast this
    · have : (0 : ℚ) < ((A *ᵥ q) i : ℤ) := by
        rw [intCast_mulVec_apply, intCast_eq_smul hq, mulVec_smul, Pi.smul_apply, smul_eq_mul]
        exact mul_pos hdq (hAp i)
      have : 0 < (A *ᵥ q) i := by exact_mod_cast this
      omega
  · rintro ⟨p, hp, hAp⟩
    refine ⟨fun i => (p i : ℚ), fun i => Int.cast_pos.mpr (hp i), fun i => ?_⟩
    rw [← intCast_mulVec_apply]
    exact_mod_cast (show (0 : ℤ) < (A *ᵥ p) i by linarith [hAp i])

/-- **Affine type from a positive integer null vector**, over `ℤ`. -/
theorem IsZMatrix.posSemidef_and_not_posDef_of_int_null [Nonempty ι] (hZ : A.IsZMatrix)
    (hA : A.IsSymm) {δ : ι → ℤ} (hδ : ∀ i, 0 < δ i) (hAδ : A *ᵥ δ = 0) :
    A.PosSemidef ∧ ¬A.PosDef := by
  rw [← hA.posSemidef_map_intCast_iff, ← hA.posDef_map_intCast_iff]
  refine hZ.map_intCast.posSemidef_and_not_posDef_of_null (hA.map _)
    (δ := fun i => (δ i : ℚ)) (fun i => by exact_mod_cast hδ i) (funext fun i => ?_)
  rw [← intCast_mulVec_apply, hAδ]
  simp

lemma IsIndecomposable.map_intCast (hconn : A.IsIndecomposable) :
    (A.map ((↑) : ℤ → ℚ)).IsIndecomposable := by
  simpa [isIndecomposable_iff_reflTransGen] using hconn

/-- **The `ℤδ` kernel.** For an indecomposable symmetric integer Z-matrix with a positive null
vector `δ` that is primitive (no non-unit divides all its coordinates), the isotropic integer
vectors are exactly the integer multiples of `δ`. -/
theorem IsZMatrix.isotropic_int_eq_zsmul (hZ : A.IsZMatrix) (hA : A.IsSymm)
    (hconn : A.IsIndecomposable) {δ : ι → ℤ} (hδ : ∀ i, 0 < δ i) (hAδ : A *ᵥ δ = 0)
    (hprim : ∀ n : ℤ, (∀ i, n ∣ δ i) → IsUnit n) {x : ι → ℤ} (hx : x ⬝ᵥ A *ᵥ x = 0) :
    ∃ c : ℤ, x = c • δ := by
  obtain ⟨c, hc⟩ := hZ.map_intCast.isotropic_eq_smul (hA.map _) hconn.map_intCast
    (δ := fun i => (δ i : ℚ)) (fun i => by exact_mod_cast hδ i)
    (funext fun i => by rw [← intCast_mulVec_apply, hAδ]; simp)
    (x := fun i => (x i : ℚ)) (by rw [← intCast_dotProduct_mulVec, hx]; simp)
  -- `x = c δ` over `ℚ`; write `c = num/den` and show `den = 1`
  have hxi : ∀ i, x i * c.den = c.num * δ i := fun i => by
    have h := congr_fun hc i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have : ((x i * c.den : ℤ) : ℚ) = ((c.num * δ i : ℤ) : ℚ) := by
      push_cast
      rw [h, ← Rat.mul_den_eq_num c]
      ring
    exact_mod_cast this
  have hcop : IsCoprime (c.den : ℤ) c.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact c.reduced
  have hden : IsUnit (c.den : ℤ) := hprim _ fun i =>
    hcop.dvd_of_dvd_mul_left ⟨x i, by rw [← hxi]; ring⟩
  have hden1 : (c.den : ℤ) = 1 := by
    rcases Int.isUnit_iff.mp hden with h | h
    · exact h
    · exact absurd h (by have := c.den_pos; omega)
  refine ⟨c.num, funext fun i => ?_⟩
  have := hxi i
  rw [hden1, mul_one] at this
  simpa using this

/-- The `ℤδ` kernel when some coordinate of `δ` is `1`. -/
theorem IsZMatrix.isotropic_int_eq_zsmul_of_eq_one (hZ : A.IsZMatrix) (hA : A.IsSymm)
    (hconn : A.IsIndecomposable) {δ : ι → ℤ} (hδ : ∀ i, 0 < δ i) (hAδ : A *ᵥ δ = 0) {k : ι}
    (hk : δ k = 1) {x : ι → ℤ} (hx : x ⬝ᵥ A *ᵥ x = 0) : x = x k • δ := by
  obtain ⟨c, rfl⟩ := hZ.isotropic_int_eq_zsmul hA hconn hδ hAδ
    (fun n hn => isUnit_of_dvd_one (hk ▸ hn k)) hx
  simp [hk]

end Matrix
