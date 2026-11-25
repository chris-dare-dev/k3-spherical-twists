/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import K3Twists.Algebra.PoincareParity

/-!
# The defect identity of a long exact sequence

For a long exact sequence `⋯ → K_j → E_j → Q_j →δ K_{j+1} → ⋯` of finite-dimensional vector
spaces, rank–nullity in each degree gives
`dim E_j + rk δ_{j-1} + rk δ_j = dim K_j + dim Q_j`
(`LinearMap.finrank_add_finrank_range_connecting`). In Poincaré polynomials
`P_X(t) = Σ_j dim X_j tʲ ∈ ℤ[t, t⁻¹]` this is the **defect identity**

  `P_E = P_K + P_Q - (1 + t) R`, `R = Σ_j rk(δ_j) tʲ ∈ ℕ[t, t⁻¹]`

(`LaurentPolynomial.poincare_eq_sub_mul`, `LinearMap.poincare_eq_of_exact`), and `R` is
determined by `P_E`, `P_K`, `P_Q` because `1 + t` is not a zero divisor
(`LaurentPolynomial.defect_unique`). At `t = -1` it says that Euler characteristics are additive
(`LaurentPolynomial.poincareNegOne_eq_add`); at `t = 1` that total dimension is subadditive with
defect exactly `2R(1)` (`LaurentPolynomial.poincareOne_add_two_mul`).

For a distinguished triangle `K → E → Q` and a cohomological functor (`Hom(S, -)`, or the
cohomology of an exact functor to graded vector spaces) the long exact sequence is the one of
the triangle, and `R` counts the ranks of the connecting maps. Families of dimensions are
finitely supported functions `ℤ →₀ ℕ`.
-/

open LaurentPolynomial Module

namespace LaurentPolynomial

/-- The Poincaré polynomial `Σ_j f(j) tʲ` of a finitely supported family of dimensions. -/
noncomputable def poincare (f : ℤ →₀ ℕ) : ℤ[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff (f.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero)

@[simp]
lemma coeff_poincare (f : ℤ →₀ ℕ) (j : ℤ) : (poincare f).coeff j = f j := rfl

lemma poincare_injective : Function.Injective poincare := fun f f' h ↦ by
  ext j
  have := congrArg (fun p : ℤ[T;T⁻¹] ↦ p.coeff j) h
  simpa using this

@[simp]
lemma poincare_add (f f' : ℤ →₀ ℕ) : poincare (f + f') = poincare f + poincare f' := by
  apply AddMonoidAlgebra.coeff_injective
  ext j
  simp [AddMonoidAlgebra.coeff_add]

@[simp]
lemma poincare_single (j : ℤ) (n : ℕ) : poincare (Finsupp.single j n) = C (n : ℤ) * T j := by
  rw [← single_eq_C_mul_T]
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.coeff_single]
  ext i
  simp only [coeff_poincare, Finsupp.single_apply]
  split_ifs <;> simp

/-- **The defect identity.** If the dimensions `e, k, q` and the ranks `r` satisfy
`e_j + r_{j-1} + r_j = k_j + q_j` in every degree, then
`P_E = P_K + P_Q - (1 + t) R`, `R = Σ_j r_j tʲ`. -/
theorem poincare_eq_sub_mul {k e q r : ℤ →₀ ℕ} (h : ∀ j, e j + r (j - 1) + r j = k j + q j) :
    poincare e = poincare k + poincare q - (1 + T 1) * poincare r := by
  rw [add_mul, one_mul]
  apply AddMonoidAlgebra.coeff_injective
  ext j
  simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.coe_sub,
    Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, T, AddMonoidAlgebra.coeff_single_mul_apply,
    coeff_poincare, one_mul]
  have := h j
  rw [show -1 + j = j - 1 by ring]
  omega

lemma one_add_T_ne_zero : (1 + T 1 : ℤ[T;T⁻¹]) ≠ 0 := by
  intro h
  have := congrArg (fun p : ℤ[T;T⁻¹] ↦ p.coeff 0) h
  rw [← T_zero] at this
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, T_apply] at this
  norm_num at this

/-- **The defect is unique**: `1 + t` is not a zero divisor, so `R` is determined by
`P_E`, `P_K`, `P_Q`. -/
theorem defect_unique {k e q r r' : ℤ →₀ ℕ} (h : ∀ j, e j + r (j - 1) + r j = k j + q j)
    (h' : ∀ j, e j + r' (j - 1) + r' j = k j + q j) : r = r' := by
  have h1 := poincare_eq_sub_mul h
  have h2 := poincare_eq_sub_mul h'
  rw [h1, sub_right_inj] at h2
  exact poincare_injective (mul_left_cancel₀ one_add_T_ne_zero h2)

@[simp]
lemma poincare_zero : poincare 0 = 0 := rfl

/-- At `t = 1` the Poincaré polynomial is the total dimension `P(1)`. -/
lemma eval₂_one_poincare (f : ℤ →₀ ℕ) :
    eval₂ (RingHom.id ℤ) 1 (poincare f) = f.poincareOne := by
  induction f using Finsupp.induction with
  | zero => simp [Finsupp.poincareOne]
  | single_add a n f ha hn ih =>
    rw [poincare_add, map_add, ih, poincare_single, eval₂_C_mul_T, Finsupp.poincareOne,
      Finsupp.poincareOne, Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
      Finsupp.sum_single_index rfl]
    simp

/-- At `t = -1` the Poincaré polynomial is the Euler characteristic `P(-1)`. -/
lemma eval₂_neg_one_poincare (f : ℤ →₀ ℕ) :
    eval₂ (RingHom.id ℤ) (-1) (poincare f) = f.poincareNegOne := by
  induction f using Finsupp.induction with
  | zero => simp [Finsupp.poincareNegOne]
  | single_add a n f ha hn ih =>
    rw [poincare_add, map_add, ih, poincare_single, eval₂_C_mul_T, Finsupp.poincareNegOne,
      Finsupp.poincareNegOne, Finsupp.sum_add_index' (fun _ ↦ by simp)
        (fun _ _ _ ↦ by push_cast; ring), Finsupp.sum_single_index (by simp)]
    simp [Int.negOnePow, mul_comm]

/-- At `t = -1`: Euler characteristics are additive, `χ(E) = χ(K) + χ(Q)`. -/
theorem poincareNegOne_eq_add {k e q r : ℤ →₀ ℕ} (h : ∀ j, e j + r (j - 1) + r j = k j + q j) :
    e.poincareNegOne = k.poincareNegOne + q.poincareNegOne := by
  have := congrArg (eval₂ (RingHom.id ℤ) (-1)) (poincare_eq_sub_mul h)
  simpa [eval₂_neg_one_poincare] using this

/-- At `t = 1`: total dimension is subadditive with defect exactly `2 R(1)`,
`P_E(1) + 2 R(1) = P_K(1) + P_Q(1)`. -/
theorem poincareOne_add_two_mul {k e q r : ℤ →₀ ℕ} (h : ∀ j, e j + r (j - 1) + r j = k j + q j) :
    e.poincareOne + 2 * r.poincareOne = k.poincareOne + q.poincareOne := by
  have := congrArg (eval₂ (RingHom.id ℤ) 1) (poincare_eq_sub_mul h)
  simp only [map_sub, map_add, map_mul, map_one, eval₂_one_poincare, eval₂_T, one_zpow,
    Units.val_one] at this
  omega

end LaurentPolynomial

/-! ### Long exact sequences -/

namespace LinearMap

variable {k : Type*} [Field k] {K E Q : ℤ → Type*} [∀ j, AddCommGroup (K j)]
  [∀ j, Module k (K j)] [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
  [∀ j, AddCommGroup (Q j)] [∀ j, Module k (Q j)] [∀ j, FiniteDimensional k (K j)]
  [∀ j, FiniteDimensional k (E j)] [∀ j, FiniteDimensional k (Q j)]
  {f : ∀ j, K j →ₗ[k] E j} {g : ∀ j, E j →ₗ[k] Q j} {δ : ∀ j, Q j →ₗ[k] K (j + 1)}

/-- **The per-degree defect of a long exact sequence**
`⋯ → K_j → E_j → Q_j →δ K_{j+1} → ⋯`:
`dim E_{j+1} + rk δ_j + rk δ_{j+1} = dim K_{j+1} + dim Q_{j+1}`. -/
theorem finrank_add_finrank_range_connecting
    (hfg : ∀ j, range (f j) = ker (g j)) (hgδ : ∀ j, range (g j) = ker (δ j))
    (hδf : ∀ j, range (δ j) = ker (f (j + 1))) (j : ℤ) :
    finrank k (E (j + 1)) + finrank k (range (δ j)) + finrank k (range (δ (j + 1))) =
      finrank k (K (j + 1)) + finrank k (Q (j + 1)) := by
  have hE := finrank_range_add_finrank_ker (g (j + 1))
  have hK := finrank_range_add_finrank_ker (f (j + 1))
  have hQ := finrank_range_add_finrank_ker (δ (j + 1))
  rw [← hfg] at hE
  rw [← hδf] at hK
  rw [← hgδ] at hQ
  omega

/-- **The defect identity for a long exact sequence** of finite-dimensional spaces, finitely many
of them nonzero: `P_E = P_K + P_Q - (1 + t) R` with `R = Σ_j rk(δ_j) tʲ`. -/
theorem poincare_eq_of_exact
    (hfg : ∀ j, range (f j) = ker (g j)) (hgδ : ∀ j, range (g j) = ker (δ j))
    (hδf : ∀ j, range (δ j) = ker (f (j + 1)))
    (hK : (Function.support fun j ↦ finrank k (K j)).Finite)
    (hE : (Function.support fun j ↦ finrank k (E j)).Finite)
    (hQ : (Function.support fun j ↦ finrank k (Q j)).Finite) :
    ∃ r : ℤ →₀ ℕ, (∀ j, r j = finrank k (range (δ j))) ∧
      LaurentPolynomial.poincare (Finsupp.ofSupportFinite _ hE) =
        LaurentPolynomial.poincare (Finsupp.ofSupportFinite _ hK) +
          LaurentPolynomial.poincare (Finsupp.ofSupportFinite _ hQ) -
            (1 + LaurentPolynomial.T 1) * LaurentPolynomial.poincare r := by
  have hr : (Function.support fun j ↦ finrank k (range (δ j))).Finite := by
    refine hQ.subset fun j hj ↦ ?_
    simp only [Function.mem_support, ne_eq] at hj ⊢
    intro h0
    exact hj (Nat.eq_zero_of_le_zero ((LinearMap.finrank_range_le (δ j)).trans h0.le))
  refine ⟨Finsupp.ofSupportFinite _ hr, fun j ↦ rfl,
    LaurentPolynomial.poincare_eq_sub_mul fun j ↦ ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by ring⟩
  simp only [Finsupp.ofSupportFinite_coe, add_sub_cancel_right]
  exact finrank_add_finrank_range_connecting hfg hgδ hδf i

end LinearMap
