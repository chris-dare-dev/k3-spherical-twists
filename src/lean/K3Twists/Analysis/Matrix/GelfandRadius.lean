/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Matrix.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import K3Twists.Analysis.SpecificLimits.GrowthRate
import K3Twists.RingTheory.Polynomial.Chebyshev

/-!
# Growth rates of real matrices and the Gelfand radius

For a real square matrix `A`, Mathlib's `gelfandRadius A` is `lim ‖Aⁿ‖^{1/n}` for the `ℓ∞`
operator norm (`Matrix.Norms.Operator`). This file identifies it with growth rates of vectors
and with the spectral radius, and gives certificates for it, without Perron–Frobenius theory.

## Main results

* `Matrix.tendsto_rate_of_pos`: if `A ≥ 0` entrywise and the seed `c` has entries at least
  `m > 0`, then `‖Aⁿ c‖^{1/n} → gelfandRadius A`. No irreducibility, primitivity or Perron
  vector is used.
* `Matrix.spectralRadius_map_ofReal`: the Gelfand radius of a real matrix is the spectral
  radius of its complexification; `Matrix.tendsto_rate_of_pos_spectralRadius` states the rate
  with Mathlib's `spectralRadius ℂ (A.map Complex.ofReal)`, which needs no norm.
* `Matrix.gelfandRadius_le_of_abs_le`: `|E| ≤ P` entrywise implies
  `gelfandRadius E ≤ gelfandRadius P`.
* Certificates from one test vector (Collatz, Math. Z. 48 (1942); Wielandt, Math. Z. 52 (1950)):
  `Matrix.norm_pow_le_of_mulVec_le` (a subinvariant vector `L v ≤ ρ v` with `v ≥ m > 0` gives
  `‖Lᵏ‖ ≤ (‖v‖ / m) ρᵏ`), `Matrix.gelfandRadius_le_of_mulVec_le`, and the lower bound
  `Matrix.le_gelfandRadius_of_smul_le_mulVec` (`t v ≤ L v` with `0 ≤ v ≠ 0`).
* Variational upper bounds: `Matrix.limsup_rpow_inv_le_of_le_mul` (if `X (n + q) ≤ X n L`
  entrywise for nonnegative matrices, `q ≥ 1`, then `limsup ‖X n‖^{1/n} ≤ gelfandRadius(L)^{1/q}`)
  and `Matrix.limsup_gelfandRadius_rpow_inv_le` (if `b_n^{1/n} → λ ≥ 1` and
  `‖L q‖ ≤ 1 + A ∑_{k<q} b_k`, then `limsup gelfandRadius(L q)^{1/q} ≤ λ`).
* `Matrix.gelfandRadius_eq_of_det_eq_one`: a real `2 × 2` matrix of determinant one and trace
  `l + l⁻¹` with `l > 1` has Gelfand radius `l`; the proof uses only the Chebyshev form of its
  powers and the trace, no eigenvector.
* `Matrix.gelfandRadius_thurston`: the Thurston matrices `[[1, aμ], [0, 1]]`, `[[1, 0], [bμ, 1]]`
  of two multitwists (W. Thurston, Bull. Amer. Math. Soc. 19 (1988)) have a product of Gelfand
  radius `λ` with `λ + λ⁻¹ = 2 + abμ²`; `Matrix.gelfandRadius_thurston_two_two` evaluates it at
  `a = b = 2`, `μ = g`: `λ = 1 + 2g² + 2g√(g² + 1)`.

## Conventions

Inequalities between vectors and matrices are entrywise; "`A ≥ 0`" is `∀ i j, 0 ≤ A i j`.
Vectors carry the sup norm and matrices the `ℓ∞` operator norm (the maximal absolute row sum),
opened with `open scoped Matrix.Norms.Operator`. For `x ≥ 0`, `x ^ (n : ℝ)⁻¹` is the `n`-th root.
-/

open Filter Topology

namespace Matrix

open scoped Matrix.Norms.Operator

section Order

variable {κ ι : Type*} [Fintype ι]

/-- A matrix with nonnegative entries maps nonnegative vectors to nonnegative vectors. -/
lemma mulVec_nonneg {A : Matrix κ ι ℝ} (hA : ∀ i j, 0 ≤ A i j) {v : ι → ℝ} (hv : 0 ≤ v) :
    0 ≤ A *ᵥ v :=
  fun i => dotProduct_nonneg_of_nonneg (fun j => hA i j) hv

/-- A matrix with nonnegative entries is monotone on vectors. -/
lemma mulVec_mono {A : Matrix κ ι ℝ} (hA : ∀ i j, 0 ≤ A i j) {v w : ι → ℝ} (h : v ≤ w) :
    A *ᵥ v ≤ A *ᵥ w :=
  fun i => dotProduct_le_dotProduct_of_nonneg_left h (fun j => hA i j)

/-- A product of matrices with nonnegative entries has nonnegative entries. -/
lemma list_prod_apply_nonneg [DecidableEq ι] (L : List (Matrix ι ι ℝ))
    (hL : ∀ A ∈ L, ∀ i j, 0 ≤ A i j) (i j : ι) : 0 ≤ L.prod i j := by
  induction L generalizing i j with
  | nil => rw [List.prod_nil, Matrix.one_apply]; split_ifs <;> norm_num
  | cons A L ih =>
    rw [List.prod_cons, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hL A (by simp) i k) (ih (fun B hB => hL B (by simp [hB])) k j)

/-- The sup norm is monotone on nonnegative vectors. -/
lemma norm_le_norm_of_nonneg_of_le {x y : ι → ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : ‖x‖ ≤ ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun i => ?_
  rw [Real.norm_of_nonneg (hx i)]
  exact (hxy i).trans ((le_abs_self (y i)).trans (by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y i))

end Order

section Rate

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- For a nonnegative matrix and a seed bounded below by `m > 0`, `m ‖B‖ ≤ ‖B c‖`. -/
lemma mul_norm_le_norm_mulVec {B : Matrix κ ι ℝ} (hB : ∀ a b, 0 ≤ B a b) {c : ι → ℝ} {m : ℝ}
    (hm : 0 < m) (hc : ∀ a, m ≤ c a) : m * ‖B‖ ≤ ‖B *ᵥ c‖ := by
  have key : ∀ i, ((∑ j, ‖B i j‖₊ : NNReal) : ℝ) ≤ ‖B *ᵥ c‖ / m := by
    intro i
    rw [le_div_iff₀ hm, NNReal.coe_sum]
    calc (∑ j, (‖B i j‖₊ : ℝ)) * m = ∑ j, B i j * m := by
          rw [Finset.sum_mul]; congr 1; funext j
          rw [coe_nnNorm, Real.norm_eq_abs, abs_of_nonneg (hB i j)]
      _ ≤ ∑ j, B i j * c j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hc j) (hB i j)
      _ = (B *ᵥ c) i := rfl
      _ ≤ ‖(B *ᵥ c) i‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ ‖B *ᵥ c‖ := norm_le_pi_norm _ i
  have hsup : (Finset.univ.sup fun i => ∑ j, ‖B i j‖₊) ≤ (‖B *ᵥ c‖ / m).toNNReal :=
    Finset.sup_le fun i _ => by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]; exact key i
  have : ‖B‖ ≤ ‖B *ᵥ c‖ / m := by
    rw [linfty_opNorm_def]
    calc _ ≤ ((‖B *ᵥ c‖ / m).toNNReal : ℝ) := NNReal.coe_le_coe.2 hsup
      _ = _ := Real.coe_toNNReal _ (by positivity)
  rw [le_div_iff₀ hm] at this
  linarith

/-- **Rate of a seed bounded below.** For `A ≥ 0` entrywise and a seed `c` with entries at least
`m > 0`, `‖Aⁿ c‖^{1/n} → gelfandRadius A`. No irreducibility, primitivity or Perron vector is
used: `m ‖Aⁿ‖ ≤ ‖Aⁿ c‖ ≤ ‖c‖ ‖Aⁿ‖`. -/
theorem tendsto_rate_of_pos (A : Matrix ι ι ℝ) (hA : ∀ a b, 0 ≤ A a b) (c : ι → ℝ) {m : ℝ}
    (hm : 0 < m) (hc : ∀ a, m ≤ c a) :
    Tendsto (fun n : ℕ => ‖(A ^ n) *ᵥ c‖ ^ (n : ℝ)⁻¹) atTop (𝓝 (gelfandRadius A)) := by
  refine Real.tendsto_rpow_inv_of_bounds (H := fun n => ‖A ^ n‖) (c := m) (C := ‖c‖ + 1) hm
    (by positivity) (fun n => norm_nonneg _) ?_ ?_ (tendsto_gelfandRadius A)
  · exact Eventually.of_forall fun n => mul_norm_le_norm_mulVec (pow_apply_nonneg hA n) hm hc
  · refine Eventually.of_forall fun n => (linfty_opNorm_mulVec _ _).trans ?_
    nlinarith [norm_nonneg (A ^ n), norm_nonneg c]

/-- The Gelfand radius of a real matrix is the spectral radius of its complexification. -/
theorem spectralRadius_map_ofReal (A : Matrix ι ι ℝ) :
    spectralRadius ℂ (A.map Complex.ofReal) = ENNReal.ofReal (gelfandRadius A) := by
  rw [spectrum.spectralRadius_eq_gelfandRadius]
  congr 1
  apply gelfandRadius_eq_of_norm_pow_eq
  intro n
  have : (A.map Complex.ofReal) ^ n = (A ^ n).map Complex.ofReal :=
    (map_pow (Complex.ofRealHom.mapMatrix) A n).symm
  rw [this, linfty_opNorm_def, linfty_opNorm_def]
  congr 2
  funext i
  congr 1
  funext j
  simp

/-- **Rate of a seed bounded below, spectral form.** For `A ≥ 0` entrywise and a seed with
entries at least `m > 0`, `‖Aⁿ c‖^{1/n}` tends to the spectral radius of `A` over `ℂ`. -/
theorem tendsto_rate_of_pos_spectralRadius (A : Matrix ι ι ℝ) (hA : ∀ a b, 0 ≤ A a b)
    (c : ι → ℝ) {m : ℝ} (hm : 0 < m) (hc : ∀ a, m ≤ c a) :
    Tendsto (fun n : ℕ => ‖(A ^ n) *ᵥ c‖ ^ (n : ℝ)⁻¹) atTop
      (𝓝 (spectralRadius ℂ (A.map Complex.ofReal)).toReal) := by
  rw [spectralRadius_map_ofReal, ENNReal.toReal_ofReal (gelfandRadius_nonneg A)]
  exact tendsto_rate_of_pos A hA c hm hc

/-- **Entrywise domination bounds the Gelfand radius.** If `|E| ≤ P` entrywise then
`gelfandRadius E ≤ gelfandRadius P`. -/
theorem gelfandRadius_le_of_abs_le {E P : Matrix ι ι ℝ} (h : ∀ a b, |E a b| ≤ P a b) :
    gelfandRadius E ≤ gelfandRadius P := by
  have hP : ∀ a b, 0 ≤ P a b := fun a b => (abs_nonneg _).trans (h a b)
  have hpow : ∀ n a b, |(E ^ n) a b| ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> simp
    | succ n ih =>
      intro a b
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (ih a k) (h k b) (abs_nonneg _) (pow_apply_nonneg hP n a k)
  refine gelfandRadius_le_of_norm_pow_le 1 fun n => ?_
  rw [one_mul, linfty_opNorm_def, linfty_opNorm_def, NNReal.coe_le_coe]
  refine Finset.sup_mono_fun fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_apply_nonneg hP n i j)]
  exact hpow n i j

end Rate

/-! ### Certificates from one test vector -/

section Certificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `L ≥ 0`, `ρ ≥ 0` and `L v ≤ ρ v` entrywise, then `Lᵏ v ≤ ρᵏ v`. -/
lemma pow_mulVec_le_of_mulVec_le {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {v : ι → ℝ} (hv : L *ᵥ v ≤ ρ • v) (k : ℕ) : (L ^ k) *ᵥ v ≤ ρ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc (L ^ (k + 1)) *ᵥ v = L *ᵥ ((L ^ k) *ᵥ v) := by rw [pow_succ', mulVec_mulVec]
      _ ≤ L *ᵥ (ρ ^ k • v) := mulVec_mono hL ih
      _ = ρ ^ k • (L *ᵥ v) := mulVec_smul _ _ _
      _ ≤ ρ ^ k • (ρ • v) := smul_le_smul_of_nonneg_left hv (pow_nonneg hρ k)
      _ = ρ ^ (k + 1) • v := by rw [smul_smul, pow_succ]

/-- If `L ≥ 0`, `t ≥ 0` and `t v ≤ L v` entrywise, then `tᵏ v ≤ Lᵏ v`. -/
lemma smul_le_pow_mulVec_of_smul_le_mulVec {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j) {t : ℝ}
    (ht : 0 ≤ t) {v : ι → ℝ} (hv : t • v ≤ L *ᵥ v) (k : ℕ) : t ^ k • v ≤ (L ^ k) *ᵥ v := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc t ^ (k + 1) • v = t ^ k • (t • v) := by rw [smul_smul, pow_succ]
      _ ≤ t ^ k • (L *ᵥ v) := smul_le_smul_of_nonneg_left hv (pow_nonneg ht k)
      _ = L *ᵥ (t ^ k • v) := (mulVec_smul _ _ _).symm
      _ ≤ L *ᵥ ((L ^ k) *ᵥ v) := mulVec_mono hL ih
      _ = (L ^ (k + 1)) *ᵥ v := by rw [mulVec_mulVec, pow_succ']

omit [DecidableEq ι] in
/-- A subinvariant vector with positive entries has a nonnegative ratio: if `L ≥ 0`,
`v ≥ m > 0` and `L v ≤ ρ v` on a nonempty index type, then `ρ ≥ 0`. -/
lemma nonneg_of_mulVec_le [Nonempty ι] {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j)
    {v : ι → ℝ} {m ρ : ℝ} (hm : 0 < m) (hvm : ∀ i, m ≤ v i) (hv : L *ᵥ v ≤ ρ • v) : 0 ≤ ρ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 : 0 ≤ (L *ᵥ v) i := mulVec_nonneg hL (fun j => hm.le.trans (hvm j)) i
  have h2 := hv i
  have hi := hm.trans_le (hvm i)
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  by_contra hρ
  nlinarith

/-- **Subinvariant vector certificate.** If `L ≥ 0` and `v` has entries at least `m > 0` with
`L v ≤ ρ v` entrywise, then `‖Lᵏ‖ ≤ (‖v‖ / m) ρᵏ` for the `ℓ∞` operator norm. With `m` the
least entry of `v`, the constant is `max v / min v`. -/
theorem norm_pow_le_of_mulVec_le {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j) {v : ι → ℝ}
    {m ρ : ℝ} (hm : 0 < m) (hvm : ∀ i, m ≤ v i) (hv : L *ᵥ v ≤ ρ • v) (k : ℕ) :
    ‖L ^ k‖ ≤ ‖v‖ / m * ρ ^ k := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h1 : L ^ k = 0 := Subsingleton.elim _ _
    have h2 : v = 0 := Subsingleton.elim _ _
    simp [h1, h2]
  have hρ := nonneg_of_mulVec_le hL hm hvm hv
  have hv0 : 0 ≤ v := fun j => hm.le.trans (hvm j)
  have h1 := mul_norm_le_norm_mulVec (pow_apply_nonneg hL k) hm hvm
  have h2 : ‖(L ^ k) *ᵥ v‖ ≤ ρ ^ k * ‖v‖ := by
    have := norm_le_norm_of_nonneg_of_le (mulVec_nonneg (pow_apply_nonneg hL k) hv0)
      (pow_mulVec_le_of_mulVec_le hL hρ hv k)
    rwa [norm_smul, Real.norm_of_nonneg (pow_nonneg hρ k)] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith

/-- **Upper certificate for the Gelfand radius.** If `L ≥ 0` and `v` has positive entries with
`L v ≤ ρ v` entrywise, then `gelfandRadius L ≤ ρ`. -/
theorem gelfandRadius_le_of_mulVec_le [Nonempty ι] {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j)
    {v : ι → ℝ} {m ρ : ℝ} (hm : 0 < m) (hvm : ∀ i, m ≤ v i) (hv : L *ᵥ v ≤ ρ • v) :
    gelfandRadius L ≤ ρ :=
  gelfandRadius_le_of_bound (nonneg_of_mulVec_le hL hm hvm hv)
    (norm_pow_le_of_mulVec_le hL hm hvm hv)

/-- **Collatz–Wielandt lower bound.** If `L ≥ 0` and a nonzero vector `v ≥ 0` satisfies
`t v ≤ L v` entrywise, then `t ≤ gelfandRadius L`: `Lⁿ v ≥ tⁿ v` gives
`‖Lⁿ‖ ‖v‖ ≥ ‖Lⁿ v‖ ≥ tⁿ ‖v‖` (Collatz, Math. Z. 48 (1942); Wielandt, Math. Z. 52 (1950)). -/
theorem le_gelfandRadius_of_smul_le_mulVec {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j)
    {v : ι → ℝ} (hv0 : 0 ≤ v) (hv : v ≠ 0) {t : ℝ} (ht : t • v ≤ L *ᵥ v) :
    t ≤ gelfandRadius L := by
  rcases lt_or_ge t 0 with htn | ht0
  · exact htn.le.trans (gelfandRadius_nonneg L)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hpow : ∀ k : ℕ, t ^ k ≤ ‖L ^ k‖ := by
    intro k
    have h1 : t ^ k * ‖v‖ ≤ ‖(L ^ k) *ᵥ v‖ := by
      have := norm_le_norm_of_nonneg_of_le (smul_nonneg (pow_nonneg ht0 k) hv0)
        (smul_le_pow_mulVec_of_smul_le_mulVec hL ht0 ht k)
      rwa [norm_smul, Real.norm_of_nonneg (pow_nonneg ht0 k)] at this
    exact le_of_mul_le_mul_right (h1.trans (linfty_opNorm_mulVec (L ^ k) v)) hvpos
  refine le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_gelfandRadius L) ?_
  filter_upwards [eventually_ne_atTop 0] with k hk
  calc t = (t ^ k) ^ (k : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast ht0 hk).symm
    _ ≤ ‖L ^ k‖ ^ (k : ℝ)⁻¹ := Real.rpow_le_rpow (pow_nonneg ht0 k) (hpow k) (by positivity)

end Certificate

/-! ### Variational upper bounds -/

section Variational

/-- The `ℓ∞` operator norm is monotone on matrices with nonnegative entries. -/
lemma norm_le_norm_of_nonneg_of_apply_le {κ ι : Type*} [Fintype κ] [Fintype ι]
    {Y Z : Matrix κ ι ℝ} (hY : ∀ i j, 0 ≤ Y i j) (h : ∀ i j, Y i j ≤ Z i j) : ‖Y‖ ≤ ‖Z‖ := by
  rw [linfty_opNorm_def, linfty_opNorm_def, NNReal.coe_le_coe]
  refine Finset.sup_mono_fun fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, Real.norm_of_nonneg (hY i j),
    Real.norm_of_nonneg ((hY i j).trans (h i j))]
  exact h i j

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Domination by a fixed matrix.** If `L ≥ 0` and `X (n + q) ≤ X n L` entrywise for every
`n`, then `X (r + k q) ≤ X r Lᵏ` entrywise. -/
lemma apply_le_mul_pow_of_le_mul {X : ℕ → Matrix ι ι ℝ} {L : Matrix ι ι ℝ}
    (hL : ∀ i j, 0 ≤ L i j) {q : ℕ} (hdom : ∀ n i j, X (n + q) i j ≤ (X n * L) i j) (r k : ℕ) :
    ∀ i j, X (r + k * q) i j ≤ (X r * L ^ k) i j := by
  induction k with
  | zero => intro i j; simp
  | succ k ih =>
    intro i j
    calc X (r + (k + 1) * q) i j = X (r + k * q + q) i j := by rw [add_mul, one_mul, add_assoc]
      _ ≤ (X (r + k * q) * L) i j := hdom _ i j
      _ ≤ (X r * L ^ k * L) i j := by
          rw [Matrix.mul_apply, Matrix.mul_apply]
          exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (ih i l) (hL l j)
      _ = (X r * L ^ (k + 1)) i j := by rw [Matrix.mul_assoc, ← pow_succ]

/-- **Variational upper bound, exponential form.** Let `X n ≥ 0` and `L ≥ 0` be real matrices
with `X (n + q) ≤ X n L` entrywise for every `n`, where `q ≥ 1`. Then for every
`R > gelfandRadius(L)^{1/q}` there is `K` with `‖X n‖ ≤ K Rⁿ` for all `n`. -/
theorem exists_norm_le_mul_pow_of_le_mul {X : ℕ → Matrix ι ι ℝ} (hX : ∀ n i j, 0 ≤ X n i j)
    {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j) {q : ℕ} (hq : q ≠ 0)
    (hdom : ∀ n i j, X (n + q) i j ≤ (X n * L) i j) {R : ℝ}
    (hR : gelfandRadius L ^ (q : ℝ)⁻¹ < R) : ∃ K, ∀ n, ‖X n‖ ≤ K * R ^ n := by
  have hR0 : 0 < R := lt_of_le_of_lt (by positivity) hR
  have hRq : gelfandRadius L < R ^ q := by
    have h := Real.rpow_lt_rpow (by positivity) hR (by positivity : (0 : ℝ) < q)
    rwa [← Real.rpow_mul (gelfandRadius_nonneg L), inv_mul_cancel₀ (by exact_mod_cast hq),
      Real.rpow_one, Real.rpow_natCast] at h
  obtain ⟨D, hD, hLk⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt L hRq
  set B := ∑ r ∈ Finset.range q, ‖X r‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun r _ => norm_nonneg _
  set E := max 1 R⁻¹ with hE
  refine ⟨B * D * E ^ q, fun n => ?_⟩
  obtain ⟨r, k, hr, rfl⟩ : ∃ r k, r < q ∧ n = r + k * q :=
    ⟨n % q, n / q, Nat.mod_lt n (Nat.pos_of_ne_zero hq), by
      rw [Nat.mul_comm]; exact (Nat.mod_add_div n q).symm⟩
  have h1 : ‖X (r + k * q)‖ ≤ ‖X r‖ * ‖L ^ k‖ :=
    (norm_le_norm_of_nonneg_of_apply_le (hX _) (apply_le_mul_pow_of_le_mul hL hdom r k)).trans
      (linfty_opNorm_mul _ _)
  have h2 : ‖X r‖ ≤ B := Finset.single_le_sum (f := fun r => ‖X r‖)
    (fun i _ => norm_nonneg _) (Finset.mem_range.2 hr)
  have h3 : (R ^ q) ^ k ≤ E ^ q * R ^ (r + k * q) := by
    have e : (R ^ q) ^ k = R⁻¹ ^ r * R ^ (r + k * q) := by
      rw [pow_add, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hR0.ne'), one_mul,
        ← pow_mul, mul_comm k q]
    rw [e]
    gcongr
    calc R⁻¹ ^ r ≤ E ^ r := pow_le_pow_left₀ (by positivity) (le_max_right _ _) r
      _ ≤ E ^ q := pow_le_pow_right₀ (le_max_left _ _) hr.le
  calc ‖X (r + k * q)‖ ≤ ‖X r‖ * ‖L ^ k‖ := h1
    _ ≤ B * (D * (R ^ q) ^ k) := mul_le_mul h2 (hLk k) (norm_nonneg _) hB0
    _ ≤ B * (D * (E ^ q * R ^ (r + k * q))) := by gcongr
    _ = B * D * E ^ q * R ^ (r + k * q) := by ring

/-- **Variational upper bound.** Let `X n ≥ 0` and `L ≥ 0` be real matrices with
`X (n + q) ≤ X n L` entrywise for every `n`, where `q ≥ 1`. Then
`limsup ‖X n‖^{1/n} ≤ gelfandRadius(L)^{1/q}`. -/
theorem limsup_rpow_inv_le_of_le_mul {X : ℕ → Matrix ι ι ℝ} (hX : ∀ n i j, 0 ≤ X n i j)
    {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j) {q : ℕ} (hq : q ≠ 0)
    (hdom : ∀ n i j, X (n + q) i j ≤ (X n * L) i j) :
    limsup (fun n : ℕ => ‖X n‖ ^ (n : ℝ)⁻¹) atTop ≤ gelfandRadius L ^ (q : ℝ)⁻¹ := by
  refine le_of_forall_gt_imp_ge_of_dense fun R hR => ?_
  obtain ⟨R₁, hR₁, hR₁R⟩ := exists_between hR
  obtain ⟨K, hK⟩ := exists_norm_le_mul_pow_of_le_mul hX hL hq hdom hR₁
  have hR₁0 : 0 < R₁ := lt_of_le_of_lt (by positivity) hR₁
  have hK1 : 0 < max K 1 := lt_max_of_lt_right one_pos
  have hlim : Tendsto (fun n : ℕ => max K 1 ^ (n : ℝ)⁻¹ * R₁) atTop (𝓝 R₁) := by
    simpa using (Real.tendsto_const_rpow_inv hK1).mul_const R₁
  have hev : ∀ᶠ n : ℕ in atTop, ‖X n‖ ^ (n : ℝ)⁻¹ ≤ R := by
    filter_upwards [hlim.eventually (gt_mem_nhds hR₁R), eventually_ne_atTop 0] with n hn hn0
    refine le_trans ?_ hn.le
    calc ‖X n‖ ^ (n : ℝ)⁻¹ ≤ (max K 1 * R₁ ^ n) ^ (n : ℝ)⁻¹ :=
          Real.rpow_le_rpow (norm_nonneg _)
            ((hK n).trans (by gcongr; exact le_max_left _ _)) (by positivity)
      _ = max K 1 ^ (n : ℝ)⁻¹ * R₁ := by
          rw [Real.mul_rpow hK1.le (by positivity), Real.pow_rpow_inv_natCast hR₁0.le hn0]
  exact limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop fun n => Real.rpow_nonneg (norm_nonneg _) _) hev

/-- **Variational upper bound, the norm half.** Let `b n ≥ 0` with `b_n^{1/n} → λ ≥ 1`, and let
`L q` be real matrices with `‖L q‖ ≤ 1 + A ∑_{k<q} b_k` for some `A ≥ 0`. Then
`limsup gelfandRadius(L q)^{1/q} ≤ λ`. -/
theorem limsup_gelfandRadius_rpow_inv_le {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {lam : ℝ}
    (hlam : 1 ≤ lam) (hlim : Tendsto (fun n : ℕ => b n ^ (n : ℝ)⁻¹) atTop (𝓝 lam)) {A : ℝ}
    (hA : 0 ≤ A) {L : ℕ → Matrix ι ι ℝ} (hL : ∀ q, ‖L q‖ ≤ 1 + A * ∑ k ∈ Finset.range q, b k) :
    limsup (fun q : ℕ => gelfandRadius (L q) ^ (q : ℝ)⁻¹) atTop ≤ lam := by
  refine le_of_forall_gt_imp_ge_of_dense fun R hR => ?_
  obtain ⟨R₁, hR₁, hR₁R⟩ := exists_between hR
  have hR₁1 : 1 ≤ R₁ := hlam.trans hR₁.le
  have hR₁0 : 0 < R₁ := one_pos.trans_le hR₁1
  -- `b k ≤ R₁ᵏ` from some `N` on, so `b k ≤ C₀ + R₁ᵏ` for every `k`
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hlim.eventually (gt_mem_nhds hR₁)).and (eventually_ne_atTop 0))
  set C₀ := ∑ k ∈ Finset.range N, b k with hC₀
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun k _ => hb k
  have hbk : ∀ k, b k ≤ C₀ + R₁ ^ k := by
    intro k
    rcases lt_or_ge k N with hk | hk
    · have := Finset.single_le_sum (f := b) (fun i _ => hb i) (Finset.mem_range.2 hk)
      linarith [pow_nonneg hR₁0.le k]
    · obtain ⟨h1, h2⟩ := hN k hk
      have := (Real.rpow_inv_le_iff_of_pos (hb k) hR₁0.le
        (by exact_mod_cast Nat.pos_of_ne_zero h2)).1 h1.le
      rw [Real.rpow_natCast] at this
      linarith
  -- `‖L q‖ ≤ H q R₁^q` with `H q = 1 + A (C₀ + 1) q`
  set c := A * (C₀ + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hLq : ∀ q : ℕ, ‖L q‖ ≤ (1 + c * q) * R₁ ^ q := by
    intro q
    have hRq : 1 ≤ R₁ ^ q := one_le_pow₀ hR₁1
    have hsum : ∑ k ∈ Finset.range q, b k ≤ q * (C₀ + R₁ ^ q) := by
      calc ∑ k ∈ Finset.range q, b k ≤ ∑ _k ∈ Finset.range q, (C₀ + R₁ ^ q) :=
            Finset.sum_le_sum fun k hk => (hbk k).trans (by
              gcongr
              exact (Finset.mem_range.1 hk).le)
        _ = q * (C₀ + R₁ ^ q) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ‖L q‖ ≤ 1 + A * (q * (C₀ + R₁ ^ q)) := (hL q).trans (by gcongr)
      _ ≤ (1 + c * q) * R₁ ^ q := by
          rw [hc]
          have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
          have : A * q * C₀ ≤ A * q * C₀ * R₁ ^ q :=
            le_mul_of_one_le_right (by positivity) hRq
          nlinarith
  -- `(1 + c q)^{1/q} → 1`
  have hpoly : Tendsto (fun q : ℕ => (1 + c * q) ^ (q : ℝ)⁻¹) atTop (𝓝 1) := by
    have h := Real.tendsto_rpow_inv_of_log_div (H := fun q : ℕ => 1 + c * q)
      (fun q => by positivity)
      (Real.tendsto_log_div_zero_of_poly (A := 1) (B := c) (fun q => by
        simp only [le_add_iff_nonneg_right]; positivity) (fun q => by
          have hq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
            rcases Nat.eq_zero_or_pos q with h0 | h0
            · simp [h0]
            · have : (1 : ℝ) ≤ q := by exact_mod_cast h0
              nlinarith
          simp only [add_le_add_iff_left]
          exact mul_le_mul_of_nonneg_left hq hc0))
    rwa [Real.exp_zero] at h
  have hlim' : Tendsto (fun q : ℕ => (1 + c * q) ^ (q : ℝ)⁻¹ * R₁) atTop (𝓝 R₁) := by
    simpa using hpoly.mul_const R₁
  have hev : ∀ᶠ q : ℕ in atTop, gelfandRadius (L q) ^ (q : ℝ)⁻¹ ≤ R := by
    filter_upwards [hlim'.eventually (gt_mem_nhds hR₁R), eventually_ne_atTop 0] with q hq hq0
    refine le_trans ?_ hq.le
    calc gelfandRadius (L q) ^ (q : ℝ)⁻¹ ≤ ((1 + c * q) * R₁ ^ q) ^ (q : ℝ)⁻¹ :=
          Real.rpow_le_rpow (gelfandRadius_nonneg _) ((gelfandRadius_le_norm _).trans (hLq q))
            (by positivity)
      _ = (1 + c * q) ^ (q : ℝ)⁻¹ * R₁ := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.pow_rpow_inv_natCast hR₁0.le hq0]
  exact limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop fun q => Real.rpow_nonneg (gelfandRadius_nonneg _) _) hev

end Variational

/-! ### The `2 × 2` case -/

section TwoByTwo

open Polynomial

/-- `|tr X| ≤ (card ι) ‖X‖` for the `ℓ∞` operator norm. -/
lemma abs_trace_le_card_mul_norm {ι : Type*} [Fintype ι] (X : Matrix ι ι ℝ) :
    |X.trace| ≤ Fintype.card ι * ‖X‖ := by
  calc |X.trace| = |∑ i, X i i| := rfl
    _ ≤ ∑ i, |X i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖X‖ := Finset.sum_le_sum fun i _ => by
        simpa [Real.norm_eq_abs] using norm_apply_le_linfty_opNorm X i i
    _ = Fintype.card ι * ‖X‖ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Hyperbolic `SL₂(ℝ)`.** If `det M = 1` and `tr M = l + l⁻¹` with `l > 1`, then
`gelfandRadius M = l`. The proof uses only the Chebyshev form of the powers of `M` and the
trace: no eigenvector, and no complex numbers. -/
theorem gelfandRadius_eq_of_det_eq_one (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1)
    {l : ℝ} (hl : 1 < l) (htr : M.trace = l + l⁻¹) : gelfandRadius M = l := by
  have hl0 : l ≠ 0 := by positivity
  have hpos : 0 < l - l⁻¹ := by
    have : l⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
    linarith
  set s : ℕ → ℝ := fun k => (Chebyshev.S ℝ k).eval (l + l⁻¹) with hs
  have hsk : ∀ k : ℕ, s k = (l ^ (k + 1) - l⁻¹ ^ (k + 1)) / (l - l⁻¹) := fun k => by
    rw [eq_div_iff hpos.ne']; exact Chebyshev.S_eval_add_inv_mul_sub_inv hl0 k
  have hinv : ∀ k : ℕ, 0 ≤ l⁻¹ ^ k ∧ l⁻¹ ^ k ≤ 1 := fun k =>
    ⟨by positivity, pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hl.le)⟩
  -- `M^(k+2) = s(k+1) M - s(k) 1`
  have hM : ∀ k : ℕ, M ^ (k + 2) = s (k + 1) • M - s k • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro k
    rw [pow_eq_S_eval_trace_smul_sub M hdet, htr]
    have e1 : (((k + 2 : ℕ) : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : (((k + 2 : ℕ) : ℤ) - 2) = ((k : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2]
  set C := (‖M‖ + 1) / (l - l⁻¹) with hC
  have hsb : ∀ k : ℕ, 0 ≤ s k ∧ s k ≤ l ^ (k + 1) / (l - l⁻¹) := by
    intro k
    rw [hsk]
    constructor
    · apply div_nonneg _ hpos.le
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ l⁻¹)
        (inv_lt_one_of_one_lt₀ hl).le (k + 1)
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hl.le (k + 1)
      simp only [one_pow] at *
      linarith
    · apply div_le_div_of_nonneg_right _ hpos.le
      linarith [(hinv (k + 1)).1]
  have hup : ∀ k : ℕ, ‖M ^ (k + 2)‖ ≤ C * l ^ (k + 2) := by
    intro k
    rw [hM k]
    have hs1 := hsb (k + 1)
    have hs0 := hsb k
    calc ‖s (k + 1) • M - s k • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖
        ≤ ‖s (k + 1) • M‖ + ‖s k • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ := norm_sub_le _ _
      _ ≤ s (k + 1) * ‖M‖ + s k * 1 := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs1.1,
            abs_of_nonneg hs0.1, norm_one]
      _ ≤ l ^ (k + 2) / (l - l⁻¹) * ‖M‖ + l ^ (k + 2) / (l - l⁻¹) * 1 := by
          have hA : l ^ (k + 1) / (l - l⁻¹) ≤ l ^ (k + 2) / (l - l⁻¹) :=
            div_le_div_of_nonneg_right (pow_le_pow_right₀ hl.le (by omega)) hpos.le
          exact add_le_add (mul_le_mul_of_nonneg_right hs1.2 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hs0.2.trans hA) zero_le_one)
      _ = C * l ^ (k + 2) := by rw [hC]; field_simp
  have hlow : ∀ k : ℕ, (1 / 2) * l ^ (k + 2) ≤ ‖M ^ (k + 2)‖ := by
    intro k
    have htrace : (M ^ (k + 2)).trace = l ^ (k + 2) + l⁻¹ ^ (k + 2) := by
      rw [hM k, trace_sub, trace_smul, trace_smul, trace_one, htr]
      simp only [Fintype.card_fin, smul_eq_mul]
      rw [hsk (k + 1), hsk k]
      have hlm : l * l⁻¹ = 1 := mul_inv_cancel₀ hl0
      have key : (l ^ (k + 1 + 1) - l⁻¹ ^ (k + 1 + 1)) * (l + l⁻¹) -
          2 * (l ^ (k + 1) - l⁻¹ ^ (k + 1)) = (l ^ (k + 2) + l⁻¹ ^ (k + 2)) * (l - l⁻¹) := by
        linear_combination 2 * (l ^ (k + 1) - l⁻¹ ^ (k + 1)) * hlm
      calc _ = ((l ^ (k + 1 + 1) - l⁻¹ ^ (k + 1 + 1)) * (l + l⁻¹) -
            2 * (l ^ (k + 1) - l⁻¹ ^ (k + 1))) / (l - l⁻¹) := by push_cast; ring
        _ = (l ^ (k + 2) + l⁻¹ ^ (k + 2)) * (l - l⁻¹) / (l - l⁻¹) := by rw [key]
        _ = _ := mul_div_cancel_right₀ _ hpos.ne'
    have := abs_trace_le_card_mul_norm (M ^ (k + 2))
    rw [htrace, abs_of_nonneg (by positivity), Fintype.card_fin, Nat.cast_ofNat] at this
    linarith [(hinv (k + 2)).1]
  have hlim : Tendsto (fun n : ℕ => ‖M ^ n‖ ^ (n : ℝ)⁻¹) atTop (𝓝 l) := by
    refine Real.tendsto_rpow_inv_of_bounds (H := fun n => l ^ n) (c := 1 / 2)
      (C := max C 1) (by norm_num) (by positivity) (fun n => by positivity) ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
      exact hlow k
    · filter_upwards [eventually_ge_atTop 2] with n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
      exact (hup k).trans (by gcongr; exact le_max_left _ _)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (Real.pow_rpow_inv_natCast (by positivity) (by omega)).symm
  exact tendsto_nhds_unique (tendsto_gelfandRadius M) hlim

/-- The Thurston matrix `[[1, aμ], [0, 1]]` of a multitwist along the first part of a bipartite
configuration with Perron eigenvalue `μ`, raised to the power `a` (W. Thurston, Bull. Amer.
Math. Soc. 19 (1988)). -/
def thurstonA (a μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, a * μ; 0, 1]

/-- The Thurston matrix `[[1, 0], [bμ, 1]]` of a multitwist along the second part of a bipartite
configuration with Perron eigenvalue `μ`, raised to the power `-b`. -/
def thurstonB (b μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; b * μ, 1]

theorem det_thurstonA_mul_thurstonB (a b μ : ℝ) : (thurstonA a μ * thurstonB b μ).det = 1 := by
  simp [thurstonA, thurstonB, det_fin_two]

theorem trace_thurstonA_mul_thurstonB (a b μ : ℝ) :
    (thurstonA a μ * thurstonB b μ).trace = 2 + a * b * μ ^ 2 := by
  simp [thurstonA, thurstonB, trace_fin_two]; ring

/-- **The rate of two multitwists**: `gelfandRadius(T_A T_B) = λ` with `λ + λ⁻¹ = 2 + abμ²`,
for the Thurston matrices `T_A = [[1, aμ], [0, 1]]`, `T_B = [[1, 0], [bμ, 1]]`. -/
theorem gelfandRadius_thurston {a b μ l : ℝ} (hl : 1 < l) (h : l + l⁻¹ = 2 + a * b * μ ^ 2) :
    gelfandRadius (thurstonA a μ * thurstonB b μ) = l :=
  gelfandRadius_eq_of_det_eq_one _ (det_thurstonA_mul_thurstonB a b μ) hl
    (by rw [trace_thurstonA_mul_thurstonB, h])

/-- **Two squared twists**: for `a = b = 2` and `μ = g > 0` the rate is
`λ = 1 + 2g² + 2g√(g² + 1)`. -/
theorem gelfandRadius_thurston_two_two {g : ℝ} (hg : 0 < g) :
    gelfandRadius (thurstonA 2 g * thurstonB 2 g) = 1 + 2 * g ^ 2 + 2 * g * √(g ^ 2 + 1) := by
  have hsq : √(g ^ 2 + 1) ^ 2 = g ^ 2 + 1 := Real.sq_sqrt (by positivity)
  set l := 1 + 2 * g ^ 2 + 2 * g * √(g ^ 2 + 1)
  have hl : 1 < l := by
    have : 0 < g * √(g ^ 2 + 1) := by positivity
    nlinarith
  have hinv : l⁻¹ = 1 + 2 * g ^ 2 - 2 * g * √(g ^ 2 + 1) := by
    apply inv_eq_of_mul_eq_one_right
    nlinarith [hsq]
  apply gelfandRadius_thurston hl
  rw [hinv]; ring

end TwoByTwo

end Matrix
