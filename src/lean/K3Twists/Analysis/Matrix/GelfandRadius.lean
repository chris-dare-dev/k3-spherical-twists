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
