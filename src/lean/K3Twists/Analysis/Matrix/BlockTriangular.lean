/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.GelfandRadius
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Block-triangular certificates

Let `L ≥ 0` be a real square matrix that is block upper triangular for a grading
`blk : ι → ℕ` with values below `c`: `L i j = 0` whenever `blk j < blk i`. Suppose the diagonal
blocks share one subinvariant vector `v ≥ m > 0`,

  `∑_{blk j = blk i} L i j v j ≤ ρ v i` for every `i`,

and let `K` bound the whole matrix on `v`, `L v ≤ K v`. Then for every `k`

  `‖Lᵏ‖ ≤ 3 (‖v‖ / m) (1 + K/ρ)^{c-1} (1 + k)^{c-1} ρᵏ`

(`Matrix.norm_pow_le_of_blockTriangular`): a chain of `c` blocks costs at most a polynomial factor
of degree `c - 1` above the rate `ρ` of the blocks, whatever the blocks are linked by. No
irreducibility or primitivity of the blocks is used, only the certificates. In particular
`gelfandRadius L ≤ ρ` (`Matrix.gelfandRadius_le_of_blockTriangular`), and a leaf-count domination
`X (n + q) ≤ X n L` by such a tower matrix gives the polynomial bound
`‖X n‖ ≤ B (1 + n)^{c-1} λⁿ` with `ρ = λ^q` (`Matrix.norm_le_of_le_mul_of_blockTriangular`).

The proof applies the one-vector certificate `Matrix.norm_pow_le_of_mulVec_le` to the rescaled
vector `v'_i = v_i ε^{blk i}`. Entries of `L` linking a block to a later one meet a factor `ε`,
so `L v' ≤ (ρ + εK) v'`; the choice `ε = ρ/(ρ + K(k + 1))` for the `k`-th power makes
`(ρ + εK)ᵏ ≤ 3ρᵏ` while `max v'/min v'` grows only like `(1 + k)^{c-1}`.
-/

open Filter Topology

namespace Matrix

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(1 + 1/(k + 1))ᵏ ≤ 3`. -/
lemma one_add_inv_pow_le_three (k : ℕ) : (1 + 1 / ((k : ℝ) + 1)) ^ k ≤ 3 := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  calc (1 + 1 / ((k : ℝ) + 1)) ^ k ≤ (Real.exp (1 / ((k : ℝ) + 1))) ^ k := by
        gcongr
        linarith [Real.add_one_le_exp (1 / ((k : ℝ) + 1))]
    _ = Real.exp (k / ((k : ℝ) + 1)) := by
        rw [← Real.exp_nat_mul, mul_one_div]
    _ ≤ Real.exp 1 := by
        gcongr
        rw [div_le_one hk]
        linarith
    _ ≤ 3 := Real.exp_one_lt_three.le

/-- **The block-triangular chain bound.** For `L ≥ 0` block upper triangular for `blk` with values
below `c`, a common subinvariant vector `v ≥ m > 0` of the diagonal blocks with ratio `ρ > 0`,
and `L v ≤ K v`: `‖Lᵏ‖ ≤ 3 (‖v‖ / m) (1 + K/ρ)^{c-1} (1 + k)^{c-1} ρᵏ`. -/
theorem norm_pow_le_of_blockTriangular {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j)
    (blk : ι → ℕ) {c : ℕ} (hblk : ∀ i, blk i < c) (htri : ∀ i j, blk j < blk i → L i j = 0)
    {v : ι → ℝ} {m ρ K : ℝ} (hm : 0 < m) (hvm : ∀ i, m ≤ v i) (hρ : 0 < ρ)
    (hdiag : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => blk j = blk i), L i j * v j ≤ ρ * v i)
    (hK : L *ᵥ v ≤ K • v) (k : ℕ) :
    ‖L ^ k‖ ≤ 3 * (‖v‖ / m) * (1 + K / ρ) ^ (c - 1) * (1 + k) ^ (c - 1) * ρ ^ k := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have h1 : L ^ k = 0 := Subsingleton.elim _ _
    have h2 : v = 0 := Subsingleton.elim _ _
    simp [h1, h2]
  have hv0 : ∀ i, 0 < v i := fun i => hm.trans_le (hvm i)
  -- `K ≥ 0`, from `0 ≤ (L v)_{i₀} ≤ K v_{i₀}`
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ (L *ᵥ v) i₀ := mulVec_nonneg hL (fun j => (hv0 j).le) i₀
    have h2 := hK i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    by_contra h
    nlinarith [hv0 i₀]
  set ε : ℝ := ρ / (ρ + K * (k + 1)) with hε
  have hden : 0 < ρ + K * (k + 1) := by
    have : 0 ≤ K * (k + 1) := mul_nonneg hK0 (by positivity)
    linarith
  have hε0 : 0 < ε := div_pos hρ hden
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one hden]
    nlinarith
  have hεK : ε * K ≤ ρ / (k + 1) := by
    rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ hden (by positivity)]
    nlinarith [mul_nonneg hK0 hρ.le]
  -- the rescaled vector
  set v' : ι → ℝ := fun i => v i * ε ^ blk i with hv'
  have hv'pos : ∀ i, m * ε ^ (c - 1) ≤ v' i := by
    intro i
    have h1 : ε ^ (c - 1) ≤ ε ^ blk i :=
      pow_le_pow_of_le_one hε0.le hε1 (by have := hblk i; omega)
    calc m * ε ^ (c - 1) ≤ v i * ε ^ (c - 1) := by gcongr; exact hvm i
      _ ≤ v i * ε ^ blk i := by gcongr; exact (hv0 i).le
  have hv'le : ‖v'‖ ≤ ‖v‖ := by
    refine norm_le_norm_of_nonneg_of_le (fun i => mul_nonneg (hv0 i).le (pow_nonneg hε0.le _))
      fun i => ?_
    calc v' i = v i * ε ^ blk i := rfl
      _ ≤ v i * 1 := by gcongr; exacts [(hv0 i).le, pow_le_one₀ hε0.le hε1]
      _ = v i := mul_one _
  -- `L v' ≤ (ρ + εK) v'`
  have hsub : L *ᵥ v' ≤ (ρ + ε * K) • v' := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => blk j = blk i)]
    have hin : ∑ j ∈ Finset.univ.filter (fun j => blk j = blk i), L i j * v' j ≤
        ε ^ blk i * (ρ * v i) := by
      calc ∑ j ∈ Finset.univ.filter (fun j => blk j = blk i), L i j * v' j
          = ε ^ blk i * ∑ j ∈ Finset.univ.filter (fun j => blk j = blk i), L i j * v j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j hj => ?_
            simp only [hv', (Finset.mem_filter.1 hj).2]
            ring
        _ ≤ ε ^ blk i * (ρ * v i) := by gcongr; exact hdiag i
    have hout : ∑ j ∈ Finset.univ.filter (fun j => ¬blk j = blk i), L i j * v' j ≤
        ε ^ (blk i + 1) * (K * v i) := by
      calc ∑ j ∈ Finset.univ.filter (fun j => ¬blk j = blk i), L i j * v' j
          ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬blk j = blk i),
              ε ^ (blk i + 1) * (L i j * v j) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hne := (Finset.mem_filter.1 hj).2
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · rw [htri i j hlt]
              simp
            · calc L i j * v' j = L i j * v j * ε ^ blk j := by simp only [hv']; ring
                _ ≤ L i j * v j * ε ^ (blk i + 1) :=
                    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hε0.le hε1 hgt)
                      (mul_nonneg (hL i j) (hv0 j).le)
                _ = ε ^ (blk i + 1) * (L i j * v j) := by ring
        _ ≤ ∑ j, ε ^ (blk i + 1) * (L i j * v j) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ =>
              mul_nonneg (pow_nonneg hε0.le _) (mul_nonneg (hL i j) (hv0 j).le)
        _ = ε ^ (blk i + 1) * (L *ᵥ v) i := by rw [← Finset.mul_sum]; rfl
        _ ≤ ε ^ (blk i + 1) * (K * v i) := by
            gcongr
            simpa using hK i
    calc _ ≤ ε ^ blk i * (ρ * v i) + ε ^ (blk i + 1) * (K * v i) := add_le_add hin hout
      _ = (ρ + ε * K) * (v i * ε ^ blk i) := by ring
  -- the one-vector certificate for `v'`
  have hm' : 0 < m * ε ^ (c - 1) := by positivity
  have hcert := norm_pow_le_of_mulVec_le hL hm' hv'pos hsub k
  -- `(ρ + εK)ᵏ ≤ 3ρᵏ` and `1/ε^{c-1} ≤ ((1 + K/ρ)(1 + k))^{c-1}`
  have hpow : (ρ + ε * K) ^ k ≤ 3 * ρ ^ k := by
    calc (ρ + ε * K) ^ k ≤ (ρ * (1 + 1 / ((k : ℝ) + 1))) ^ k := by
          refine pow_le_pow_left₀ (add_nonneg hρ.le (mul_nonneg hε0.le hK0)) ?_ k
          calc ρ + ε * K ≤ ρ + ρ / (k + 1) := by linarith
            _ = ρ * (1 + 1 / ((k : ℝ) + 1)) := by ring
      _ = ρ ^ k * (1 + 1 / ((k : ℝ) + 1)) ^ k := by rw [mul_pow]
      _ ≤ ρ ^ k * 3 := by gcongr; exact one_add_inv_pow_le_three k
      _ = 3 * ρ ^ k := mul_comm _ _
  have hinv : (ε ^ (c - 1))⁻¹ ≤ (1 + K / ρ) ^ (c - 1) * (1 + k) ^ (c - 1) := by
    rw [← inv_pow, ← mul_pow]
    gcongr
    rw [hε, inv_div, div_le_iff₀ hρ]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : 0 ≤ K * k := mul_nonneg hK0 this
    field_simp
    nlinarith
  calc ‖L ^ k‖ ≤ ‖v'‖ / (m * ε ^ (c - 1)) * (ρ + ε * K) ^ k := hcert
    _ ≤ ‖v‖ / (m * ε ^ (c - 1)) * (3 * ρ ^ k) := by gcongr
    _ = 3 * (‖v‖ / m) * (ε ^ (c - 1))⁻¹ * ρ ^ k := by
        rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
        ring
    _ ≤ 3 * (‖v‖ / m) * ((1 + K / ρ) ^ (c - 1) * (1 + k) ^ (c - 1)) * ρ ^ k := by
        gcongr
    _ = 3 * (‖v‖ / m) * (1 + K / ρ) ^ (c - 1) * (1 + k) ^ (c - 1) * ρ ^ k := by ring

/-- A polynomial factor does not change the rate: if `‖Lᵏ‖ ≤ C (1 + k)^s ρᵏ` for every `k`, with
`ρ > 0`, then `gelfandRadius L ≤ ρ`. -/
theorem gelfandRadius_le_of_norm_pow_le_poly {L : Matrix ι ι ℝ} {C ρ : ℝ} {s : ℕ} (hρ : 0 < ρ)
    (h : ∀ k : ℕ, ‖L ^ k‖ ≤ C * (1 + k) ^ s * ρ ^ k) : gelfandRadius L ≤ ρ := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := hρ.trans hr
  set q := ρ / r with hq
  have hq0 : 0 < q := div_pos hρ hr0
  have hq1 : |q| < 1 := by rw [abs_of_pos hq0, div_lt_one hr0]; exact hr
  obtain ⟨D, hD⟩ := (tendsto_pow_const_mul_const_pow_of_abs_lt_one s hq1).bddAbove_range
  refine gelfandRadius_le_of_bound hr0.le (C := C * (D / q)) fun k => (h k).trans ?_
  have hk := hD ⟨k + 1, rfl⟩
  have hC : 0 ≤ C := by
    have := (norm_nonneg (L ^ 0)).trans (h 0)
    simp only [CharP.cast_eq_zero, add_zero, one_pow, mul_one, pow_zero] at this
    exact this
  have hqr : q * r = ρ := by
    rw [hq]
    field_simp
  have e : (1 + (k : ℝ)) ^ s * ρ ^ k = (((k + 1 : ℕ) : ℝ) ^ s * q ^ (k + 1)) / q * r ^ k := by
    rw [pow_succ, ← mul_assoc, mul_div_cancel_right₀ _ hq0.ne', mul_assoc, ← mul_pow, hqr]
    push_cast
    ring
  calc C * (1 + k) ^ s * ρ ^ k = C * ((1 + (k : ℝ)) ^ s * ρ ^ k) := by ring
    _ = C * ((((k + 1 : ℕ) : ℝ) ^ s * q ^ (k + 1)) / q * r ^ k) := by rw [e]
    _ ≤ C * (D / q * r ^ k) := by
        gcongr
    _ = C * (D / q) * r ^ k := by ring

/-- **The rate of a block-triangular tower matrix** is at most the common ratio of its diagonal
certificates. -/
theorem gelfandRadius_le_of_blockTriangular {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j)
    (blk : ι → ℕ) {c : ℕ} (hblk : ∀ i, blk i < c) (htri : ∀ i j, blk j < blk i → L i j = 0)
    {v : ι → ℝ} {m ρ K : ℝ} (hm : 0 < m) (hvm : ∀ i, m ≤ v i) (hρ : 0 < ρ)
    (hdiag : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => blk j = blk i), L i j * v j ≤ ρ * v i)
    (hK : L *ᵥ v ≤ K • v) : gelfandRadius L ≤ ρ :=
  gelfandRadius_le_of_norm_pow_le_poly (C := 3 * (‖v‖ / m) * (1 + K / ρ) ^ (c - 1)) (s := c - 1)
    hρ fun k => norm_pow_le_of_blockTriangular hL blk hblk htri hm hvm hρ hdiag hK k

/-- **The tower certificate.** If `X (n + q) ≤ X n L` entrywise for nonnegative matrices, `q ≥ 1`,
and `L` is block triangular with `c` blocks whose certificates have ratio `ρ = λ^q`, `λ ≥ 1`, then
`‖X n‖ ≤ B (1 + n)^{c-1} λⁿ` for every `n`, with
`B = 3 (∑_{r<q} ‖X r‖) (‖v‖ / m) (1 + K/ρ)^{c-1}`. A certified lower bound `λ ≤ rate` then makes
this the polynomial bound at the true rate. -/
theorem norm_le_of_le_mul_of_blockTriangular {X : ℕ → Matrix ι ι ℝ} (hX : ∀ n i j, 0 ≤ X n i j)
    {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j) {q : ℕ} (hq : q ≠ 0)
    (hdom : ∀ n i j, X (n + q) i j ≤ (X n * L) i j)
    (blk : ι → ℕ) {c : ℕ} (hblk : ∀ i, blk i < c) (htri : ∀ i j, blk j < blk i → L i j = 0)
    {v : ι → ℝ} {m lam K : ℝ} (hm : 0 < m) (hvm : ∀ i, m ≤ v i) (hlam : 1 ≤ lam)
    (hdiag : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => blk j = blk i), L i j * v j ≤
      lam ^ q * v i)
    (hK : L *ᵥ v ≤ K • v) (n : ℕ) :
    ‖X n‖ ≤ 3 * (∑ r ∈ Finset.range q, ‖X r‖) * (‖v‖ / m) * (1 + K / lam ^ q) ^ (c - 1) *
      (1 + n) ^ (c - 1) * lam ^ n := by
  have hρ : 0 < lam ^ q := pow_pos (one_pos.trans_le hlam) q
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have hXn : X n = 0 := Subsingleton.elim _ _
    have hXr : ∀ r, ‖X r‖ = 0 := fun r => by rw [Subsingleton.elim (X r) 0, norm_zero]
    simp [hXn, hXr]
  have hK0 : 0 ≤ K := by
    have hv0 : 0 < v i₀ := hm.trans_le (hvm i₀)
    have h1 : 0 ≤ (L *ᵥ v) i₀ := mulVec_nonneg hL (fun j => (hm.trans_le (hvm j)).le) i₀
    have h2 := hK i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    by_contra h
    nlinarith
  obtain ⟨r, k, hr, rfl⟩ : ∃ r k, r < q ∧ n = r + k * q :=
    ⟨n % q, n / q, Nat.mod_lt n (Nat.pos_of_ne_zero hq), by
      rw [Nat.mul_comm]; exact (Nat.mod_add_div n q).symm⟩
  set B := ∑ r ∈ Finset.range q, ‖X r‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun r _ => norm_nonneg _
  have h1 : ‖X (r + k * q)‖ ≤ ‖X r‖ * ‖L ^ k‖ :=
    (norm_le_norm_of_nonneg_of_apply_le (hX _) (apply_le_mul_pow_of_le_mul hL hdom r k)).trans
      (linfty_opNorm_mul _ _)
  have h2 : ‖X r‖ ≤ B := Finset.single_le_sum (f := fun r => ‖X r‖)
    (fun i _ => norm_nonneg _) (Finset.mem_range.2 hr)
  have h3 := norm_pow_le_of_blockTriangular hL blk hblk htri hm hvm hρ hdiag hK k
  have hv : 0 ≤ ‖v‖ / m := div_nonneg (norm_nonneg _) hm.le
  have hk : (1 + (k : ℝ)) ^ (c - 1) ≤ (1 + ((r + k * q : ℕ) : ℝ)) ^ (c - 1) := by
    have hkn : k ≤ r + k * q := by
      have : k ≤ k * q := Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hq)
      omega
    gcongr
  have hl : (lam ^ q) ^ k ≤ lam ^ (r + k * q) := by
    rw [← pow_mul, mul_comm q k]
    exact pow_le_pow_right₀ hlam (by omega)
  calc ‖X (r + k * q)‖ ≤ ‖X r‖ * ‖L ^ k‖ := h1
    _ ≤ B * (3 * (‖v‖ / m) * (1 + K / lam ^ q) ^ (c - 1) * (1 + k) ^ (c - 1) * (lam ^ q) ^ k) :=
        mul_le_mul h2 h3 (norm_nonneg _) hB0
    _ ≤ B * (3 * (‖v‖ / m) * (1 + K / lam ^ q) ^ (c - 1) *
          (1 + ((r + k * q : ℕ) : ℝ)) ^ (c - 1) * lam ^ (r + k * q)) := by
        gcongr
    _ = _ := by ring

end Matrix
