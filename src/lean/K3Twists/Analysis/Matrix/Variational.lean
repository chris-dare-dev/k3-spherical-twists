/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.GelfandRadius

/-!
# The variational formula: the infimum over periods is a limit

Let `X n ≥ 0` be real matrices whose norms grow at the rate `λ ≥ 1`, `‖X n‖^{1/n} → λ`. For each
period `q ≥ 1` let `L q ≥ 0` be a leaf matrix that dominates one period,
`X (n + q) ≤ X n (L q)` entrywise for every `n`, and suppose the leaf matrices satisfy the norm
bound `‖L q‖ ≤ 1 + A ∑_{k<q} ‖X k‖` of a tower built letter by letter. The two variational
bounds of `GelfandRadius.lean` give `λ ≤ gelfandRadius(L q)^{1/q}` for every `q ≥ 1`
(`Matrix.limsup_rpow_inv_le_of_le_mul`) and `limsup gelfandRadius(L q)^{1/q} ≤ λ`
(`Matrix.limsup_gelfandRadius_rpow_inv_le`). Together, with a bound on the sequence, the periods
converge and the infimum is their limit:

* `Matrix.tendsto_gelfandRadius_rpow_inv_of_le_mul`: `gelfandRadius(L q)^{1/q} → λ`;
* `Matrix.iInf_gelfandRadius_rpow_inv_eq`: `⨅_{q ≥ 1} gelfandRadius(L q)^{1/q} = λ`.

So every period certifies an upper bound for the rate, and the certificates converge to it.
-/

open Filter Topology

namespace Matrix

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Under the norm bound, `gelfandRadius(L q)^{1/q}` is bounded: `‖X k‖ ≤ C₀ + Rᵏ` with
`R = λ + 1` gives `‖L q‖ ≤ (1 + c q) R^q ≤ ((1 + c) R)^q` by Bernoulli's inequality. -/
lemma exists_gelfandRadius_rpow_inv_le {X : ℕ → Matrix ι ι ℝ} {lam : ℝ} (hlam : 1 ≤ lam)
    (hlim : Tendsto (fun n : ℕ => ‖X n‖ ^ (n : ℝ)⁻¹) atTop (𝓝 lam)) {L : ℕ → Matrix ι ι ℝ}
    {A : ℝ} (hA : 0 ≤ A) (hnorm : ∀ q, ‖L q‖ ≤ 1 + A * ∑ k ∈ Finset.range q, ‖X k‖) :
    ∃ B, ∀ q : ℕ, gelfandRadius (L q) ^ (q : ℝ)⁻¹ ≤ B := by
  set R := lam + 1 with hR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hlim.eventually (gt_mem_nhds (show lam < R by linarith))).and (eventually_ne_atTop 0))
  set C₀ := ∑ k ∈ Finset.range N, ‖X k‖ with hC₀
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hXk : ∀ k, ‖X k‖ ≤ C₀ + R ^ k := by
    intro k
    rcases lt_or_ge k N with hk | hk
    · have := Finset.single_le_sum (f := fun k => ‖X k‖) (fun i _ => norm_nonneg _)
        (Finset.mem_range.2 hk)
      linarith [pow_nonneg hR0.le k]
    · obtain ⟨h1, h2⟩ := hN k hk
      have := (Real.rpow_inv_le_iff_of_pos (norm_nonneg _) hR0.le
        (by exact_mod_cast Nat.pos_of_ne_zero h2)).1 h1.le
      rw [Real.rpow_natCast] at this
      linarith
  set c := A * (C₀ + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨max 1 ((1 + c) * R), fun q => ?_⟩
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp
  have hRq : 1 ≤ R ^ q := one_le_pow₀ hR1
  have hsum : ∑ k ∈ Finset.range q, ‖X k‖ ≤ q * (C₀ + R ^ q) := by
    calc ∑ k ∈ Finset.range q, ‖X k‖ ≤ ∑ _k ∈ Finset.range q, (C₀ + R ^ q) :=
          Finset.sum_le_sum fun k hk => (hXk k).trans (by
            gcongr
            exact (Finset.mem_range.1 hk).le)
      _ = q * (C₀ + R ^ q) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hLq : ‖L q‖ ≤ ((1 + c) * R) ^ q := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hbern : 1 + q * c ≤ (1 + c) ^ q := one_add_mul_le_pow (by linarith) q
    calc ‖L q‖ ≤ 1 + A * (q * (C₀ + R ^ q)) := (hnorm q).trans (by gcongr)
      _ ≤ (1 + q * c) * R ^ q := by
          rw [hc]
          have : A * q * C₀ ≤ A * q * C₀ * R ^ q := le_mul_of_one_le_right (by positivity) hRq
          nlinarith
      _ ≤ (1 + c) ^ q * R ^ q := by gcongr
      _ = ((1 + c) * R) ^ q := (mul_pow _ _ _).symm
  calc gelfandRadius (L q) ^ (q : ℝ)⁻¹ ≤ (((1 + c) * R) ^ q) ^ (q : ℝ)⁻¹ :=
        Real.rpow_le_rpow (gelfandRadius_nonneg _) ((gelfandRadius_le_norm _).trans hLq)
          (by positivity)
    _ = (1 + c) * R := Real.pow_rpow_inv_natCast (by positivity) hq.ne'
    _ ≤ max 1 ((1 + c) * R) := le_max_right _ _

/-- **The variational formula, convergence.** If `‖X n‖^{1/n} → λ ≥ 1`, every period `q ≥ 1` has
a leaf matrix `L q ≥ 0` with `X (n + q) ≤ X n (L q)`, and `‖L q‖ ≤ 1 + A ∑_{k<q} ‖X k‖`, then
`gelfandRadius(L q)^{1/q} → λ`, and every period gives an upper bound
`λ ≤ gelfandRadius(L q)^{1/q}`. -/
theorem tendsto_gelfandRadius_rpow_inv_of_le_mul {X : ℕ → Matrix ι ι ℝ}
    (hX : ∀ n i j, 0 ≤ X n i j) {lam : ℝ} (hlam : 1 ≤ lam)
    (hlim : Tendsto (fun n : ℕ => ‖X n‖ ^ (n : ℝ)⁻¹) atTop (𝓝 lam)) {L : ℕ → Matrix ι ι ℝ}
    (hL : ∀ q i j, 0 ≤ L q i j) (hdom : ∀ q, q ≠ 0 → ∀ n i j, X (n + q) i j ≤ (X n * L q) i j)
    {A : ℝ} (hA : 0 ≤ A) (hnorm : ∀ q, ‖L q‖ ≤ 1 + A * ∑ k ∈ Finset.range q, ‖X k‖) :
    (∀ q, q ≠ 0 → lam ≤ gelfandRadius (L q) ^ (q : ℝ)⁻¹) ∧
      Tendsto (fun q : ℕ => gelfandRadius (L q) ^ (q : ℝ)⁻¹) atTop (𝓝 lam) := by
  have hlow : ∀ q, q ≠ 0 → lam ≤ gelfandRadius (L q) ^ (q : ℝ)⁻¹ := fun q hq => by
    have h := limsup_rpow_inv_le_of_le_mul hX (hL q) hq (hdom q hq)
    rwa [hlim.limsup_eq] at h
  have hup := limsup_gelfandRadius_rpow_inv_le (b := fun n => ‖X n‖) (fun n => norm_nonneg _)
    hlam hlim hA hnorm
  obtain ⟨B, hB⟩ := exists_gelfandRadius_rpow_inv_le hlam hlim hA hnorm
  have hbdd : IsBoundedUnder (· ≤ ·) atTop fun q : ℕ => gelfandRadius (L q) ^ (q : ℝ)⁻¹ :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hB)
  refine ⟨hlow, tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩⟩
  · filter_upwards [eventually_ne_atTop 0] with q hq
    exact ha.trans_le (hlow q hq)
  · exact eventually_lt_of_limsup_lt (hup.trans_lt hb) hbdd

/-- **The variational formula, infimum.** Under the hypotheses of
`Matrix.tendsto_gelfandRadius_rpow_inv_of_le_mul`, the rate is the infimum of the period
certificates: `⨅_{q ≥ 1} gelfandRadius(L q)^{1/q} = λ`. -/
theorem iInf_gelfandRadius_rpow_inv_eq {X : ℕ → Matrix ι ι ℝ} (hX : ∀ n i j, 0 ≤ X n i j)
    {lam : ℝ} (hlam : 1 ≤ lam) (hlim : Tendsto (fun n : ℕ => ‖X n‖ ^ (n : ℝ)⁻¹) atTop (𝓝 lam))
    {L : ℕ → Matrix ι ι ℝ} (hL : ∀ q i j, 0 ≤ L q i j)
    (hdom : ∀ q, q ≠ 0 → ∀ n i j, X (n + q) i j ≤ (X n * L q) i j) {A : ℝ} (hA : 0 ≤ A)
    (hnorm : ∀ q, ‖L q‖ ≤ 1 + A * ∑ k ∈ Finset.range q, ‖X k‖) :
    ⨅ q : ℕ+, gelfandRadius (L q) ^ ((q : ℕ) : ℝ)⁻¹ = lam := by
  obtain ⟨hlow, htend⟩ :=
    tendsto_gelfandRadius_rpow_inv_of_le_mul hX hlam hlim hL hdom hA hnorm
  have hbdd : BddBelow (Set.range fun q : ℕ+ => gelfandRadius (L q) ^ ((q : ℕ) : ℝ)⁻¹) :=
    ⟨lam, by
      rintro _ ⟨q, rfl⟩
      exact hlow q q.ne_zero⟩
  refine le_antisymm ?_ (le_ciInf fun q => hlow q q.ne_zero)
  refine ge_of_tendsto htend ?_
  filter_upwards [eventually_ne_atTop 0] with q hq
  exact ciInf_le hbdd ⟨q, Nat.pos_of_ne_zero hq⟩

end Matrix
