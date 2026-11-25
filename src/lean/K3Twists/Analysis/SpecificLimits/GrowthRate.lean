/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Exponential growth rates

The analytic part of the point-mass corollary: a sequence `H_n ≥ 0` with
`H_{m+n} ≤ K H_m H_n` has an exponential rate `ρ = lim H_n^{1/n}`, every finite block certifies
the upper bound `ρ ≤ (K H_k)^{1/k}`, and these bounds converge to `ρ` (Fekete's lemma, in
Mathlib as `Submultiplicative.tendsto_lim`). A second sequence squeezed between two constant
multiples of `H` has the same rate, uniformly in any parameter on which the constants do not
depend. We also record the transfer of rates under `o(n)` errors in the logarithm, the rate one
of polynomially bounded sequences, and the rate per letter of a periodic word.

## Fekete's lemma with a gap, padding, and a witness

* `tendsto_div_of_superadd_gap`: if `ℓ(m) + ℓ(n) ≤ ℓ(m + n + D)` and the certificates
  `ℓ(q)/(q + D)`, `q ≥ 1`, are bounded above, `ℓ(N)/N` converges to their supremum. No
  monotonicity is needed. `le_of_superadd_gap` and `le_div_of_block` are the lower and upper
  certificates, and `fekete_sandwich` packages both for a positive sequence `P` with
  `c P_m · c P_n ≤ c P_{m+n+D}` and `P_{n+q} ≤ K(q) P_n`:
  `log(c P_q)/(q + D) ≤ η ≤ log K(q)/q`.
* `tendsto_log_div_of_runningMax`: a one-sided step bound `x_n ≤ L x_{n+1}`, `x ≥ c > 0`, gives
  `x` the rate of its running maximum; `tendsto_log_exact_of_coupled` adds two comparisons with a
  distortion sequence `A`, `x_n ≤ K A_n` and `A_n ≤ K (n + 1) B_n`, and is the analytic core of
  the exact-length theorem for maxima over words of length exactly `n`.
* `sqrtWitness m n = m^n 2^{⌈√n⌉}` is submultiplicative with rate `m`, its doubling loss
  `H_k²/H_{2k}` is at least `2^{(2 - √2)√k - 1}`, and it has no polynomial envelope
  `H_n ≤ B (1 + n)^s m^n`: submultiplicativity does not control a sequence up to a polynomial.

Throughout, `x ^ (n : ℝ)⁻¹` is the `n`-th root; at `n = 0` it is `x⁰ = 1`, which is harmless for
limits.
-/

namespace Real

open Filter Topology Real

/-- `n`-th roots through logarithms: `H^{1/n} = exp(log H / n)` for `H > 0`. -/
lemma rpow_inv_eq_exp_log_div {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ (n : ℝ)⁻¹ = exp (log x / n) := by
  rw [rpow_def_of_pos hx, div_eq_mul_inv]

/-- If `log H_n / n → L` then `H_n^{1/n} → exp L`. -/
theorem tendsto_rpow_inv_of_log_div {H : ℕ → ℝ} (hpos : ∀ n, 0 < H n) {L : ℝ}
    (h : Tendsto (fun n : ℕ => log (H n) / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => H n ^ (n : ℝ)⁻¹) atTop (𝓝 (exp L)) := by
  have := (continuous_exp.tendsto L).comp h
  refine this.congr (fun n => ?_)
  simp [Function.comp, rpow_inv_eq_exp_log_div (hpos n)]

/-- If `H_n^{1/n} → ρ > 0` then `log H_n / n → log ρ`. -/
theorem tendsto_log_div_of_rpow_inv {H : ℕ → ℝ} (hpos : ∀ n, 0 < H n) {ρ : ℝ} (hρ : 0 < ρ)
    (h : Tendsto (fun n : ℕ => H n ^ (n : ℝ)⁻¹) atTop (𝓝 ρ)) :
    Tendsto (fun n : ℕ => log (H n) / n) atTop (𝓝 (log ρ)) := by
  have := ((continuousAt_log hρ.ne').tendsto).comp h
  refine this.congr (fun n => ?_)
  simp only [Function.comp, rpow_inv_eq_exp_log_div (hpos n), log_exp]

/-- Constants have `n`-th roots tending to one. -/
lemma tendsto_const_rpow_inv {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  exact ((continuous_const_rpow hc.ne').tendsto' 0 1 (rpow_zero c)).comp h0

/-- **Fekete's lemma with a constant.** If `H ≥ 0` and `H_{m+n} ≤ K H_m H_n` with `K > 0`, then
`H_n^{1/n}` converges to some `ρ`; every block `k ≥ 1` certifies `ρ ≤ (K H_k)^{1/k}`, and these
certified upper bounds converge to `ρ`. -/
theorem exists_rate_of_submul {H : ℕ → ℝ} {K : ℝ} (hK : 0 < K) (hH : ∀ n, 0 ≤ H n)
    (hsub : ∀ m n, H (m + n) ≤ K * H m * H n) :
    ∃ ρ : ℝ, Tendsto (fun n : ℕ => H n ^ (n : ℝ)⁻¹) atTop (𝓝 ρ) ∧
      (∀ k : ℕ, k ≠ 0 → ρ ≤ (K * H k) ^ (k : ℝ)⁻¹) ∧
      Tendsto (fun k : ℕ => (K * H k) ^ (k : ℝ)⁻¹) atTop (𝓝 ρ) := by
  set u : ℕ → ℝ := fun n => K * H n with hu_def
  have hu : Submultiplicative u := fun m n => by
    simp only [hu_def]
    calc K * H (m + n) ≤ K * (K * H m * H n) := mul_le_mul_of_nonneg_left (hsub m n) hK.le
      _ = K * H m * (K * H n) := by ring
  have hu0 : ∀ n, 0 ≤ u n := fun n => mul_nonneg hK.le (hH n)
  refine ⟨hu.lim, ?_, fun k hk => hu.lim_le_rpow hu0 hk, hu.tendsto_lim hu0⟩
  have h := (hu.tendsto_lim hu0).div (tendsto_const_rpow_inv hK) one_ne_zero
  rw [div_one] at h
  refine h.congr (fun n => ?_)
  simp only [hu_def, Pi.div_apply]
  rw [mul_rpow hK.le (hH n)]
  have : K ^ (n : ℝ)⁻¹ ≠ 0 := (rpow_pos_of_pos hK _).ne'
  field_simp

/-- A submultiplicative-up-to-`K` sequence is at least `ρⁿ / K`, where `ρ` is its rate. -/
lemma pow_rate_le {H : ℕ → ℝ} {K ρ : ℝ} (hK : 0 < K) (hH : ∀ n, 0 ≤ H n)
    (hρ : ∀ k : ℕ, k ≠ 0 → ρ ≤ (K * H k) ^ (k : ℝ)⁻¹) (hρ0 : 0 ≤ ρ) {n : ℕ} (hn : n ≠ 0) :
    ρ ^ n ≤ K * H n := by
  have h := pow_le_pow_left₀ hρ0 (hρ n hn) n
  rwa [← rpow_natCast ((K * H n) ^ (n : ℝ)⁻¹), ← rpow_mul (mul_nonneg hK.le (hH n)),
    inv_mul_cancel₀ (by exact_mod_cast hn), rpow_one] at h

/-- **Transfer of rates.** If `c H_n ≤ m_n ≤ C H_n` eventually, with `c, C > 0`, then `m` and
`H` have the same exponential rate. -/
theorem tendsto_rpow_inv_of_bounds {m H : ℕ → ℝ} {c C L : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hH : ∀ n, 0 ≤ H n) (hlow : ∀ᶠ n in atTop, c * H n ≤ m n)
    (hup : ∀ᶠ n in atTop, m n ≤ C * H n)
    (hlim : Tendsto (fun n : ℕ => H n ^ (n : ℝ)⁻¹) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => m n ^ (n : ℝ)⁻¹) atTop (𝓝 L) := by
  have hl : Tendsto (fun n : ℕ => (c * H n) ^ (n : ℝ)⁻¹) atTop (𝓝 L) := by
    have := (tendsto_const_rpow_inv hc).mul hlim
    rw [one_mul] at this
    exact this.congr (fun n => (mul_rpow hc.le (hH n)).symm)
  have hu : Tendsto (fun n : ℕ => (C * H n) ^ (n : ℝ)⁻¹) atTop (𝓝 L) := by
    have := (tendsto_const_rpow_inv hC).mul hlim
    rw [one_mul] at this
    exact this.congr (fun n => (mul_rpow hC.le (hH n)).symm)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
  · filter_upwards [hlow] with n hn
    exact rpow_le_rpow (mul_nonneg hc.le (hH n)) hn (by positivity)
  · filter_upwards [hlow, hup] with n hn hn'
    exact rpow_le_rpow ((mul_nonneg hc.le (hH n)).trans hn) hn' (by positivity)

/-- **Uniform transfer of rates.** If a family `m_i` satisfies `c H_n ≤ m_i(n) ≤ C H_n` with
constants independent of `i`, the `n`-th roots of `m_i(n)` converge to the rate of `H` uniformly
in `i`. -/
theorem tendstoUniformly_rpow_inv_of_bounds {ι : Type*} {m : ι → ℕ → ℝ} {H : ℕ → ℝ}
    {c C L : ℝ} (hc : 0 < c) (hC : 0 < C) (hH : ∀ n, 0 ≤ H n)
    (hlow : ∀ i n, c * H n ≤ m i n) (hup : ∀ i n, m i n ≤ C * H n)
    (hlim : Tendsto (fun n : ℕ => H n ^ (n : ℝ)⁻¹) atTop (𝓝 L)) :
    TendstoUniformly (fun n i => m i n ^ (n : ℝ)⁻¹) (fun _ => L) atTop := by
  have hl : Tendsto (fun n : ℕ => (c * H n) ^ (n : ℝ)⁻¹) atTop (𝓝 L) := by
    have := (tendsto_const_rpow_inv hc).mul hlim
    rw [one_mul] at this
    exact this.congr (fun n => (mul_rpow hc.le (hH n)).symm)
  have hu : Tendsto (fun n : ℕ => (C * H n) ^ (n : ℝ)⁻¹) atTop (𝓝 L) := by
    have := (tendsto_const_rpow_inv hC).mul hlim
    rw [one_mul] at this
    exact this.congr (fun n => (mul_rpow hC.le (hH n)).symm)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have h1 := (Metric.tendsto_nhds.mp hl) ε hε
  have h2 := (Metric.tendsto_nhds.mp hu) ε hε
  filter_upwards [h1, h2] with n hn1 hn2 i
  rw [Real.dist_eq] at hn1 hn2 ⊢
  have lo : (c * H n) ^ (n : ℝ)⁻¹ ≤ m i n ^ (n : ℝ)⁻¹ :=
    rpow_le_rpow (mul_nonneg hc.le (hH n)) (hlow i n) (by positivity)
  have hi : m i n ^ (n : ℝ)⁻¹ ≤ (C * H n) ^ (n : ℝ)⁻¹ :=
    rpow_le_rpow ((mul_nonneg hc.le (hH n)).trans (hlow i n)) (hup i n) (by positivity)
  rw [abs_lt] at hn1 hn2 ⊢
  constructor <;> linarith [hn1.1, hn1.2, hn2.1, hn2.2]

/-- **Rates under `o(n)` errors.** If `|log m_n - log p_n| ≤ e_n` and `e_n / n → 0`, the
normalized logarithms of `m` and `p` have the same asymptotics. -/
theorem tendsto_log_div_sub_of_bound {m p e : ℕ → ℝ}
    (hbound : ∀ n, |log (m n) - log (p n)| ≤ e n)
    (he : Tendsto (fun n : ℕ => e n / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => log (m n) / n - log (p n) / n) atTop (𝓝 0) := by
  have hle : ∀ n : ℕ, |log (m n) / n - log (p n) / n| ≤ e n / n := by
    intro n
    rw [← sub_div, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (hbound n) (Nat.cast_nonneg n)
  have hneg : Tendsto (fun n : ℕ => -(e n / n)) atTop (𝓝 0) := by simpa using he.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hneg he (fun n => ?_) (fun n => ?_)
  · exact neg_le_of_abs_le (hle n)
  · exact le_of_abs_le (hle n)

/-- If `p` has normalized logarithm `→ ℓ` and `m` differs from `p` by `o(n)` in the logarithm,
then `m` has the same limit. -/
theorem tendsto_log_div_of_bound {m p e : ℕ → ℝ}
    (hbound : ∀ n, |log (m n) - log (p n)| ≤ e n)
    (he : Tendsto (fun n : ℕ => e n / n) atTop (𝓝 0)) {ℓ : ℝ}
    (hp : Tendsto (fun n : ℕ => log (p n) / n) atTop (𝓝 ℓ)) :
    Tendsto (fun n : ℕ => log (m n) / n) atTop (𝓝 ℓ) := by
  have := (tendsto_log_div_sub_of_bound hbound he).add hp
  rw [zero_add] at this
  exact this.congr (fun n => by ring)

/-- **Polynomial growth has rate one.** If `1 ≤ H_n ≤ A + B n²`, then `log H_n / n → 0`. -/
theorem tendsto_log_div_zero_of_poly {H : ℕ → ℝ} {A B : ℝ} (h1 : ∀ n, 1 ≤ H n)
    (hpoly : ∀ n, H n ≤ A + B * n ^ 2) :
    Tendsto (fun n : ℕ => log (H n) / n) atTop (𝓝 0) := by
  set C : ℝ := |A| + |B| + 1 with hC
  have hCpos : 0 < C := by positivity
  -- for `n ≥ 1`: `H n ≤ C n²`, so `0 ≤ log H n / n ≤ (log C + 2 log n) / n`
  have hlogn : Tendsto (fun n : ℕ => log (n : ℝ) / n) atTop (𝓝 0) := by
    have := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine this.congr (fun n => ?_)
    simp
  have hconst : Tendsto (fun n : ℕ => log C / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ => log C / n + 2 * (log (n : ℝ) / n)) atTop (𝓝 0) := by
    simpa using hconst.add (hlogn.const_mul 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards with n
    exact div_nonneg (log_nonneg (h1 n)) (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hHC : H n ≤ C * (n : ℝ) ^ 2 := by
      have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      calc H n ≤ A + B * n ^ 2 := hpoly n
        _ ≤ |A| + |B| * n ^ 2 := by
            gcongr
            · exact le_abs_self A
            · exact le_abs_self B
        _ ≤ C * (n : ℝ) ^ 2 := by
            rw [hC]; nlinarith [abs_nonneg A, abs_nonneg B]
    have hlog : log (H n) ≤ log C + 2 * log n := by
      have hpos : 0 < H n := lt_of_lt_of_le one_pos (h1 n)
      calc log (H n) ≤ log (C * (n : ℝ) ^ 2) := log_le_log hpos hHC
        _ = log C + 2 * log n := by
            rw [log_mul hCpos.ne' (by positivity), log_pow]; push_cast; ring
    have hnpos : (0 : ℝ) < n := by linarith
    calc log (H n) / n ≤ (log C + 2 * log n) / n := div_le_div_of_nonneg_right hlog hnpos.le
      _ = log C / n + 2 * (log n / n) := by ring

/-- `⌊N/p⌋ / N → 1/p`. -/
theorem tendsto_natDiv_div {p : ℕ} (hp : 0 < p) :
    Tendsto (fun N : ℕ => ((N / p : ℕ) : ℝ) / N) atTop (𝓝 (1 / p)) := by
  have hb : ∀ N : ℕ, 0 < N → |((N / p : ℕ) : ℝ) / N - 1 / p| ≤ 1 / N := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hdm := Nat.div_add_mod N p
    have hmod : N % p < p := Nat.mod_lt N hp
    have hdm' : (p : ℝ) * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) = N := by exact_mod_cast hdm
    have hmod' : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast hmod
    have hmod0 : (0 : ℝ) ≤ ((N % p : ℕ) : ℝ) := Nat.cast_nonneg _
    have heq : ((N / p : ℕ) : ℝ) / N - 1 / p = -(((N % p : ℕ) : ℝ) / (N * p)) := by
      field_simp
      linear_combination hdm'
    rw [heq, abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hN']
    nlinarith
  have h0 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ h0
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [Real.norm_eq_abs]
  exact hb N hN

/-- **The rate per letter.** Let `a_N` be the logarithm of a quantity measured after the first
`N` letters of a periodic word with period `ℓ ≥ 1`. If after `k` whole periods `a_{ℓk}/k → L`,
and an incomplete period changes `a` by at most `D`, then `a_N / N → L / ℓ`. -/
theorem tendsto_log_div_of_period {a : ℕ → ℝ} {ℓ : ℕ} (hℓ : 0 < ℓ) {L D : ℝ}
    (hper : Tendsto (fun k : ℕ => a (ℓ * k) / k) atTop (𝓝 L))
    (hclose : ∀ N, |a N - a (ℓ * (N / ℓ))| ≤ D) :
    Tendsto (fun N : ℕ => a N / N) atTop (𝓝 (L / ℓ)) := by
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  -- `N / ℓ → ∞`
  have hk : Tendsto (fun N : ℕ => N / ℓ) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨ℓ * b, fun N hN => (Nat.le_div_iff_mul_le hℓ).mpr (by linarith [mul_comm ℓ b])⟩
  have h1 : Tendsto (fun N : ℕ => a (ℓ * (N / ℓ)) / ((N / ℓ : ℕ) : ℝ)) atTop (𝓝 L) :=
    hper.comp hk
  -- `(N / ℓ) / N → 1 / ℓ`
  have h2 := tendsto_natDiv_div hℓ
  -- the error of an incomplete period is `O(1/N)`
  have h3 : Tendsto (fun N : ℕ => (a N - a (ℓ * (N / ℓ))) / N) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => D / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ h0
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hN']
    exact div_le_div_of_nonneg_right (hclose N) hN'.le
  have := (h1.mul h2).add h3
  rw [show L * (1 / (ℓ : ℝ)) + 0 = L / ℓ by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop ℓ] with N hN
  have hkpos : 0 < N / ℓ := Nat.div_pos hN hℓ
  have hk' : (0 : ℝ) < ((N / ℓ : ℕ) : ℝ) := by exact_mod_cast hkpos
  have hN' : (0 : ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le hℓ hN
    exact_mod_cast this
  field_simp
  ring

/-! ### Fekete's lemma with a gap -/

/-- Iterating the gap inequality: `k ℓ(q) + ℓ(r) ≤ ℓ(k(q + D) + r)`. -/
lemma iter_superadd_gap {ℓ : ℕ → ℝ} {D : ℕ} (hsup : ∀ m n, ℓ m + ℓ n ≤ ℓ (m + n + D))
    (q k r : ℕ) : (k : ℝ) * ℓ q + ℓ r ≤ ℓ (k * (q + D) + r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hsup q (k * (q + D) + r)
    have he : q + (k * (q + D) + r) + D = (k + 1) * (q + D) + r := by ring
    rw [he] at h
    push_cast
    linarith

/-- Each certificate of a gap-superadditive sequence holds eventually: if `a < ℓ(q)/(q + D)`
then `a < ℓ(N)/N` for large `N`. No monotonicity is needed, because the remainders
`r < q + D` are finitely many. -/
lemma eventually_lt_of_superadd_gap {ℓ : ℕ → ℝ} {D : ℕ}
    (hsup : ∀ m n, ℓ m + ℓ n ≤ ℓ (m + n + D)) {q : ℕ} (hp : 0 < q + D)
    {a : ℝ} (ha : a < ℓ q / ((q : ℝ) + D)) : ∀ᶠ N : ℕ in atTop, a < ℓ N / N := by
  set mn := (Finset.range (q + D)).inf' (Finset.nonempty_range_iff.2 hp.ne') ℓ
  have hmn : ∀ r < q + D, mn ≤ ℓ r := fun r hr => Finset.inf'_le _ (Finset.mem_range.2 hr)
  have hk := tendsto_natDiv_div hp
  have hlim : Tendsto (fun N : ℕ => ((N / (q + D) : ℕ) : ℝ) / N * ℓ q + mn / N) atTop
      (𝓝 (1 / ((q + D : ℕ) : ℝ) * ℓ q + 0)) :=
    (hk.mul_const _).add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  have hval : 1 / ((q + D : ℕ) : ℝ) * ℓ q + 0 = ℓ q / ((q : ℝ) + D) := by
    push_cast; ring
  rw [hval] at hlim
  filter_upwards [hlim.eventually (lt_mem_nhds ha), eventually_gt_atTop 0] with N hN hNpos
  have h1 := iter_superadd_gap hsup q (N / (q + D)) (N % (q + D))
  rw [Nat.div_add_mod' N (q + D)] at h1
  have h3 := hmn (N % (q + D)) (Nat.mod_lt N hp)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have : ((N / (q + D) : ℕ) : ℝ) / N * ℓ q + mn / N ≤ ℓ N / N := by
    rw [div_mul_eq_mul_div, ← add_div, div_le_div_iff_of_pos_right hN']
    linarith
  linarith

/-- **Fekete's lemma with a gap** (M. Fekete, Math. Z. 17 (1923), for `D = 0`). If
`ℓ(m) + ℓ(n) ≤ ℓ(m + n + D)` and the certificates `ℓ(q)/(q + D)`, `q ≥ 1`, are bounded above,
then `ℓ(N)/N` converges to their supremum. No monotonicity and no positivity are assumed.

The supremum runs over `q ≥ 1`: at `q = D = 0` the convention `x / 0 = 0` would insert a false
certificate `0` (for `ℓ(n) = -n` the limit is `-1`). -/
theorem tendsto_div_of_superadd_gap {ℓ : ℕ → ℝ} {D : ℕ}
    (hsup : ∀ m n, ℓ m + ℓ n ≤ ℓ (m + n + D))
    (hbdd : BddAbove (Set.range fun q : ℕ => ℓ (q + 1) / ((q : ℝ) + 1 + D))) :
    Tendsto (fun N : ℕ => ℓ N / N) atTop (𝓝 (⨆ q : ℕ, ℓ (q + 1) / ((q : ℝ) + 1 + D))) := by
  set L := ⨆ q : ℕ, ℓ (q + 1) / ((q : ℝ) + 1 + D) with hL
  have hcert : ∀ N : ℕ, 0 < N → ℓ N ≤ L * (N + D) := by
    intro N hN
    obtain ⟨q, rfl⟩ : ∃ q, N = q + 1 := ⟨N - 1, by omega⟩
    have h1 : ℓ (q + 1) / ((q : ℝ) + 1 + D) ≤ L := le_ciSup hbdd q
    have hpos : (0 : ℝ) < (q : ℝ) + 1 + D := by positivity
    rw [div_le_iff₀ hpos] at h1
    push_cast
    linarith
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨q, hq⟩ := exists_lt_of_lt_ciSup ha
    refine eventually_lt_of_superadd_gap hsup (q := q + 1) (by omega) ?_
    push_cast
    exact hq
  · have h0 : Tendsto (fun N : ℕ => L + L * D / (N : ℝ)) atTop (𝓝 (L + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [add_zero] at h0
    filter_upwards [h0.eventually (gt_mem_nhds hb), eventually_gt_atTop 0] with N hN hNpos
    have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
    have : ℓ N / N ≤ L + L * D / N := by
      have hc := hcert N hNpos
      rw [div_le_iff₀ hN', add_mul, div_mul_cancel₀ _ hN'.ne']
      linarith
    linarith

/-- **Lower certificates.** Every `q` with `q + D > 0` gives `ℓ(q)/(q + D) ≤ lim ℓ(N)/N`. -/
theorem le_of_superadd_gap {ℓ : ℕ → ℝ} {D : ℕ} {L : ℝ}
    (hsup : ∀ m n, ℓ m + ℓ n ≤ ℓ (m + n + D))
    (hlim : Tendsto (fun N : ℕ => ℓ N / N) atTop (𝓝 L)) {q : ℕ} (hp : 0 < q + D) :
    ℓ q / ((q : ℝ) + D) ≤ L := by
  by_contra h
  push Not at h
  have h1 := eventually_lt_of_superadd_gap hsup hp (a := (L + ℓ q / ((q : ℝ) + D)) / 2)
    (by linarith)
  have h2 := hlim.eventually (gt_mem_nhds (show L < (L + ℓ q / ((q : ℝ) + D)) / 2 by linarith))
  obtain ⟨N, hN1, hN2⟩ := (h1.and h2).exists
  linarith

/-- **Upper (block) certificates.** If `ℓ(N)/N → L` and a block of `q ≥ 1` steps adds at most
`K`, that is `ℓ(n + q) ≤ ℓ(n) + K`, then `L ≤ K/q`. -/
theorem le_div_of_block {ℓ : ℕ → ℝ} {L K : ℝ} {q : ℕ} (hq : 0 < q)
    (hlim : Tendsto (fun N : ℕ => ℓ N / N) atTop (𝓝 L))
    (hblock : ∀ n, ℓ (n + q) ≤ ℓ n + K) : L ≤ K / q := by
  have hiter : ∀ k : ℕ, ℓ (k * q) ≤ ℓ 0 + k * K := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hblock (k * q)
      rw [show (k + 1) * q = k * q + q by ring]
      push_cast
      linarith
  have hkq : Tendsto (fun k : ℕ => k * q) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun k hk => le_trans hk (Nat.le_mul_of_pos_right k hq)⟩
  have hsub : Tendsto (fun k : ℕ => ℓ (k * q) / ((k * q : ℕ) : ℝ)) atTop (𝓝 L) :=
    hlim.comp hkq
  have hR : Tendsto (fun k : ℕ => ℓ 0 / ((k * q : ℕ) : ℝ) + K / q) atTop (𝓝 (0 + K / q)) :=
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hkq)).add tendsto_const_nhds
  rw [zero_add] at hR
  refine le_of_tendsto_of_tendsto hsub hR ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpos : (0 : ℝ) < ((k * q : ℕ) : ℝ) := by push_cast; positivity
  calc ℓ (k * q) / ((k * q : ℕ) : ℝ) ≤ (ℓ 0 + k * K) / ((k * q : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (hiter k) hpos.le
    _ = ℓ 0 / ((k * q : ℕ) : ℝ) + K / q := by
        push_cast
        field_simp

/-- **The Fekete sandwich.** A positive sequence `P` that is supermultiplicative up to a gap `D`
and a constant `c > 0`, `c P_m · c P_n ≤ c P_{m+n+D}`, and satisfies block bounds
`P_{n+q} ≤ K(q) P_n`, has an exponential rate `η = lim log P_N / N`, squeezed by the two
certificates `log(c P_q)/(q + D) ≤ η ≤ log K(q)/q`. No monotonicity is assumed; the bound
`BddAbove` that Fekete's lemma needs comes from the block bound with `q = 1`. -/
theorem fekete_sandwich {P : ℕ → ℝ} {c : ℝ} {D : ℕ} (hc : 0 < c) (hP : ∀ n, 0 < P n)
    (hsup : ∀ m n, c * P m * (c * P n) ≤ c * P (m + n + D))
    (K : ℕ → ℝ) (hblock : ∀ q n, P (n + q) ≤ K q * P n) :
    ∃ η : ℝ, Tendsto (fun N : ℕ => log (P N) / N) atTop (𝓝 η) ∧
      (∀ q : ℕ, 0 < q + D → log (c * P q) / ((q : ℝ) + D) ≤ η) ∧
      (∀ q : ℕ, 0 < q → η ≤ log (K q) / q) := by
  have hK : ∀ q, 0 < K q := fun q => by
    have h1 := hblock q 0
    have h2 := hP (0 + q)
    by_contra hneg
    push Not at hneg
    nlinarith [hP 0]
  set ℓ : ℕ → ℝ := fun n => log (c * P n) with hℓ
  have hcP : ∀ n, 0 < c * P n := fun n => mul_pos hc (hP n)
  have hsup' : ∀ m n, ℓ m + ℓ n ≤ ℓ (m + n + D) := fun m n => by
    simp only [hℓ]
    rw [← log_mul (hcP m).ne' (hcP n).ne']
    exact log_le_log (mul_pos (hcP m) (hcP n)) (hsup m n)
  have hblock' : ∀ q n, ℓ (n + q) ≤ ℓ n + log (K q) := fun q n => by
    simp only [hℓ]
    rw [← log_mul (hcP n).ne' (hK q).ne']
    refine log_le_log (hcP _) ?_
    have := hblock q n
    nlinarith
  have hlin : ∀ n : ℕ, ℓ n ≤ ℓ 0 + n * log (K 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hblock' 1 n
      push_cast
      linarith
  have hbdd : BddAbove (Set.range fun q : ℕ => ℓ (q + 1) / ((q : ℝ) + 1 + D)) := by
    refine ⟨|ℓ 0| + |log (K 1)|, ?_⟩
    rintro _ ⟨q, rfl⟩
    have hp' : (1 : ℝ) ≤ (q : ℝ) + 1 + D := by
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      have : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      linarith
    have hq' : ((q + 1 : ℕ) : ℝ) ≤ (q : ℝ) + 1 + D := by push_cast; simp
    simp only
    rw [div_le_iff₀ (by linarith)]
    have h1 := hlin (q + 1)
    have h2 : ℓ 0 ≤ |ℓ 0| * ((q : ℝ) + 1 + D) := by
      nlinarith [le_abs_self (ℓ 0), abs_nonneg (ℓ 0)]
    have h3 : ((q + 1 : ℕ) : ℝ) * log (K 1) ≤ |log (K 1)| * ((q : ℝ) + 1 + D) := by
      nlinarith [le_abs_self (log (K 1)), abs_nonneg (log (K 1)),
        Nat.cast_nonneg (α := ℝ) (q + 1)]
    nlinarith
  set η := ⨆ q : ℕ, ℓ (q + 1) / ((q : ℝ) + 1 + D)
  have hlim := tendsto_div_of_superadd_gap hsup' hbdd
  have hlimP : Tendsto (fun N : ℕ => log (P N) / N) atTop (𝓝 η) := by
    have h0 : Tendsto (fun N : ℕ => log c / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have := hlim.sub h0
    rw [sub_zero] at this
    refine this.congr fun N => ?_
    simp only [hℓ]
    rw [log_mul hc.ne' (hP N).ne']
    ring
  exact ⟨η, hlimP, fun q hq => le_of_superadd_gap hsup' hlim hq,
    fun q hq => le_div_of_block hq hlim (hblock' q)⟩

/-! ### Padding and exact lengths -/

/-- **Padding with a one-sided step bound.** Let `x_n ≥ c > 0` with `x_n ≤ L x_{n+1}` (a
sequence may drop by at most a factor `L` per step) and let `B` dominate `x` and be attained
earlier, `x_n ≤ B_n ≤ x_k` for some `k ≤ n` (a running maximum). If `log B_n / n → η` then
`log x_n / n → η`. A two-sided step bound is not needed, and `η ≥ 0` is a consequence. -/
theorem tendsto_log_div_of_runningMax {x B : ℕ → ℝ} {c L η : ℝ} (hc : 0 < c)
    (hx : ∀ n, c ≤ x n) (hL : 1 ≤ L) (hstep : ∀ n, x n ≤ L * x (n + 1))
    (hxB : ∀ n, x n ≤ B n) (hBatt : ∀ n, ∃ k ≤ n, B n ≤ x k)
    (hB : Tendsto (fun n : ℕ => log (B n) / n) atTop (𝓝 η)) :
    Tendsto (fun n : ℕ => log (x n) / n) atTop (𝓝 η) := by
  have hxpos : ∀ n, 0 < x n := fun n => lt_of_lt_of_le hc (hx n)
  have hBpos : ∀ n, 0 < B n := fun n => lt_of_lt_of_le (hxpos n) (hxB n)
  have hLpos : 0 < L := by linarith
  have hl : 0 ≤ log L := log_nonneg hL
  have hiter : ∀ k j : ℕ, log (x k) ≤ log (x (k + j)) + j * log L := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := hstep (k + j)
      have h2 : log (x (k + j)) ≤ log L + log (x (k + j + 1)) := by
        rw [← log_mul hLpos.ne' (hxpos _).ne']
        exact log_le_log (hxpos _) h1
      rw [← add_assoc]
      push_cast
      linarith
  have hc0 : Tendsto (fun n : ℕ => log c / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hη : 0 ≤ η := by
    refine le_of_tendsto_of_tendsto hc0 hB (Eventually.of_forall fun n => ?_)
    exact div_le_div_of_nonneg_right (log_le_log hc ((hx n).trans (hxB n))) (Nat.cast_nonneg _)
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a 0 with ha0 | ha0
    · filter_upwards [hc0.eventually (lt_mem_nhds ha0)] with n hn
      have : log c / n ≤ log (x n) / n :=
        div_le_div_of_nonneg_right (log_le_log hc (hx n)) (Nat.cast_nonneg _)
      linarith
    · have hηpos : 0 < η := lt_of_le_of_lt ha0 ha
      set ε := (η - a) / 4 with hε
      have hεpos : 0 < ε := by rw [hε]; linarith
      have hden : 0 < 1 + 2 * log L / η := by positivity
      set δ := ε / (1 + 2 * log L / η) with hδ
      have hδpos : 0 < δ := div_pos hεpos hden
      have hδε : δ + 2 * log L * δ / η = ε := by
        have : δ * (1 + 2 * log L / η) = ε := div_mul_cancel₀ _ hden.ne'
        calc δ + 2 * log L * δ / η = δ * (1 + 2 * log L / η) := by ring
          _ = ε := this
      have hup := hB.eventually (gt_mem_nhds (show η < η + δ by linarith))
      have hlo := hB.eventually (lt_mem_nhds (show η - δ < η by linarith))
      obtain ⟨K0, hK0⟩ := eventually_atTop.1 hup
      set C := ∑ k ∈ Finset.range (K0 + 1), |log (B k)| with hC
      have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hBk : ∀ k : ℕ, log (B k) ≤ C + (η + δ) * k := by
        intro k
        have hk0 : 0 ≤ (η + δ) * k := by positivity
        rcases le_or_gt k K0 with hk | hk
        · have : |log (B k)| ≤ C :=
            Finset.single_le_sum (f := fun k => |log (B k)|) (fun _ _ => abs_nonneg _)
              (Finset.mem_range.2 (by omega))
          have := le_abs_self (log (B k))
          linarith
        · have h1 := hK0 k hk.le
          have hk' : (0 : ℝ) < k := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hk)
          rw [div_lt_iff₀ hk'] at h1
          linarith
      have herr : Tendsto (fun n : ℕ => log L * C / η / n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      filter_upwards [hlo, herr.eventually (gt_mem_nhds hεpos), eventually_gt_atTop 0]
        with n hn1 hn2 hn3
      obtain ⟨k, hkn, hBk'⟩ := hBatt n
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn3
      have h1 : (η - δ) * n < log (B n) := by rwa [lt_div_iff₀ hn'] at hn1
      have h2 : log (B n) ≤ log (x k) := log_le_log (hBpos n) hBk'
      have h3 : log (x k) ≤ log (B k) := log_le_log (hxpos k) (hxB k)
      have h4 := hBk k
      have h5 := hiter k (n - k)
      rw [Nat.add_sub_cancel' hkn, Nat.cast_sub hkn] at h5
      have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
      have h6 : ((n : ℝ) - k) * η ≤ C + 2 * δ * n := by nlinarith
      have h7 : ((n : ℝ) - k) * log L ≤ log L * C / η / n * n + 2 * log L * δ / η * n := by
        have e : log L * C / η / n * n + 2 * log L * δ / η * n =
            log L * (C + 2 * δ * n) / η := by field_simp
        rw [e, le_div_iff₀ hηpos]
        nlinarith
      have h8 : log L * C / η / n * n ≤ ε * n := by
        exact mul_le_mul_of_nonneg_right hn2.le hn'.le
      have h9 : (δ + 2 * log L * δ / η) * n = ε * n := by rw [hδε]
      rw [lt_div_iff₀ hn']
      nlinarith
  · filter_upwards [hB.eventually (gt_mem_nhds hb)] with n hn
    have : log (x n) / n ≤ log (B n) / n :=
      div_le_div_of_nonneg_right (log_le_log (hxpos n) (hxB n)) (Nat.cast_nonneg _)
    linarith

/-- **Exact length from a coupled comparison.** Let `x_n ≥ c > 0` with `x_n ≤ L x_{n+1}`, let
`B` be a running maximum of `x` as in `tendsto_log_div_of_runningMax`, and let `A > 0` have
`log A_n / n → η`. If `x_n ≤ K A_n` and `A_n ≤ K (n + 1) B_n` then `log x_n / n → η`.

This is the analytic core of the exact-length theorem for maxima of masses over words of length
exactly `n`: `x_n` is that maximum, `B_n` the maximum over words of length at most `n`, and
`A_n` a distortion sequence; the two comparisons are the geometric inputs and are hypotheses
here. -/
theorem tendsto_log_exact_of_coupled {x B A : ℕ → ℝ} {c L K η : ℝ} (hc : 0 < c)
    (hx : ∀ n, c ≤ x n) (hL : 1 ≤ L) (hstep : ∀ n, x n ≤ L * x (n + 1))
    (hxB : ∀ n, x n ≤ B n) (hBatt : ∀ n, ∃ k ≤ n, B n ≤ x k)
    (hK : 0 < K) (hA : ∀ n, 0 < A n) (hxA : ∀ n, x n ≤ K * A n)
    (hAB : ∀ n, A n ≤ K * (n + 1) * B n)
    (hAlim : Tendsto (fun n : ℕ => log (A n) / n) atTop (𝓝 η)) :
    Tendsto (fun n : ℕ => log (x n) / n) atTop (𝓝 η) := by
  have hxpos : ∀ n, 0 < x n := fun n => lt_of_lt_of_le hc (hx n)
  have hBpos : ∀ n, 0 < B n := fun n => lt_of_lt_of_le (hxpos n) (hxB n)
  refine tendsto_log_div_of_runningMax hc hx hL hstep hxB hBatt ?_
  have hη : 0 ≤ η := by
    have h0 : Tendsto (fun n : ℕ => log (c / K) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine le_of_tendsto_of_tendsto h0 hAlim (Eventually.of_forall fun n => ?_)
    refine div_le_div_of_nonneg_right (log_le_log (by positivity) ?_) (Nat.cast_nonneg _)
    rw [div_le_iff₀ hK]
    linarith [hx n, hxA n]
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- `log B_n ≥ log A_n - log K - log (n + 1)`
    have hlogn : Tendsto (fun n : ℕ => log K / n + log ((n : ℝ) + 1) / n) atTop (𝓝 (0 + 0)) := by
      refine (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add ?_
      have h1 : Tendsto (fun n : ℕ => log ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
          (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
        refine this.congr fun n => ?_
        simp
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
        have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
        rw [add_zero] at this
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
      have := h1.mul h2
      rw [zero_mul] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rw [add_zero] at hlogn
    have hdiff := hAlim.sub hlogn
    rw [sub_zero] at hdiff
    filter_upwards [hdiff.eventually (lt_mem_nhds ha), eventually_gt_atTop 0] with n hn hnpos
    have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hle : log (A n) ≤ log K + log ((n : ℝ) + 1) + log (B n) := by
      rw [← log_mul hK.ne' (by positivity), ← log_mul (by positivity) (hBpos n).ne']
      exact log_le_log (hA n) (hAB n)
    have : log (A n) / n - (log K / n + log ((n : ℝ) + 1) / n) ≤ log (B n) / n := by
      rw [← add_div, ← sub_div]
      exact div_le_div_of_nonneg_right (by linarith) hn'.le
    linarith
  · set b' := (η + b) / 2
    have hb' : η < b' := by simp only [b']; linarith
    have hb'pos : 0 < b' := by linarith
    obtain ⟨K0, hK0⟩ := eventually_atTop.1 (hAlim.eventually (gt_mem_nhds hb'))
    set C := ∑ k ∈ Finset.range (K0 + 1), |log (A k)|
    have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hAk : ∀ k : ℕ, log (A k) ≤ C + b' * k := by
      intro k
      have hk0 : 0 ≤ b' * k := by positivity
      rcases le_or_gt k K0 with hk | hk
      · have : |log (A k)| ≤ C :=
          Finset.single_le_sum (f := fun k => |log (A k)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_range.2 (by omega))
        have := le_abs_self (log (A k))
        linarith
      · have h1 := hK0 k hk.le
        have hk' : (0 : ℝ) < k := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hk)
        rw [div_lt_iff₀ hk'] at h1
        linarith
    have herr : Tendsto (fun n : ℕ => b' + (log K + C) / n) atTop (𝓝 (b' + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [add_zero] at herr
    filter_upwards [herr.eventually (gt_mem_nhds (show b' < b by simp only [b']; linarith)),
      eventually_gt_atTop 0] with n hn hnpos
    have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
    obtain ⟨k, hkn, hBk⟩ := hBatt n
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have h1 : log (B n) ≤ log K + log (A k) := by
      rw [← log_mul hK.ne' (hA k).ne']
      exact log_le_log (hBpos n) (hBk.trans (hxA k))
    have h2 := hAk k
    have h3 : log (B n) / n ≤ b' + (log K + C) / n := by
      rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
      nlinarith
    linarith


/-! ### A submultiplicative sequence without a polynomial envelope -/

/-- `⌈√(a + b)⌉ ≤ ⌈√a⌉ + ⌈√b⌉`. -/
lemma ceil_sqrt_add_le (a b : ℕ) :
    ⌈√((a + b : ℕ) : ℝ)⌉₊ ≤ ⌈√(a : ℝ)⌉₊ + ⌈√(b : ℝ)⌉₊ := by
  rw [Nat.ceil_le]
  have ha := Nat.le_ceil √(a : ℝ)
  have hb := Nat.le_ceil √(b : ℝ)
  have hsum : √((a + b : ℕ) : ℝ) ≤ √(a : ℝ) + √(b : ℝ) := by
    rw [sqrt_le_left (by positivity)]
    have h1 := sq_sqrt (Nat.cast_nonneg (α := ℝ) a)
    have h2 := sq_sqrt (Nat.cast_nonneg (α := ℝ) b)
    push_cast
    nlinarith [sqrt_nonneg (a : ℝ), sqrt_nonneg (b : ℝ)]
  push_cast at hsum ⊢
  linarith

/-- The sequence `m^n 2^{⌈√n⌉}`. -/
noncomputable def sqrtWitness (m : ℝ) (n : ℕ) : ℝ := m ^ n * 2 ^ ⌈√(n : ℝ)⌉₊

lemma sqrtWitness_pos {m : ℝ} (hm : 0 < m) (n : ℕ) : 0 < sqrtWitness m n := by
  unfold sqrtWitness; positivity

/-- `m^n 2^{⌈√n⌉}` is submultiplicative for `m > 0`. -/
theorem sqrtWitness_add_le {m : ℝ} (hm : 0 < m) (a b : ℕ) :
    sqrtWitness m (a + b) ≤ sqrtWitness m a * sqrtWitness m b := by
  unfold sqrtWitness
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (ceil_sqrt_add_le a b)
  rw [pow_add] at h
  rw [pow_add]
  calc m ^ a * m ^ b * 2 ^ ⌈√((a + b : ℕ) : ℝ)⌉₊
      ≤ m ^ a * m ^ b * (2 ^ ⌈√(a : ℝ)⌉₊ * 2 ^ ⌈√(b : ℝ)⌉₊) := by gcongr
    _ = _ := by ring

/-- `m^n 2^{⌈√n⌉}` has exponential rate `m`. -/
theorem tendsto_sqrtWitness {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => sqrtWitness m n ^ (n : ℝ)⁻¹) atTop (𝓝 m) := by
  have hlog : Tendsto (fun n : ℕ => log (sqrtWitness m n) / n) atTop (𝓝 (log m)) := by
    -- `log H_n / n = log m + ⌈√n⌉ log 2 / n` for `n ≥ 1`, and `⌈√n⌉ / n ≤ 2 / √n`
    have hc : Tendsto (fun n : ℕ => (⌈√(n : ℝ)⌉₊ : ℝ) / n) atTop (𝓝 0) := by
      have hs : Tendsto (fun n : ℕ => 2 / √(n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hs
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hsq : 1 ≤ √(n : ℝ) := by rw [le_sqrt (by norm_num) (by positivity)]; simpa using hn'
      have hss : √(n : ℝ) * √(n : ℝ) = n := mul_self_sqrt (by positivity)
      have hceil : (⌈√(n : ℝ)⌉₊ : ℝ) ≤ 2 * √(n : ℝ) := by
        have := Nat.ceil_lt_add_one (sqrt_nonneg (n : ℝ))
        linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := (hc.mul_const (log 2)).const_add (log m)
    rw [zero_mul, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    unfold sqrtWitness
    rw [log_mul (by positivity) (by positivity), log_pow, log_pow]
    field_simp
  have h := tendsto_rpow_inv_of_log_div (sqrtWitness_pos hm) hlog
  rwa [exp_log hm] at h

/-- **The doubling loss of `m^n 2^{⌈√n⌉}`**: `H_k² ≥ 2^{(2 - √2)√k - 1} H_{2k}`. The loss
grows faster than any power of `k`, so no doubling inequality `H_{2k} ≥ H_k²/(C k^a)` holds. -/
theorem sqrtWitness_doubling {m : ℝ} (hm : 0 < m) (k : ℕ) :
    (2 : ℝ) ^ ((2 - √2) * √(k : ℝ) - 1) * sqrtWitness m (2 * k) ≤ sqrtWitness m k ^ 2 := by
  unfold sqrtWitness
  have h2k : √((2 * k : ℕ) : ℝ) = √2 * √(k : ℝ) := by push_cast; exact sqrt_mul (by norm_num) _
  have hexp : (2 - √2) * √(k : ℝ) - 1 + (⌈√((2 * k : ℕ) : ℝ)⌉₊ : ℝ) ≤
      ((2 * ⌈√(k : ℝ)⌉₊ : ℕ) : ℝ) := by
    have h1 := Nat.ceil_lt_add_one (sqrt_nonneg ((2 * k : ℕ) : ℝ))
    have h2 := Nat.le_ceil √(k : ℝ)
    rw [h2k] at h1 ⊢
    push_cast
    linarith
  have hrpow : (2 : ℝ) ^ ((2 - √2) * √(k : ℝ) - 1) * 2 ^ ⌈√((2 * k : ℕ) : ℝ)⌉₊ ≤
      2 ^ (2 * ⌈√(k : ℝ)⌉₊) := by
    rw [← rpow_natCast 2 ⌈√((2 * k : ℕ) : ℝ)⌉₊, ← rpow_add (by norm_num),
      ← rpow_natCast 2 (2 * ⌈√(k : ℝ)⌉₊)]
    exact rpow_le_rpow_of_exponent_le (by norm_num) hexp
  calc (2 : ℝ) ^ ((2 - √2) * √(k : ℝ) - 1) * (m ^ (2 * k) * 2 ^ ⌈√((2 * k : ℕ) : ℝ)⌉₊)
      = m ^ (2 * k) * ((2 : ℝ) ^ ((2 - √2) * √(k : ℝ) - 1) * 2 ^ ⌈√((2 * k : ℕ) : ℝ)⌉₊) := by
        ring
    _ ≤ m ^ (2 * k) * 2 ^ (2 * ⌈√(k : ℝ)⌉₊) := by gcongr
    _ = (m ^ k * 2 ^ ⌈√(k : ℝ)⌉₊) ^ 2 := by ring

/-- **No polynomial envelope.** `H_n = m^n 2^{⌈√n⌉}` is submultiplicative with rate `m`
(`sqrtWitness_add_le`, `tendsto_sqrtWitness`), yet no bound `H_n ≤ B (1 + n)^s m^n` holds. So
submultiplicativity alone does not give a polynomial envelope of a sequence around its rate. -/
theorem not_exists_poly_envelope_sqrtWitness {m : ℝ} (hm : 0 < m) :
    ¬ ∃ B s : ℝ, ∀ n : ℕ, sqrtWitness m n ≤ B * (1 + n) ^ s * m ^ n := by
  rintro ⟨B, s, h⟩
  -- at `n = k²` the bound reads `2^k ≤ B (1 + k²)^s ≤ B 2^N k^{2N}` with `N = ⌈|s|⌉`
  set N := ⌈|s|⌉₊
  have hkey : ∀ k : ℕ, 1 ≤ k → (2 : ℝ) ^ k ≤ B * 2 ^ N * (k : ℝ) ^ (2 * N) := by
    intro k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h1 := h (k ^ 2)
    unfold sqrtWitness at h1
    have hceil : ⌈√(((k ^ 2 : ℕ) : ℝ))⌉₊ = k := by
      push_cast
      rw [sqrt_sq (Nat.cast_nonneg k), Nat.ceil_natCast]
    rw [hceil] at h1
    have hmk : 0 < m ^ (k ^ 2) := by positivity
    have h2 : (2 : ℝ) ^ k ≤ B * (1 + ((k ^ 2 : ℕ) : ℝ)) ^ s := by
      have := (mul_le_mul_iff_of_pos_left hmk).1 (by linarith [h1] : m ^ (k ^ 2) * 2 ^ k ≤
        m ^ (k ^ 2) * (B * (1 + ((k ^ 2 : ℕ) : ℝ)) ^ s))
      exact this
    have hB : 0 ≤ B := by
      by_contra hB
      push Not at hB
      have : B * (1 + ((k ^ 2 : ℕ) : ℝ)) ^ s < 0 :=
        mul_neg_of_neg_of_pos hB (by positivity)
      linarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
    have hbase : (1 : ℝ) ≤ 1 + ((k ^ 2 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((k ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have h3 : (1 + ((k ^ 2 : ℕ) : ℝ)) ^ s ≤ (1 + ((k ^ 2 : ℕ) : ℝ)) ^ (N : ℝ) :=
      rpow_le_rpow_of_exponent_le hbase ((le_abs_self s).trans (Nat.le_ceil _))
    have h4 : (1 + ((k ^ 2 : ℕ) : ℝ)) ^ (N : ℝ) ≤ 2 ^ N * (k : ℝ) ^ (2 * N) := by
      rw [rpow_natCast, pow_mul, ← mul_pow]
      gcongr
      push_cast
      nlinarith
    calc (2 : ℝ) ^ k ≤ B * (1 + ((k ^ 2 : ℕ) : ℝ)) ^ s := h2
      _ ≤ B * (2 ^ N * (k : ℝ) ^ (2 * N)) := by gcongr; exact h3.trans h4
      _ = B * 2 ^ N * (k : ℝ) ^ (2 * N) := by ring
  -- but `k^{2N} / 2^k → 0`
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt (2 * N) (by norm_num : (1 : ℝ) < 2)
  have hC : 0 < B * 2 ^ N := by
    have := hkey 1 le_rfl
    simp only [Nat.cast_one, one_pow, mul_one, pow_one] at this
    linarith
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (B * 2 ^ N) by positivity))
  obtain ⟨k, hk, hk1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have h1 := hkey k hk1
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_lt_div_iff₀ h2k hC] at hk
  nlinarith

end Real
