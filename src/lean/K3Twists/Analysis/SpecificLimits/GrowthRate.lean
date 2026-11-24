/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
  have h2 : Tendsto (fun N : ℕ => ((N / ℓ : ℕ) : ℝ) / N) atTop (𝓝 (1 / ℓ)) := by
    have hb : ∀ N : ℕ, 0 < N → |((N / ℓ : ℕ) : ℝ) / N - 1 / ℓ| ≤ 1 / N := by
      intro N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hdm := Nat.div_add_mod N ℓ
      have hmod : N % ℓ < ℓ := Nat.mod_lt N hℓ
      have hdm' : (ℓ : ℝ) * ((N / ℓ : ℕ) : ℝ) + ((N % ℓ : ℕ) : ℝ) = N := by exact_mod_cast hdm
      have hmod' : ((N % ℓ : ℕ) : ℝ) < ℓ := by exact_mod_cast hmod
      have hmod0 : (0 : ℝ) ≤ ((N % ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
      have heq : ((N / ℓ : ℕ) : ℝ) / N - 1 / ℓ = -(((N % ℓ : ℕ) : ℝ) / (N * ℓ)) := by
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

end Real
