/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Topical.Basic

/-!
# Collatz–Wielandt bounds for monotone homogeneous maps

For a monotone homogeneous map `f` of the orthant (`MonotoneHomogeneous`) one test vector
bounds the cycle time from either side, with no fixed-point theorem:

* a vector `x` with entries at least `m > 0` and `f x ≤ s x` gives `‖fⁿ 𝟙‖ ≤ (‖x‖/m) sⁿ`, so
  `R(f) ≤ s` (`norm_iterate_one_le_of_le_smul`, `cycleTime_le_of_le_smul`);
* a vector `0 ≤ v ≠ 0` with `t v ≤ f v` gives `t ≤ R(f)` (`le_cycleTime_of_smul_le`);
* a positive eigenvector, `f x = μ x`, gives `R(f) = μ` (`cycleTime_eq_of_eigenvector`).

These are the inequalities of Collatz (Math. Z. 48 (1942)) and Wielandt (Math. Z. 52 (1950)) in
the nonlinear setting of Gaubert and Gunawardena (Trans. Amer. Math. Soc. 356 (2004)).

The **ratio test** (`cycleTime_mem_Icc_of_ratio`, `cycleTime_mem_Icc_inf_sup`): for `v > 0`,
`min_i (f v)_i / v_i ≤ R(f) ≤ max_i (f v)_i / v_i`. Applied to `v, f v, f² v, …` it gives a
sequence of brackets, each certified by exact arithmetic.

For a nonnegative matrix `A` the map `x ↦ A x` has cycle time `gelfandRadius A`
(`cycleTime_mulVec`, through `Matrix.tendsto_rate_of_pos`), so the certificates
`Matrix.gelfandRadius_le_of_mulVec_le` and `Matrix.le_gelfandRadius_of_smul_le_mulVec` are the
linear case of the two bounds above.
-/

open Filter Topology

namespace MonotoneHomogeneous

variable {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ι → ℝ}

omit [Fintype ι] in
/-- `f x ≤ s x` iterates to `fⁿ x ≤ sⁿ x`. -/
lemma iterate_le_pow_smul (hf : MonotoneHomogeneous f) {x : ι → ℝ} (hx : 0 ≤ x) {s : ℝ}
    (hs : 0 ≤ s) (h : f x ≤ s • x) (n : ℕ) : f^[n] x ≤ s ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc f (f^[n] x) ≤ s ^ n • f x :=
          hf.le_smul_of_le ((hf.iterate n).map_nonneg hx) (pow_nonneg hs n) hx ih
      _ ≤ s ^ n • (s • x) := smul_le_smul_of_nonneg_left h (pow_nonneg hs n)
      _ = s ^ (n + 1) • x := by rw [smul_smul, pow_succ]

omit [Fintype ι] in
/-- `t v ≤ f v` iterates to `tⁿ v ≤ fⁿ v`. -/
lemma pow_smul_le_iterate (hf : MonotoneHomogeneous f) {v : ι → ℝ} (hv : 0 ≤ v) {t : ℝ}
    (ht : 0 ≤ t) (h : t • v ≤ f v) (n : ℕ) : t ^ n • v ≤ f^[n] v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc t ^ (n + 1) • v = t ^ n • (t • v) := by rw [smul_smul, pow_succ]
      _ ≤ t ^ n • f v := smul_le_smul_of_nonneg_left h (pow_nonneg ht n)
      _ ≤ f (f^[n] v) := hf.smul_le_of_le (pow_nonneg ht n) hv ih

omit [Fintype ι] in
/-- A positive vector with `f x ≤ s x` forces `s ≥ 0`. -/
lemma nonneg_of_le_smul [Nonempty ι] (hf : MonotoneHomogeneous f) {x : ι → ℝ} {m s : ℝ}
    (hm : 0 < m) (hxm : ∀ i, m ≤ x i) (h : f x ≤ s • x) : 0 ≤ s := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h0 : 0 ≤ f x i := hf.map_nonneg (fun j => hm.le.trans (hxm j)) i
  have h1 : f x i ≤ s * x i := by simpa using h i
  by_contra hs
  have hs' : s < 0 := not_le.1 hs
  nlinarith [hxm i]

/-- **Upper Collatz–Wielandt bound.** If `x` has entries at least `m > 0` and `f x ≤ s x`, then
`‖fⁿ 𝟙‖ ≤ (‖x‖ / m) sⁿ`. -/
theorem norm_iterate_one_le_of_le_smul (hf : MonotoneHomogeneous f) {x : ι → ℝ} {m s : ℝ}
    (hm : 0 < m) (hxm : ∀ i, m ≤ x i) (h : f x ≤ s • x) (n : ℕ) :
    ‖f^[n] 1‖ ≤ ‖x‖ / m * s ^ n := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim x 0, Subsingleton.elim (f^[n] 1) 0]
  have hs := hf.nonneg_of_le_smul hm hxm h
  have hx0 : 0 ≤ x := fun i => hm.le.trans (hxm i)
  have h1 : (1 : ι → ℝ) ≤ m⁻¹ • x := fun i => by
    simp only [Pi.one_apply, Pi.smul_apply, smul_eq_mul]
    rw [le_inv_mul_iff₀ hm, mul_one]
    exact hxm i
  have h4 : f^[n] 1 ≤ (m⁻¹ * s ^ n) • x := by
    calc f^[n] 1 ≤ m⁻¹ • f^[n] x :=
          (hf.iterate n).le_smul_of_le zero_le_one (inv_nonneg.2 hm.le) hx0 h1
      _ ≤ m⁻¹ • (s ^ n • x) :=
          smul_le_smul_of_nonneg_left (hf.iterate_le_pow_smul hx0 hs h n) (inv_nonneg.2 hm.le)
      _ = (m⁻¹ * s ^ n) • x := smul_smul _ _ _
  have := Matrix.norm_le_norm_of_nonneg_of_le ((hf.iterate n).map_nonneg zero_le_one) h4
  rw [norm_smul_of_nonneg (by positivity)] at this
  calc _ ≤ _ := this
    _ = ‖x‖ / m * s ^ n := by ring

/-- **Upper bound for the cycle time.** A vector `x` with entries at least `m > 0` and
`f x ≤ s x` gives `R(f) ≤ s`. -/
theorem cycleTime_le_of_le_smul [Nonempty ι] (hf : MonotoneHomogeneous f) {x : ι → ℝ}
    {m s : ℝ} (hm : 0 < m) (hxm : ∀ i, m ≤ x i) (h : f x ≤ s • x) : cycleTime f ≤ s := by
  have hs := hf.nonneg_of_le_smul hm hxm h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hK : 0 < ‖x‖ / m := by
    have : m ≤ ‖x‖ := (hxm i).trans ((le_abs_self _).trans (by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x i))
    exact div_pos (hm.trans_le this) hm
  have hlim : Tendsto (fun n : ℕ => (‖x‖ / m) ^ (n : ℝ)⁻¹ * s) atTop (𝓝 s) := by
    simpa using (Real.tendsto_const_rpow_inv hK).mul_const s
  refine le_of_tendsto_of_tendsto hf.tendsto_cycleTime hlim ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  calc ‖f^[n] 1‖ ^ (n : ℝ)⁻¹ ≤ (‖x‖ / m * s ^ n) ^ (n : ℝ)⁻¹ :=
        Real.rpow_le_rpow (norm_nonneg _) (hf.norm_iterate_one_le_of_le_smul hm hxm h n)
          (by positivity)
    _ = (‖x‖ / m) ^ (n : ℝ)⁻¹ * s := by
        rw [Real.mul_rpow hK.le (pow_nonneg hs n), Real.pow_rpow_inv_natCast hs hn]

/-- **Lower Collatz–Wielandt bound.** A vector `0 ≤ v ≠ 0` with `t v ≤ f v` gives `t ≤ R(f)`:
`tⁿ ‖v‖ ≤ ‖fⁿ v‖ ≤ ‖v‖ ‖fⁿ 𝟙‖`. -/
theorem le_cycleTime_of_smul_le (hf : MonotoneHomogeneous f) {v : ι → ℝ} (hv0 : 0 ≤ v)
    (hv : v ≠ 0) {t : ℝ} (ht : t • v ≤ f v) : t ≤ cycleTime f := by
  rcases lt_or_ge t 0 with htn | ht0
  · exact htn.le.trans hf.cycleTime_nonneg
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hpow : ∀ n, t ^ n ≤ ‖f^[n] 1‖ := by
    intro n
    have h2 : t ^ n * ‖v‖ ≤ ‖f^[n] v‖ := by
      have := Matrix.norm_le_norm_of_nonneg_of_le (smul_nonneg (pow_nonneg ht0 n) hv0)
        (hf.pow_smul_le_iterate hv0 ht0 ht n)
      rwa [norm_smul_of_nonneg (pow_nonneg ht0 n)] at this
    have h3 := hf.norm_iterate_le hv0 n
    have : t ^ n * ‖v‖ ≤ ‖f^[n] 1‖ * ‖v‖ := by linarith
    exact le_of_mul_le_mul_right this hvpos
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hf.tendsto_cycleTime ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  calc t = (t ^ n) ^ (n : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast ht0 hn).symm
    _ ≤ ‖f^[n] 1‖ ^ (n : ℝ)⁻¹ := Real.rpow_le_rpow (pow_nonneg ht0 n) (hpow n) (by positivity)

/-- **A positive eigenvector gives the cycle time.** -/
theorem cycleTime_eq_of_eigenvector [Nonempty ι] (hf : MonotoneHomogeneous f) {x : ι → ℝ}
    {m μ : ℝ} (hm : 0 < m) (hxm : ∀ i, m ≤ x i) (hx : f x = μ • x) : cycleTime f = μ := by
  have hx0 : 0 ≤ x := fun i => hm.le.trans (hxm i)
  have hxne : x ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    intro h
    have := hxm i
    rw [h, Pi.zero_apply] at this
    linarith
  exact le_antisymm (hf.cycleTime_le_of_le_smul hm hxm hx.le)
    (hf.le_cycleTime_of_smul_le hx0 hxne hx.ge)

/-- **The ratio test.** If `v` has entries at least `m > 0` and `l v_i ≤ (f v)_i ≤ u v_i` for every
`i`, then `l ≤ R(f) ≤ u`. -/
theorem cycleTime_mem_Icc_of_ratio [Nonempty ι] (hf : MonotoneHomogeneous f) {v : ι → ℝ}
    {m : ℝ} (hm : 0 < m) (hvm : ∀ i, m ≤ v i) {l u : ℝ} (hl : ∀ i, l * v i ≤ f v i)
    (hu : ∀ i, f v i ≤ u * v i) : l ≤ cycleTime f ∧ cycleTime f ≤ u := by
  have hv0 : 0 ≤ v := fun i => hm.le.trans (hvm i)
  have hvne : v ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    intro h
    have := hvm i
    rw [h, Pi.zero_apply] at this
    linarith
  exact ⟨hf.le_cycleTime_of_smul_le hv0 hvne fun i => by simpa using hl i,
    hf.cycleTime_le_of_le_smul hm hvm fun i => by simpa using hu i⟩

/-- **The ratio test with the extreme ratios.** For `v > 0`,
`min_i (f v)_i / v_i ≤ R(f) ≤ max_i (f v)_i / v_i`. -/
theorem cycleTime_mem_Icc_inf_sup [Nonempty ι] (hf : MonotoneHomogeneous f) {v : ι → ℝ}
    (hv : ∀ i, 0 < v i) :
    Finset.univ.inf' Finset.univ_nonempty (fun i => f v i / v i) ≤ cycleTime f ∧
      cycleTime f ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => f v i / v i) := by
  set m := Finset.univ.inf' Finset.univ_nonempty v with hm
  have hm0 : 0 < m := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty v
    rw [hm, hi]
    exact hv i
  refine hf.cycleTime_mem_Icc_of_ratio hm0 (fun i => Finset.inf'_le _ (Finset.mem_univ i))
    (fun i => ?_) (fun i => ?_)
  · have := Finset.inf'_le (fun i => f v i / v i) (Finset.mem_univ i)
    rw [le_div_iff₀ (hv i)] at this
    exact this
  · have := Finset.le_sup' (fun i => f v i / v i) (Finset.mem_univ i)
    rw [div_le_iff₀ (hv i)] at this
    exact this

/-! ### The linear case -/

open scoped Matrix.Norms.Operator

/-- **The cycle time of a nonnegative matrix is its Gelfand radius.** -/
theorem cycleTime_mulVec [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    cycleTime A.mulVec = gelfandRadius A := by
  have hiter : ∀ n : ℕ, A.mulVec^[n] 1 = (A ^ n).mulVec 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Matrix.mulVec_mulVec, pow_succ']
  have h1 := (MonotoneHomogeneous.mulVec hA).tendsto_cycleTime
  simp only [hiter] at h1
  exact tendsto_nhds_unique h1 (Matrix.tendsto_rate_of_pos A hA 1 one_pos fun _ => le_rfl)

end MonotoneHomogeneous
