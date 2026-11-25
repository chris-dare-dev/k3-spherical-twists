/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Order.Polynomial

/-!
# The polynomial modulus lemma

Let `P` be a complex polynomial and `c > 0`. If the moduli `|P(n)|` lie in the lattice `cℤ` for
all large integers `n`, then `P P̄ = q²` for a real polynomial `q`, where `P̄` has the conjugate
coefficients (`Polynomial.exists_mul_map_conj_eq_sq`). On the real line `P P̄ = |P|²`, so `|P|`
is then a polynomial function there. A monic quadratic with this property has real coefficients
or is a square `(X + b)²` (`Polynomial.im_eq_zero_or_eq_sq_of_mul_map_conj_eq_sq`), and the
second case occurs with `b` not real: `|(n + i)²| = n² + 1`.

## Proof

Write `F = P P̄ = (Re P)² + (Im P)²`, a real polynomial of degree `2d` with positive leading
coefficient, and `a(n) = |P(n)|`, so that `a(n)² = F(n)` (`mul_map_conj_eq`, `eval_mul_map_conj`).

* **Square-root approximation** (`exists_degree_sub_sq_lt`): there is a real `q₀` of degree `d`
  with positive leading coefficient and `deg(F - q₀²) < d`, found by matching the top `d + 1`
  coefficients one at a time.
* Then `a(n) - q₀(n) = (F - q₀²)(n)/(a(n) + q₀(n)) → 0`, with no Taylor expansion.
* The `(d + 1)`-st forward difference of `a` is that of `a - q₀`, so it tends to zero; it lies
  in `cℤ` for large `n`, so it vanishes for large `n`.
* By the Gregory–Newton formula (`exists_eval_eq_of_fwdDiff_iter_eq_zero`) `a` agrees with a
  polynomial `Q` from some `N₀` on, so `F` and `Q(X - N₀)²` agree at infinitely many points and
  are equal (`exists_eq_sq_of_eventually_mem_zmultiples`).

The quadratic case compares the coefficients of the real quartic
`(X² + αX + δ)² + (βX + ε)² = q²`, read off from five values.
-/

open Filter Topology Finset

namespace Polynomial

/-- Matching the top coefficients of a square root: for `F` of degree `2d` with positive leading
coefficient and `k ≤ d` there is `q` of degree `d` with leading coefficient `√(lead F)` such that
`F - q²` has no coefficient in degrees `≥ 2d - k`. -/
theorem exists_coeff_sub_sq_eq_zero {F : ℝ[X]} {d : ℕ} (hF : F.natDegree = 2 * d)
    (hlc : 0 < F.leadingCoeff) :
    ∀ k ≤ d, ∃ q : ℝ[X], q.natDegree = d ∧ q.leadingCoeff = Real.sqrt F.leadingCoeff ∧
      ∀ m, 2 * d - k ≤ m → (F - q ^ 2).coeff m = 0 := by
  set b := Real.sqrt F.leadingCoeff
  have hb : 0 < b := Real.sqrt_pos.mpr hlc
  have hb2 : b ^ 2 = F.leadingCoeff := Real.sq_sqrt hlc.le
  intro k hk
  induction k with
  | zero =>
    refine ⟨C b * X ^ d, by rw [natDegree_C_mul_X_pow _ _ hb.ne'], by
      rw [leadingCoeff_C_mul_X_pow], fun m hm => ?_⟩
    rw [coeff_sub, mul_pow, ← C_pow, ← pow_mul, coeff_C_mul_X_pow]
    rcases (show 2 * d - 0 ≤ m from hm).eq_or_lt with h | h
    · simp only [Nat.sub_zero] at h
      subst h
      rw [mul_comm d 2, ite_eq_left rfl]
      have : F.coeff (2 * d) = F.leadingCoeff := by rw [leadingCoeff, hF]
      rw [this, hb2, sub_self]
    · rw [ite_eq_right (by omega), coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
  | succ k ih =>
    obtain ⟨q, hqd, hqlc, hq⟩ := ih (by omega)
    set R := F - q ^ 2
    set l := d - k - 1 with hl
    set e := R.coeff (2 * d - k - 1)
    set c := e / (2 * b)
    refine ⟨q + C c * X ^ l, ?_, ?_, fun m hm => ?_⟩
    · rw [natDegree_add_eq_left_of_natDegree_lt]
      · exact hqd
      · calc (C c * X ^ l).natDegree ≤ l := natDegree_C_mul_X_pow_le _ _
          _ < d := by omega
          _ = q.natDegree := hqd.symm
    · have hq0 : q ≠ 0 := by
        rintro rfl
        simp only [leadingCoeff_zero] at hqlc
        linarith
      rw [leadingCoeff_add_of_degree_lt', hqlc]
      refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
      rw [degree_eq_natDegree hq0, hqd]
      exact_mod_cast (show l < d by omega)
    · have hexp : F - (q + C c * X ^ l) ^ 2 =
          R - (C (2 * c) * (X ^ l * q) + C (c ^ 2) * X ^ (2 * l)) := by
        simp only [R, map_mul, map_pow, C_ofNat, pow_mul]
        ring
      have hS : (C (c ^ 2) * X ^ (2 * l)).coeff m = 0 := by
        rw [coeff_C_mul, coeff_X_pow, ite_eq_right (by omega), mul_zero]
      have hT : (C (2 * c) * (X ^ l * q)).coeff m =
          2 * c * (if l ≤ m then q.coeff (m - l) else 0) := by
        rw [coeff_C_mul, coeff_X_pow_mul']
      rw [hexp, coeff_sub, coeff_add, hS, add_zero, hT, ite_eq_left (by omega)]
      rcases (show 2 * d - (k + 1) ≤ m from hm).eq_or_lt with h | h
      · -- the top coefficient cancels
        have h1 : m - l = d := by omega
        have h2 : R.coeff m = e := by simp only [e]; congr 1; omega
        have h3 : q.coeff d = b := by rw [← hqlc, leadingCoeff, hqd]
        rw [h1, h2, h3]
        simp only [c]
        field_simp
        ring
      · rw [hq m (by omega), coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < m - l),
          mul_zero, sub_zero]

/-- **Polynomial approximation of a square root.** A real polynomial `F` of degree `2d` with
positive leading coefficient is `q² + R` with `q` of degree `d`, positive leading coefficient, and
`deg R < d`. -/
theorem exists_degree_sub_sq_lt {F : ℝ[X]} {d : ℕ} (hF : F.natDegree = 2 * d)
    (hlc : 0 < F.leadingCoeff) :
    ∃ q : ℝ[X], q.natDegree = d ∧ 0 < q.leadingCoeff ∧ (F - q ^ 2).degree < d := by
  obtain ⟨q, hqd, hqlc, hq⟩ := exists_coeff_sub_sq_eq_zero hF hlc d le_rfl
  refine ⟨q, hqd, hqlc ▸ Real.sqrt_pos.mpr hlc, ?_⟩
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  exact hq m (by omega)

open fwdDiff in
/-- **Gregory–Newton.** A real sequence whose `(d + 1)`-st forward differences vanish is the
sequence of values `Q(m)` of a real polynomial `Q` (of degree at most `d`). -/
theorem exists_eval_eq_of_fwdDiff_iter_eq_zero {b : ℕ → ℝ} {d : ℕ}
    (hb : ∀ m, Δ_[1]^[d + 1] b m = 0) : ∃ Q : ℝ[X], ∀ m : ℕ, b m = Q.eval (m : ℝ) := by
  have hzero : ∀ k, d + 1 ≤ k → Δ_[1]^[k] b 0 = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_comm, Function.iterate_add_apply]
    have h0 : (Δ_[1]^[d + 1] b) = 0 := _root_.funext fun m => hb m
    have hfix : Δ_[1] (0 : ℕ → ℝ) = 0 := _root_.funext fun x => by simp [fwdDiff]
    rw [h0, Function.iterate_fixed hfix]
    rfl
  set β : ℕ → ℝ := fun k => Δ_[1]^[k] b 0
  refine ⟨∑ k ∈ range (d + 1), C (β k / k.factorial) * descPochhammer ℝ k, fun m => ?_⟩
  have hGN := shift_eq_sum_fwdDiff_iter 1 b m 0
  simp only [smul_eq_mul, mul_one, zero_add, nsmul_eq_mul] at hGN
  rw [hGN, eval_finsetSum]
  have h1 : ∑ k ∈ range (m + 1), (m.choose k : ℝ) * β k =
      ∑ k ∈ range (m + d + 2), (m.choose k : ℝ) * β k := by
    refine sum_subset (range_subset_range.mpr (by omega)) fun k hk hk' => ?_
    rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hk'; omega), Nat.cast_zero,
      zero_mul]
  have h2 : ∑ k ∈ range (d + 1), (m.choose k : ℝ) * β k =
      ∑ k ∈ range (m + d + 2), (m.choose k : ℝ) * β k := by
    refine sum_subset (range_subset_range.mpr (by omega)) fun k hk hk' => ?_
    rw [show β k = 0 from hzero k (by simp only [mem_range] at hk'; omega), mul_zero]
  change ∑ k ∈ range (m + 1), (m.choose k : ℝ) * β k = _
  rw [h1, ← h2]
  refine sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

open fwdDiff in
/-- **The polynomial modulus lemma over `ℝ`.** Let `F` be a real polynomial of degree `2d` with
positive leading coefficient, and `a` a nonnegative sequence with `a n ^ 2 = F(n)`. If
`a n ∈ cℤ` for all large `n`, for some `c > 0`, then `F = q²` for a real polynomial `q`. -/
theorem exists_eq_sq_of_eventually_mem_zmultiples {F : ℝ[X]} {d : ℕ} (hF : F.natDegree = 2 * d)
    (hlc : 0 < F.leadingCoeff) {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (ha : ∀ n, a n ^ 2 = F.eval (n : ℝ)) {c : ℝ} (hc : 0 < c)
    (hmem : ∀ᶠ n in atTop, a n ∈ AddSubgroup.zmultiples c) : ∃ q : ℝ[X], F = q ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- a constant
    refine ⟨C (Real.sqrt F.leadingCoeff), ?_⟩
    rw [← C_pow, Real.sq_sqrt hlc.le, leadingCoeff, hF, mul_zero]
    exact eq_C_of_natDegree_eq_zero (by rw [hF])
  obtain ⟨q, hqd, hqlc, hRq⟩ := exists_degree_sub_sq_lt hF hlc
  set R := F - q ^ 2
  have hq0 : q ≠ 0 := by rintro rfl; simp at hqlc
  have hqdeg : q.degree = d := by rw [degree_eq_natDegree hq0, hqd]
  -- the square root of `F` is `q` up to `o(1)`
  have hqpos : ∀ᶠ x in atTop, 0 < q.eval x :=
    (tendsto_atTop_of_leadingCoeff_nonneg (P := q) (by rw [hqdeg]; exact_mod_cast hd)
      hqlc.le).eventually_gt_atTop 0
  have hdiv : Tendsto (fun x => R.eval x / q.eval x) atTop (𝓝 0) :=
    (isLittleO_atTop_of_degree_lt R q (by rw [hqdeg]; exact hRq)).tendsto_div_nhds_zero
  set g : ℕ → ℝ := fun n => a n - q.eval (n : ℝ)
  have hg : Tendsto g atTop (𝓝 0) := by
    have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
    have hlim : Tendsto (fun n : ℕ => ‖R.eval (n : ℝ) / q.eval (n : ℝ)‖) atTop (𝓝 0) := by
      simpa using (hdiv.comp hcast).norm
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hcast.eventually hqpos] with n hn
    simp only [Real.norm_eq_abs, g]
    have hsum : 0 < a n + q.eval (n : ℝ) := by linarith [ha0 n]
    have hkey : a n - q.eval (n : ℝ) = R.eval (n : ℝ) / (a n + q.eval (n : ℝ)) := by
      rw [eq_div_iff hsum.ne']
      simp only [R, eval_sub, eval_pow, ← ha n]
      ring
    rw [hkey, abs_div, abs_div, abs_of_pos hsum, abs_of_pos hn]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hn (by linarith [ha0 n])
  -- the `(d + 1)`-st difference of `a` tends to zero
  set L : (ℕ → ℝ) → ℕ → ℝ := fun f n => ∑ k ∈ range (d + 1 + 1),
    ((-1 : ℤ) ^ (d + 1 - k) * ((d + 1).choose k : ℤ)) • f (n + k)
  have hLa : ∀ n, Δ_[1]^[d + 1] a n = L a n := fun n => by
    rw [fwdDiff_iter_eq_sum_shift]
    simp [L]
  have hLq : ∀ n : ℕ, L (fun n => q.eval (n : ℝ)) n = 0 := fun n => by
    have := congrFun (fwdDiff_iter_eq_zero_of_degree_lt (P := q) (n := d + 1) (by omega)) n
    rw [fwdDiff_iter_eq_sum_shift] at this
    simpa [L] using this
  have hLg : Tendsto (L g) atTop (𝓝 0) := by
    have : Tendsto (L g) atTop (𝓝 (∑ k ∈ range (d + 1 + 1),
        ((-1 : ℤ) ^ (d + 1 - k) * ((d + 1).choose k : ℤ)) • (0 : ℝ))) :=
      tendsto_finsetSum _ fun k _ => (hg.comp (tendsto_add_atTop_nat k)).const_smul _
    simpa using this
  have hsplit : ∀ n, L a n = L g n := fun n => by
    have : L a n = L (fun n => q.eval (n : ℝ)) n + L g n := by
      simp only [L, g, ← sum_add_distrib, ← smul_add]
      congr 1 with k
      ring_nf
    rw [this, hLq, zero_add]
  -- an element of `cℤ` of modulus less than `c` is zero
  have hLmem : ∀ᶠ n in atTop, L a n ∈ AddSubgroup.zmultiples c := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hmem
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    exact AddSubgroup.sum_mem _ fun k _ => AddSubgroup.zsmul_mem _ (hN _ (by omega)) _
  have hsmall : ∀ᶠ n in atTop, |L a n| < c := by
    have := (hLg.abs).eventually (gt_mem_nhds (a := c) (by simpa using hc))
    filter_upwards [this] with n hn
    rw [hsplit]
    simpa using hn
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hLmem.and hsmall)
  have hvan : ∀ n, N₀ ≤ n → Δ_[1]^[d + 1] a n = 0 := by
    intro n hn
    obtain ⟨hm, hs⟩ := hN₀ n hn
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
    rw [hLa, ← hk]
    rw [← hk, zsmul_eq_mul, abs_mul, abs_of_pos hc] at hs
    have : |(k : ℝ)| < 1 := by nlinarith [abs_nonneg (k : ℝ)]
    have : k = 0 := by
      rw [← Int.cast_abs] at this
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast this)
    simp [this]
  -- Gregory–Newton from `N₀` on
  obtain ⟨Q, hQ⟩ := exists_eval_eq_of_fwdDiff_iter_eq_zero (b := fun m => a (m + N₀)) (d := d)
    fun m => by
      rw [fwdDiff_iter_comp_add]
      exact hvan _ (by omega)
  refine ⟨Q.comp (X - C (N₀ : ℝ)), eq_of_infinite_eval_eq _ _ ?_⟩
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : ℝ) + N₀)
    (fun m m' h => by simpa using h) fun m => ?_
  simp only [Set.mem_ofPred_eq, eval_pow, eval_comp, eval_sub, eval_X, eval_C, add_sub_cancel_right]
  rw [← hQ m, ← Nat.cast_add, ha]

/-! ### Complex polynomials -/

/-- The real polynomial of the real parts of the coefficients of `P`. -/
noncomputable def rePart (P : ℂ[X]) : ℝ[X] := ∑ n ∈ P.support, C (P.coeff n).re * X ^ n

/-- The real polynomial of the imaginary parts of the coefficients of `P`. -/
noncomputable def imPart (P : ℂ[X]) : ℝ[X] := ∑ n ∈ P.support, C (P.coeff n).im * X ^ n

@[simp]
lemma coeff_rePart (P : ℂ[X]) (m : ℕ) : (rePart P).coeff m = (P.coeff m).re := by
  simp only [rePart, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, Complex.zero_re]

@[simp]
lemma coeff_imPart (P : ℂ[X]) (m : ℕ) : (imPart P).coeff m = (P.coeff m).im := by
  simp only [imPart, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, Complex.zero_im]

/-- `P = Re P + i Im P` coefficientwise. -/
lemma eq_rePart_add_imPart (P : ℂ[X]) :
    P = (rePart P).map Complex.ofRealHom + C Complex.I * (imPart P).map Complex.ofRealHom := by
  ext m
  apply Complex.ext <;> simp [coeff_map]

/-- `P P̄ = (Re P)² + (Im P)²`. -/
lemma mul_map_conj_eq (P : ℂ[X]) :
    P * P.map (starRingEnd ℂ) =
      ((rePart P) ^ 2 + (imPart P) ^ 2).map Complex.ofRealHom := by
  have hP := eq_rePart_add_imPart P
  set A := rePart P
  set B := imPart P
  have hconj : P.map (starRingEnd ℂ) =
      A.map Complex.ofRealHom - C Complex.I * B.map Complex.ofRealHom := by
    rw [hP]
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_map,
      Complex.conj_I, map_neg]
    have : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
      ext x
      simp
    rw [this]
    ring
  have hI : (C Complex.I) ^ 2 = (-1 : ℂ[X]) := by
    rw [← C_pow, Complex.I_sq, C_neg, C_1]
  rw [hconj, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_pow]
  conv_lhs => arg 1; rw [hP]
  linear_combination (-(B.map Complex.ofRealHom) ^ 2) * hI

/-- On real points, `P P̄` takes the value `|P(x)|²`. -/
lemma eval_mul_map_conj (P : ℂ[X]) (x : ℝ) :
    (P * P.map (starRingEnd ℂ)).eval (x : ℂ) = ((‖P.eval (x : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [eval_mul, eval_map]
  have : eval₂ (starRingEnd ℂ) (x : ℂ) P = starRingEnd ℂ (P.eval (x : ℂ)) := by
    rw [← eval₂_at_apply, Complex.conj_ofReal]
  rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The polynomial modulus lemma.** Let `P` be a complex polynomial and `c > 0`. If
`|P(n)| ∈ cℤ` for all large integers `n`, then `P P̄ = q²` for a real polynomial `q`. -/
theorem exists_mul_map_conj_eq_sq {P : ℂ[X]} {c : ℝ} (hc : 0 < c)
    (hmem : ∀ᶠ n : ℕ in atTop, ‖P.eval (n : ℂ)‖ ∈ AddSubgroup.zmultiples c) :
    ∃ q : ℝ[X], P * P.map (starRingEnd ℂ) = (q.map Complex.ofRealHom) ^ 2 := by
  rcases eq_or_ne P 0 with rfl | hP
  · exact ⟨0, by simp⟩
  set F := rePart P ^ 2 + imPart P ^ 2
  have hFmap := mul_map_conj_eq P
  have hinj : Function.Injective Complex.ofRealHom := Complex.ofReal_injective
  have hconjP : P.map (starRingEnd ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (starRingEnd ℂ).injective).mpr hP
  have hdeg : F.natDegree = 2 * P.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj F, ← hFmap, natDegree_mul hP hconjP,
      natDegree_map_eq_of_injective (starRingEnd ℂ).injective]
    ring
  have hlc : 0 < F.leadingCoeff := by
    have h := congrArg leadingCoeff hFmap
    rw [leadingCoeff_mul, leadingCoeff_map_of_injective (starRingEnd ℂ).injective,
      leadingCoeff_map_of_injective hinj, Complex.mul_conj] at h
    rw [Complex.ofRealHom_eq_coe] at h
    have h' : Complex.normSq P.leadingCoeff = F.leadingCoeff := by exact_mod_cast h
    rw [← h']
    exact Complex.normSq_pos.mpr (leadingCoeff_ne_zero.mpr hP)
  have heval : ∀ n : ℕ, ‖P.eval (n : ℂ)‖ ^ 2 = F.eval (n : ℝ) := fun n => by
    have h1 := eval_mul_map_conj P n
    rw [hFmap, eval_map, ← Complex.ofRealHom_eq_coe, eval₂_at_apply] at h1
    exact_mod_cast (Complex.ofReal_injective h1).symm
  obtain ⟨q, hq⟩ := exists_eq_sq_of_eventually_mem_zmultiples hdeg hlc (fun n => norm_nonneg _)
    heval hc hmem
  refine ⟨q, ?_⟩
  rw [hFmap, show rePart P ^ 2 + imPart P ^ 2 = q ^ 2 from hq, Polynomial.map_pow]

/-! ### Monic quadratics -/

/-- **The monic quadratic case.** If `P = X² + uX + v` has `P P̄ = q²` for a real polynomial `q`,
then `P` has real coefficients or `P = (X + u/2)²`. -/
theorem im_eq_zero_or_eq_sq_of_mul_map_conj_eq_sq {u v : ℂ} {q : ℝ[X]}
    (h : (X ^ 2 + C u * X + C v) * (X ^ 2 + C u * X + C v).map (starRingEnd ℂ) =
      (q.map Complex.ofRealHom) ^ 2) :
    (u.im = 0 ∧ v.im = 0) ∨ X ^ 2 + C u * X + C v = (X + C (u / 2)) ^ 2 := by
  set P : ℂ[X] := X ^ 2 + C u * X + C v
  set α := u.re
  set β := u.im
  set δ := v.re
  set ε := v.im
  -- the real identity `A² + B² = q²`
  have hA : rePart P = X ^ 2 + C α * X + C δ := by
    ext m
    simp only [coeff_rePart, P, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    rcases m with _ | _ | _ | m <;> simp [α, δ]
  have hB : imPart P = C β * X + C ε := by
    ext m
    simp only [coeff_imPart, P, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    rcases m with _ | _ | _ | m <;> simp [β, ε]
  have hreal : (X ^ 2 + C α * X + C δ) ^ 2 + (C β * X + C ε) ^ 2 = q ^ 2 := by
    apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
    rw [← hA, ← hB, ← mul_map_conj_eq, Polynomial.map_pow]
    exact h
  -- `q` has degree two
  have hAdeg : (X ^ 2 + C α * X + C δ : ℝ[X]).natDegree = 2 := by
    have := natDegree_quadratic (R := ℝ) (a := 1) (b := α) (c := δ) one_ne_zero
    simpa using this
  have hBdeg : (C β * X + C ε : ℝ[X]).natDegree ≤ 1 := natDegree_linear_le
  have hB2 : ((C β * X + C ε : ℝ[X]) ^ 2).natDegree <
      ((X ^ 2 + C α * X + C δ : ℝ[X]) ^ 2).natDegree := by
    rw [natDegree_pow, natDegree_pow, hAdeg]
    omega
  have hlhs : ((X ^ 2 + C α * X + C δ) ^ 2 + (C β * X + C ε) ^ 2 : ℝ[X]).natDegree = 4 := by
    rw [natDegree_add_eq_left_of_natDegree_lt hB2, natDegree_pow, hAdeg]
  have hqdeg : q.natDegree = 2 := by
    have := congrArg natDegree hreal
    rw [hlhs, natDegree_pow] at this
    omega
  set q₀ := q.coeff 0
  set q₁ := q.coeff 1
  set q₂ := q.coeff 2
  have hq : ∀ x : ℝ, q.eval x = q₂ * x ^ 2 + q₁ * x + q₀ := fun x => by
    rw [q.as_sum_range_C_mul_X_pow, hqdeg]
    simp [Finset.sum_range_succ, q₀, q₁, q₂]
    ring
  have he : ∀ x : ℝ, (x ^ 2 + α * x + δ) ^ 2 + (β * x + ε) ^ 2 =
      (q₂ * x ^ 2 + q₁ * x + q₀) ^ 2 := fun x => by
    have := congrArg (eval x) hreal
    simpa [hq x] using this
  have e0 := he 0
  have e1 := he 1
  have e2 := he (-1)
  have e3 := he 2
  have e4 := he (-2)
  norm_num at e0 e1 e2 e3 e4
  -- the coefficients of the quartic identity
  have d4 : 1 - q₂ ^ 2 = 0 := by linear_combination (e3 + e4 - 4 * e1 - 4 * e2 + 6 * e0) / 24
  have d3 : 2 * α - 2 * q₂ * q₁ = 0 := by linear_combination (e3 - e4 - 2 * e1 + 2 * e2) / 12
  have d2 : α ^ 2 + 2 * δ + β ^ 2 - q₁ ^ 2 - 2 * q₂ * q₀ = 0 := by
    linear_combination (16 * e1 + 16 * e2 - e3 - e4 - 30 * e0) / 24
  have d1 : 2 * α * δ + 2 * β * ε - 2 * q₁ * q₀ = 0 := by
    linear_combination (8 * e1 - 8 * e2 - e3 + e4) / 12
  have d0 : δ ^ 2 + ε ^ 2 - q₀ ^ 2 = 0 := by linear_combination e0
  have hq₁ : q₁ = q₂ * α := by linear_combination (-q₂ / 2) * d3 + q₁ * d4
  have hq₀ : q₀ = q₂ * (δ + β ^ 2 / 2) := by
    rw [hq₁] at d2
    linear_combination (-q₂ / 2) * d2 + (q₀ + q₂ * α ^ 2 / 2) * d4
  have hβε : β * ε = α * β ^ 2 / 2 := by
    rw [hq₁, hq₀] at d1
    linear_combination d1 / 2 - (α * (δ + β ^ 2 / 2)) * d4
  have hε2 : ε ^ 2 = δ * β ^ 2 + β ^ 4 / 4 := by
    rw [hq₀] at d0
    linear_combination d0 - (δ + β ^ 2 / 2) ^ 2 * d4
  by_cases hβ : β = 0
  · left
    refine ⟨hβ, ?_⟩
    rw [hβ] at hε2
    simpa using hε2
  · right
    have hε : ε = α * β / 2 := by
      apply mul_left_cancel₀ hβ
      linear_combination hβε
    have hδ : δ = (α ^ 2 - β ^ 2) / 4 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hβ)
      rw [hε] at hε2
      linear_combination -hε2
    have hv : v = u ^ 2 / 4 := by
      apply Complex.ext
      · simp only [Complex.div_re, sq, Complex.mul_re]
        rw [show v.re = δ from rfl, hδ]
        simp [α, β]
        ring
      · simp only [Complex.div_ofNat_im, sq, Complex.mul_im]
        rw [show v.im = ε from rfl, hε]
        simp [α, β]
        ring
    simp only [P, hv]
    rw [show C (u ^ 2 / 4) = C (u / 2) ^ 2 by rw [← C_pow]; ring_nf,
      show C u = 2 * C (u / 2) by rw [← C_ofNat, ← C_mul]; ring_nf]
    ring

end Polynomial
