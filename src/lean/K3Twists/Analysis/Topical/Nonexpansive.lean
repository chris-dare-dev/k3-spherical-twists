/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Convex.HilbertMetric
import K3Twists.Analysis.Topical.Basic

/-!
# Monotone homogeneous maps are nonexpansive

A monotone homogeneous map `f` of the orthant (`MonotoneHomogeneous`) does not increase the
Thompson and Hilbert pseudometrics of `Analysis/Convex/HilbertMetric.lean` on each part of the
cone. A part is the set of nonnegative vectors with a given support; `f` maps two vectors with
the same support to two vectors with the same support. The proof: on the support,
`log x - log y ≤ a` means `x ≤ e^a y`; monotonicity and homogeneity give `f x ≤ e^a f y`, and back
to logarithms (Bushell, Arch. Rational Mech. Anal. 52 (1973); Nussbaum, Mem. Amer. Math. Soc. 75
(1988)).

On the open orthant, for maps that preserve it, these are the statements
`d_T(f x, f y) ≤ d_T(x, y)` and `d_H(f x, f y) ≤ d_H(x, y)`. The maps are not contractions in
general: the identity is monotone homogeneous. Strict contraction is a theorem about positive
linear maps (Birkhoff, `Analysis/Convex/Birkhoff2.lean`), not about this class.

## Main results

* `MonotoneHomogeneous.pos_iff_of_le_smul`: `f` preserves the relation "same support": if
  `x ≤ c • y` and `y ≤ c' • x`, then `f x` and `f y` have the same support.
* `MonotoneHomogeneous.thompsonEDist_map_le`, `MonotoneHomogeneous.hilbertEDist_map_le`:
  nonexpansiveness on each part.
* `MonotoneHomogeneous.thompsonEDist_map_le_of_pos`,
  `MonotoneHomogeneous.hilbertEDist_map_le_of_pos`: the open orthant.
-/

open Real Set
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

/-- `log p - log q ≤ a` for positive `p, q` means `p ≤ e^a q`. -/
lemma le_exp_mul_of_log_sub_le {p q a : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : log p - log q ≤ a) : p ≤ exp a * q := by
  rw [← exp_log hp, ← exp_log hq, ← exp_add]
  exact exp_le_exp.2 (by linarith)

/-- `p ≤ e^a q` for positive `p, q` means `log p - log q ≤ a`. -/
lemma log_sub_le_of_le_exp_mul {p q a : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : p ≤ exp a * q) : log p - log q ≤ a := by
  have := log_le_log hp h
  rw [log_mul (exp_pos a).ne' hq.ne', log_exp] at this
  linarith

omit [Fintype ι] in
/-- Two nonnegative vectors with the same support and `log x - log y ≤ a` on it satisfy
`x ≤ e^a y`. -/
lemma le_exp_smul_of_log_sub_le {x y : ι → ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hsupp : ∀ i, 0 < x i ↔ 0 < y i) {a : ℝ} (h : ∀ i, 0 < x i → log (x i) - log (y i) ≤ a) :
    x ≤ exp a • y := fun i => by
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hi : 0 < x i
  · exact le_exp_mul_of_log_sub_le hi ((hsupp i).1 hi) (h i hi)
  · rw [le_antisymm (not_lt.1 hi) (hx0 i)]
    exact mul_nonneg (exp_pos a).le (hy0 i)

namespace MonotoneHomogeneous

variable {f : (ι → ℝ) → ι → ℝ}

omit [Fintype ι] in
/-- If `x ≤ c y` and `y ≤ c' x`, then `f x` and `f y` have the same support. -/
lemma pos_iff_of_le_smul (hf : MonotoneHomogeneous f) {x y : ι → ℝ} (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hxy : x ≤ c • y) (hyx : y ≤ c' • x)
    (i : ι) : 0 < f x i ↔ 0 < f y i := by
  have h1 := hf.le_smul_of_le hx0 hc hy0 hxy i
  have h2 := hf.le_smul_of_le hy0 hc' hx0 hyx i
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  exact ⟨fun h => pos_of_mul_pos_right (h.trans_le h1) hc,
    fun h => pos_of_mul_pos_right (h.trans_le h2) hc'⟩

/-- **Nonexpansiveness for the Thompson pseudometric**, on each part: if `x, y ≥ 0` have the same
support, so do `f x` and `f y`, and `d_T(f x, f y) ≤ d_T(x, y)` on the supports. -/
theorem thompsonEDist_map_le (hf : MonotoneHomogeneous f) {x y : ι → ℝ} (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) (hsupp : ∀ i, 0 < x i ↔ 0 < y i) :
    (∀ i, 0 < f x i ↔ 0 < f y i) ∧
      thompsonEDist {i | 0 < f x i} (f x) (f y) ≤ thompsonEDist {i | 0 < x i} x y := by
  set D := thompsonEDist {i | 0 < x i} x y with hDdef
  have hD : D ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (thompsonEDist_le_iff.2 fun i _ =>
      ENNReal.ofReal_le_ofReal (Finset.single_le_sum
        (f := fun i => |log (x i) - log (y i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  set d := D.toReal with hd
  have hdi : ∀ i, 0 < x i → |log (x i) - log (y i)| ≤ d := fun i hi => by
    have := le_thompsonEDist (s := {i | 0 < x i}) (x := x) (y := y) hi
    rw [← hDdef, ← ENNReal.ofReal_toReal hD,
      ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at this
    exact this
  have hxy : x ≤ exp d • y :=
    le_exp_smul_of_log_sub_le hx0 hy0 hsupp fun i hi => (le_abs_self _).trans (hdi i hi)
  have hyx : y ≤ exp d • x := le_exp_smul_of_log_sub_le hy0 hx0 (fun i => (hsupp i).symm)
    fun i hi => by
      have := hdi i ((hsupp i).2 hi)
      rw [abs_sub_comm] at this
      exact (le_abs_self _).trans this
  have hfsupp := hf.pos_iff_of_le_smul hx0 hy0 (exp_pos d).le (exp_pos d).le hxy hyx
  have hfxy := hf.le_smul_of_le hx0 (exp_pos d).le hy0 hxy
  have hfyx := hf.le_smul_of_le hy0 (exp_pos d).le hx0 hyx
  refine ⟨hfsupp, thompsonEDist_le_iff.2 fun i hi => ?_⟩
  have hpx : 0 < f x i := hi
  have hpy : 0 < f y i := (hfsupp i).1 hi
  rw [← ENNReal.ofReal_toReal hD]
  refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩)
  · have := log_sub_le_of_le_exp_mul hpy hpx (by simpa using hfyx i)
    linarith
  · exact log_sub_le_of_le_exp_mul hpx hpy (by simpa using hfxy i)

/-- **Nonexpansiveness for the Hilbert pseudometric**, on each part: if `x, y ≥ 0` have the same
support, `d_H(f x, f y) ≤ d_H(x, y)` on the supports. -/
theorem hilbertEDist_map_le (hf : MonotoneHomogeneous f) {x y : ι → ℝ} (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) (hsupp : ∀ i, 0 < x i ↔ 0 < y i) :
    hilbertEDist {i | 0 < f x i} (f x) (f y) ≤ hilbertEDist {i | 0 < x i} x y := by
  classical
  by_cases hs : ∃ i, 0 < x i
  · set S := Finset.univ.filter fun i => 0 < x i with hSdef
    have hS : S.Nonempty := by
      obtain ⟨i, hi⟩ := hs
      exact ⟨i, by simp [hSdef, hi]⟩
    have hmemS : ∀ {i}, i ∈ S ↔ 0 < x i := by simp [hSdef]
    set g : ι → ℝ := fun i => log (x i) - log (y i) with hg
    obtain ⟨i₀, hi₀S, hi₀⟩ := S.exists_max_image g hS
    obtain ⟨j₀, hj₀S, hj₀⟩ := S.exists_min_image g hS
    have hxy : x ≤ exp (g i₀) • y :=
      le_exp_smul_of_log_sub_le hx0 hy0 hsupp fun i hi => hi₀ i (hmemS.2 hi)
    have hyx : y ≤ exp (-g j₀) • x := le_exp_smul_of_log_sub_le hy0 hx0
      (fun i => (hsupp i).symm) fun i hi => by
        have := hj₀ i (hmemS.2 ((hsupp i).2 hi))
        simp only [hg] at this ⊢
        linarith
    have hfsupp := hf.pos_iff_of_le_smul hx0 hy0 (exp_pos _).le (exp_pos _).le hxy hyx
    have hfxy := hf.le_smul_of_le hx0 (exp_pos _).le hy0 hxy
    have hfyx := hf.le_smul_of_le hy0 (exp_pos _).le hx0 hyx
    refine hilbertEDist_le_iff.2 fun i hi j hj => ?_
    have hpi : 0 < f x i := hi
    have hpj : 0 < f x j := hj
    have h1 := log_sub_le_of_le_exp_mul hpi ((hfsupp i).1 hpi) (by simpa using hfxy i)
    have h2 := log_sub_le_of_le_exp_mul ((hfsupp j).1 hpj) hpj (by simpa using hfyx j)
    calc ENNReal.ofReal ((log (f x i) - log (f y i)) - (log (f x j) - log (f y j)))
        ≤ ENNReal.ofReal (g i₀ - g j₀) := ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ hilbertEDist {i | 0 < x i} x y :=
        le_hilbertEDist (hmemS.1 hi₀S) (hmemS.1 hj₀S)
  · push Not at hs
    have hx : x = 0 := funext fun i => le_antisymm (hs i) (hx0 i)
    have hfx : {i | 0 < f x i} = ∅ := by
      rw [hx, hf.map_zero]
      ext i
      simp
    rw [hfx, hilbertEDist_empty]
    exact zero_le

/-- **Thompson nonexpansiveness on the open orthant.** -/
theorem thompsonEDist_map_le_of_pos (hf : MonotoneHomogeneous f) {x y : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hfx : ∀ i, 0 < f x i) :
    thompsonEDist univ (f x) (f y) ≤ thompsonEDist univ x y := by
  have h := (hf.thompsonEDist_map_le (fun i => (hx i).le) (fun i => (hy i).le)
    fun i => ⟨fun _ => hy i, fun _ => hx i⟩).2
  rwa [show {i | 0 < f x i} = univ from eq_univ_of_forall hfx,
    show {i | 0 < x i} = univ from eq_univ_of_forall hx] at h

/-- **Hilbert nonexpansiveness on the open orthant.** -/
theorem hilbertEDist_map_le_of_pos (hf : MonotoneHomogeneous f) {x y : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hfx : ∀ i, 0 < f x i) :
    hilbertEDist univ (f x) (f y) ≤ hilbertEDist univ x y := by
  have h := hf.hilbertEDist_map_le (fun i => (hx i).le) (fun i => (hy i).le)
    fun i => ⟨fun _ => hy i, fun _ => hx i⟩
  rwa [show {i | 0 < f x i} = univ from eq_univ_of_forall hfx,
    show {i | 0 < x i} = univ from eq_univ_of_forall hx] at h

end MonotoneHomogeneous
