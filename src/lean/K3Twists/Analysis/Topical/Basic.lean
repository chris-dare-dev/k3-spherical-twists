/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.GelfandRadius
import Mathlib.Analysis.Subadditive

/-!
# Monotone homogeneous maps of the orthant and their cycle time

A map `f : (ι → ℝ) → (ι → ℝ)` is **monotone homogeneous** (`MonotoneHomogeneous f`) if it maps the
nonnegative orthant into itself and is monotone and positively homogeneous of degree one there:
`0 ≤ x ≤ y ⇒ f x ≤ f y` and `f (c • x) = c • f x` for `c ≥ 0`, all inequalities coordinatewise.
These are the order-preserving homogeneous maps of the closed cone `ℝ^ι_{≥0}` of Gaubert and
Gunawardena (*The Perron–Frobenius theorem for homogeneous, monotone functions*, Trans. Amer. Math.
Soc. 356 (2004)) and of Lemmens and Nussbaum (*Nonlinear Perron–Frobenius theory*, Cambridge
Tracts in Mathematics 189, Chapter 5). "Topical" refers to their additive form on the open orthant;
the structure is named after the multiplicative properties it asks for. Nonnegative matrices,
coordinatewise maxima and minima of such maps and their composites are examples; no linearity is
assumed.

The **cycle time** `R(f) = lim ‖fⁿ 𝟙‖^{1/n}` (`cycleTime`) exists because `n ↦ ‖fⁿ 𝟙‖` is
submultiplicative for the sup norm: `f^{m+n} 𝟙 = fᵐ(fⁿ 𝟙) ≤ ‖fⁿ 𝟙‖ fᵐ 𝟙`. It is the infimum of
`‖fⁿ 𝟙‖^{1/n}` over `n ≥ 1`. Mathlib's `gelfandRadius` is defined in a normed algebra and does not
apply to a nonlinear `f`.

## Main results

* `MonotoneHomogeneous.comp`, `.iterate`, `.mulVec`, `.sup`, `.inf`: the class is closed under
  composition, and contains nonnegative matrices and coordinatewise maxima and minima.
* `MonotoneHomogeneous.norm_iterate_add_le`: `‖f^{m+n} 𝟙‖ ≤ ‖fᵐ 𝟙‖ ‖fⁿ 𝟙‖`.
* `MonotoneHomogeneous.tendsto_cycleTime`, `cycleTime_le`, `pow_cycleTime_le`: the cycle time is the
  limit and the infimum of `‖fⁿ 𝟙‖^{1/n}`.
* `MonotoneHomogeneous.tendsto_cycleTime_of_bounds`: a start with `c 𝟙 ≤ u ≤ C 𝟙`, `c > 0`, has the
  same rate; `MonotoneHomogeneous.limsup_le_cycleTime`: every start `v ≥ 0` grows at most at the
  cycle time.
* `MonotoneHomogeneous.le_iterate_of_le`, `limsup_le_cycleTime_of_le`: the sub-solution bound. A
  nonnegative sequence with `c_{n+1} ≤ f(c_n)` satisfies `c_n ≤ fⁿ(c_0)` and grows at most at the
  cycle time; `MonotoneHomogeneous.le_iterate_of_dominated` applies it along a sequence of maps
  dominated by `f`.
-/

open Filter Topology

variable {ι : Type*}

/-- `f` maps the nonnegative orthant into itself and is monotone and positively homogeneous of
degree one there. -/
structure MonotoneHomogeneous (f : (ι → ℝ) → ι → ℝ) : Prop where
  map_nonneg {x : ι → ℝ} : 0 ≤ x → 0 ≤ f x
  monotone {x y : ι → ℝ} : 0 ≤ x → x ≤ y → f x ≤ f y
  map_smul {c : ℝ} {x : ι → ℝ} : 0 ≤ c → 0 ≤ x → f (c • x) = c • f x

/-- The **cycle time** of a self-map of `ι → ℝ`: the infimum of `‖fⁿ 𝟙‖^{1/n}` over `n ≥ 1`, for the
sup norm. For a monotone homogeneous `f` it is the limit of `‖fⁿ 𝟙‖^{1/n}`
(`MonotoneHomogeneous.tendsto_cycleTime`). -/
noncomputable def cycleTime [Fintype ι] (f : (ι → ℝ) → ι → ℝ) : ℝ :=
  sInf ((fun n : ℕ => ‖f^[n] 1‖ ^ (n : ℝ)⁻¹) '' Set.Ici 1)

namespace MonotoneHomogeneous

variable {f g : (ι → ℝ) → ι → ℝ}

/-! ### The class -/

protected lemma id : MonotoneHomogeneous (id : (ι → ℝ) → ι → ℝ) :=
  ⟨fun h => h, fun _ h => h, fun _ _ => rfl⟩

lemma comp (hg : MonotoneHomogeneous g) (hf : MonotoneHomogeneous f) :
    MonotoneHomogeneous (g ∘ f) where
  map_nonneg hx := hg.map_nonneg (hf.map_nonneg hx)
  monotone hx hxy := hg.monotone (hf.map_nonneg hx) (hf.monotone hx hxy)
  map_smul hc hx := by
    simp only [Function.comp_apply, hf.map_smul hc hx, hg.map_smul hc (hf.map_nonneg hx)]

lemma iterate (hf : MonotoneHomogeneous f) (n : ℕ) : MonotoneHomogeneous f^[n] := by
  induction n with
  | zero => exact MonotoneHomogeneous.id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact hf.comp ih

lemma map_zero (hf : MonotoneHomogeneous f) : f 0 = 0 := by
  have := hf.map_smul (c := 0) (x := 0) le_rfl le_rfl
  simpa using this

/-- `x ≤ c • y` passes through `f`. -/
lemma le_smul_of_le (hf : MonotoneHomogeneous f) {x y : ι → ℝ} {c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hy : 0 ≤ y) (h : x ≤ c • y) : f x ≤ c • f y := by
  rw [← hf.map_smul hc hy]
  exact hf.monotone hx h

/-- `c • y ≤ x` passes through `f`. -/
lemma smul_le_of_le (hf : MonotoneHomogeneous f) {x y : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hy : 0 ≤ y) (h : c • y ≤ x) : c • f y ≤ f x := by
  rw [← hf.map_smul hc hy]
  exact hf.monotone (smul_nonneg hc hy) h

/-- A nonnegative matrix is monotone homogeneous. -/
lemma mulVec [Fintype ι] {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    MonotoneHomogeneous A.mulVec where
  map_nonneg hx := Matrix.mulVec_nonneg hA hx
  monotone _ hxy := Matrix.mulVec_mono hA hxy
  map_smul _ _ := Matrix.mulVec_smul _ _ _

/-- The coordinatewise maximum of two monotone homogeneous maps is monotone homogeneous. -/
lemma sup (hf : MonotoneHomogeneous f) (hg : MonotoneHomogeneous g) :
    MonotoneHomogeneous (f ⊔ g) where
  map_nonneg hx := le_sup_of_le_left (hf.map_nonneg hx)
  monotone hx hxy := sup_le_sup (hf.monotone hx hxy) (hg.monotone hx hxy)
  map_smul hc hx := by
    ext i
    simp only [Pi.sup_apply, hf.map_smul hc hx, hg.map_smul hc hx, Pi.smul_apply, smul_eq_mul]
    exact (mul_max_of_nonneg _ _ hc).symm

/-- The coordinatewise minimum of two monotone homogeneous maps is monotone homogeneous. -/
lemma inf (hf : MonotoneHomogeneous f) (hg : MonotoneHomogeneous g) :
    MonotoneHomogeneous (f ⊓ g) where
  map_nonneg hx := le_inf (hf.map_nonneg hx) (hg.map_nonneg hx)
  monotone hx hxy := inf_le_inf (hf.monotone hx hxy) (hg.monotone hx hxy)
  map_smul hc hx := by
    ext i
    simp only [Pi.inf_apply, hf.map_smul hc hx, hg.map_smul hc hx, Pi.smul_apply, smul_eq_mul]
    exact (mul_min_of_nonneg _ _ hc).symm

/-! ### Submultiplicativity and the cycle time -/

variable [Fintype ι]

/-- A nonnegative vector is at most its sup norm times `𝟙`. -/
lemma le_norm_smul_one {x : ι → ℝ} (hx : 0 ≤ x) : x ≤ ‖x‖ • (1 : ι → ℝ) := fun i => by
  have := norm_le_pi_norm x i
  rw [Real.norm_of_nonneg (hx i)] at this
  simpa using this

lemma norm_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : ι → ℝ) : ‖c • x‖ = c * ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg hc]

/-- `‖f x‖ ≤ ‖x‖ ‖f 𝟙‖` for `x ≥ 0`. -/
lemma norm_apply_le (hf : MonotoneHomogeneous f) {x : ι → ℝ} (hx : 0 ≤ x) :
    ‖f x‖ ≤ ‖x‖ * ‖f 1‖ := by
  have h1 : f x ≤ ‖x‖ • f 1 :=
    hf.le_smul_of_le hx (norm_nonneg x) zero_le_one (le_norm_smul_one hx)
  have := Matrix.norm_le_norm_of_nonneg_of_le (hf.map_nonneg hx) h1
  rwa [norm_smul_of_nonneg (norm_nonneg x)] at this

/-- **Submultiplicativity of the orbit of `𝟙`.** `‖f^{m+n} 𝟙‖ ≤ ‖fᵐ 𝟙‖ ‖fⁿ 𝟙‖`. -/
theorem norm_iterate_add_le (hf : MonotoneHomogeneous f) (m n : ℕ) :
    ‖f^[m + n] 1‖ ≤ ‖f^[m] 1‖ * ‖f^[n] 1‖ := by
  rw [Function.iterate_add_apply, mul_comm]
  exact (hf.iterate m).norm_apply_le ((hf.iterate n).map_nonneg zero_le_one)

lemma submultiplicative (hf : MonotoneHomogeneous f) :
    Submultiplicative fun n : ℕ => ‖f^[n] 1‖ :=
  hf.norm_iterate_add_le

lemma cycleTime_eq_lim (hf : MonotoneHomogeneous f) : cycleTime f = hf.submultiplicative.lim :=
  rfl

/-- **The cycle time is the limit** of `‖fⁿ 𝟙‖^{1/n}` (Fekete). -/
theorem tendsto_cycleTime (hf : MonotoneHomogeneous f) :
    Tendsto (fun n : ℕ => ‖f^[n] 1‖ ^ (n : ℝ)⁻¹) atTop (𝓝 (cycleTime f)) := by
  rw [hf.cycleTime_eq_lim]
  exact hf.submultiplicative.tendsto_lim fun _ => norm_nonneg _

/-- Every `n ≥ 1` certifies the upper bound `R(f) ≤ ‖fⁿ 𝟙‖^{1/n}`. -/
theorem cycleTime_le (hf : MonotoneHomogeneous f) {n : ℕ} (hn : n ≠ 0) :
    cycleTime f ≤ ‖f^[n] 1‖ ^ (n : ℝ)⁻¹ := by
  rw [hf.cycleTime_eq_lim]
  exact hf.submultiplicative.lim_le_rpow (fun _ => norm_nonneg _) hn

lemma cycleTime_nonneg (hf : MonotoneHomogeneous f) : 0 ≤ cycleTime f :=
  ge_of_tendsto' hf.tendsto_cycleTime fun _ => Real.rpow_nonneg (norm_nonneg _) _

/-- `R(f)ⁿ ≤ ‖fⁿ 𝟙‖` for `n ≥ 1`. -/
theorem pow_cycleTime_le (hf : MonotoneHomogeneous f) {n : ℕ} (hn : n ≠ 0) :
    cycleTime f ^ n ≤ ‖f^[n] 1‖ := by
  have h := pow_le_pow_left₀ hf.cycleTime_nonneg (hf.cycleTime_le hn) n
  rwa [← Real.rpow_natCast (‖f^[n] 1‖ ^ (n : ℝ)⁻¹), ← Real.rpow_mul (norm_nonneg _),
    inv_mul_cancel₀ (by exact_mod_cast hn), Real.rpow_one] at h

/-! ### Other starts -/

/-- `‖fⁿ v‖ ≤ ‖v‖ ‖fⁿ 𝟙‖` for `v ≥ 0`. -/
lemma norm_iterate_le (hf : MonotoneHomogeneous f) {v : ι → ℝ} (hv : 0 ≤ v) (n : ℕ) :
    ‖f^[n] v‖ ≤ ‖v‖ * ‖f^[n] 1‖ :=
  (hf.iterate n).norm_apply_le hv

/-- **Start independence.** A start `u` with `c 𝟙 ≤ u ≤ C 𝟙`, `c > 0`, grows at the cycle time:
`‖fⁿ u‖^{1/n} → R(f)`. -/
theorem tendsto_cycleTime_of_bounds (hf : MonotoneHomogeneous f) {u : ι → ℝ} {c C : ℝ}
    (hc : 0 < c) (hlow : c • (1 : ι → ℝ) ≤ u) (hup : u ≤ C • (1 : ι → ℝ)) :
    Tendsto (fun n : ℕ => ‖f^[n] u‖ ^ (n : ℝ)⁻¹) atTop (𝓝 (cycleTime f)) := by
  have hu0 : 0 ≤ u := le_trans (smul_nonneg hc.le zero_le_one) hlow
  have hC : u ≤ max C 1 • (1 : ι → ℝ) :=
    hup.trans (smul_le_smul_of_nonneg_right (le_max_left _ _) zero_le_one)
  refine Real.tendsto_rpow_inv_of_bounds (H := fun n => ‖f^[n] 1‖) (C := max C 1) hc
    (lt_max_of_lt_right one_pos) (fun _ => norm_nonneg _) (Eventually.of_forall fun n => ?_)
    (Eventually.of_forall fun n => ?_) hf.tendsto_cycleTime
  · have h1 := (hf.iterate n).smul_le_of_le hc.le zero_le_one hlow
    have := Matrix.norm_le_norm_of_nonneg_of_le
      (smul_nonneg hc.le ((hf.iterate n).map_nonneg zero_le_one)) h1
    rwa [norm_smul_of_nonneg hc.le] at this
  · have h1 := (hf.iterate n).le_smul_of_le hu0 (le_trans zero_le_one (le_max_right C 1))
      zero_le_one hC
    have := Matrix.norm_le_norm_of_nonneg_of_le ((hf.iterate n).map_nonneg hu0) h1
    rwa [norm_smul_of_nonneg (le_trans zero_le_one (le_max_right C 1))] at this

/-- If a nonnegative sequence `a` satisfies `a n ≤ K ‖fⁿ 𝟙‖` for some `K`, then
`limsup a_n^{1/n} ≤ R(f)`. -/
theorem limsup_le_cycleTime_of_le_mul (hf : MonotoneHomogeneous f) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) {K : ℝ} (hK : ∀ n, a n ≤ K * ‖f^[n] 1‖) :
    limsup (fun n : ℕ => a n ^ (n : ℝ)⁻¹) atTop ≤ cycleTime f := by
  set K' := max K 1 with hK'
  have hK'0 : 0 < K' := lt_max_of_lt_right one_pos
  have hup : Tendsto (fun n : ℕ => K' ^ (n : ℝ)⁻¹ * ‖f^[n] 1‖ ^ (n : ℝ)⁻¹) atTop
      (𝓝 (cycleTime f)) := by
    simpa using (Real.tendsto_const_rpow_inv hK'0).mul hf.tendsto_cycleTime
  refine le_of_forall_gt_imp_ge_of_dense fun L hL => ?_
  have hev : ∀ᶠ n : ℕ in atTop, a n ^ (n : ℝ)⁻¹ ≤ L := by
    filter_upwards [hup.eventually (gt_mem_nhds hL)] with n hn
    refine le_trans ?_ hn.le
    rw [← Real.mul_rpow hK'0.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (ha n) ((hK n).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (norm_nonneg _))) (by positivity)
  exact limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop fun n => Real.rpow_nonneg (ha n) _) hev

/-- **Every nonnegative start grows at most at the cycle time.** -/
theorem limsup_le_cycleTime (hf : MonotoneHomogeneous f) {v : ι → ℝ} (hv : 0 ≤ v) :
    limsup (fun n : ℕ => ‖f^[n] v‖ ^ (n : ℝ)⁻¹) atTop ≤ cycleTime f :=
  hf.limsup_le_cycleTime_of_le_mul (fun _ => norm_nonneg _) (hf.norm_iterate_le hv)

/-! ### Domination -/

omit [Fintype ι] in
/-- **The sub-solution bound.** A nonnegative sequence with `c_{n+1} ≤ f(c_n)` satisfies
`c_n ≤ fⁿ(c_0)`. -/
theorem le_iterate_of_le (hf : MonotoneHomogeneous f) {c : ℕ → ι → ℝ} (hc : ∀ n, 0 ≤ c n)
    (hdom : ∀ n, c (n + 1) ≤ f (c n)) (n : ℕ) : c n ≤ f^[n] (c 0) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hdom n).trans (hf.monotone (hc n) ih)

/-- A nonnegative sub-solution `c_{n+1} ≤ f(c_n)` grows at most at the cycle time. -/
theorem limsup_le_cycleTime_of_le (hf : MonotoneHomogeneous f) {c : ℕ → ι → ℝ}
    (hc : ∀ n, 0 ≤ c n) (hdom : ∀ n, c (n + 1) ≤ f (c n)) :
    limsup (fun n : ℕ => ‖c n‖ ^ (n : ℝ)⁻¹) atTop ≤ cycleTime f :=
  hf.limsup_le_cycleTime_of_le_mul (fun _ => norm_nonneg _) fun n =>
    (Matrix.norm_le_norm_of_nonneg_of_le (hc n) (hf.le_iterate_of_le hc hdom n)).trans
      (hf.norm_iterate_le (hc 0) n)

omit [Fintype ι] in
/-- **Domination along a sequence of maps.** If maps `g k` are dominated by `f` on the orthant,
`g k x ≤ f x`, and preserve it, the trajectory `x_{k+1} = g k (x_k)` of a start `x_0 ≥ 0` is
dominated by the orbit of `f`: `x_n ≤ fⁿ x_0`. -/
theorem le_iterate_of_dominated (hf : MonotoneHomogeneous f) {g : ℕ → (ι → ℝ) → ι → ℝ}
    (hg0 : ∀ k x, 0 ≤ x → 0 ≤ g k x) (hgf : ∀ k x, 0 ≤ x → g k x ≤ f x) {x : ℕ → ι → ℝ}
    (hx0 : 0 ≤ x 0) (hx : ∀ k, x (k + 1) = g k (x k)) (n : ℕ) : x n ≤ f^[n] (x 0) := by
  have hnonneg : ∀ k, 0 ≤ x k := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih => rw [hx k]; exact hg0 k _ ih
  exact hf.le_iterate_of_le hnonneg (fun k => by rw [hx k]; exact hgf k _ (hnonneg k)) n

end MonotoneHomogeneous
