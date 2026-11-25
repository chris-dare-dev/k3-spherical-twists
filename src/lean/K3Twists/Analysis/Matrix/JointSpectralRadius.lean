/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.GelfandRadius
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Topology.Order.IntermediateValue

/-!
# The joint spectral radius

For a finite nonempty family `A : α → Matrix ι ι ℝ`, write `A_w = A_{w₁} ⋯ A_{wₙ}` for a word
`w : Fin n → α`. The joint spectral radius (Rota–Strang, *A note on the joint spectral radius*,
Indag. Math. 22 (1960)) is

  `JSR(A) = lim_n (max_{|w| = n} ‖A_w‖)^{1/n}`.

The limit exists by Fekete's lemma, because the word maxima are submultiplicative.

## Main definitions

* `Monoid.sphereMax T a n`: the maximum of `a` over the products of `n` letters of `T : α → M`,
  in any monoid `M`.
* `Matrix.jointSpectralRadius A`: the limit above, for the `ℓ∞` operator norm; equivalent norms
  give the same limit.

## Main results

* `Monoid.sphereMax_add_le`, `Monoid.exists_rate_sphereMax`: a quasi-submultiplicative function
  `a(gh) ≤ C a(g) a(h)` has submultiplicative word maxima, hence an exponential rate.
* `Matrix.tendsto_jointSpectralRadius`: the limit exists.
* `Matrix.jointSpectralRadius_le`: every length certifies an upper bound,
  `JSR ≤ (max_{|w| = k} ‖A_w‖)^{1/k}` for `k ≥ 1`; `Matrix.jointSpectralRadius_le_of_norm_le`
  and `Matrix.jointSpectralRadius_le_of_cone` give the upper bounds used below.
* `Matrix.gelfandRadius_rpow_le_jointSpectralRadius`: every nonempty word gives a lower bound,
  `gelfandRadius(A_w)^{1/|w|} ≤ JSR`.
* `Matrix.jointSpectralRadius_unipotent_pair`: for `s ≥ 1` the pair `[[1, s], [0, 1]]`,
  `[[1, 0], [s, 1]]` has joint spectral radius `ρ_s = (s + √(s² + 4))/2`, the larger root of
  `x² = s x + 1`. The lower bound is the word of length two; the upper bound is the cone norm
  `max(x + ρ_s y, ρ_s x + y)` on nonnegative vectors.
* `Matrix.exists_tribonacci_le_jointSpectralRadius_triangle`: for the triangle graph, the three
  letters `P_i = 1 + e_i G_{i*}` have joint spectral radius at least the tribonacci constant
  `τ ∈ (1.8, 1.9)`, `τ³ = τ² + τ + 1`: `P₁P₂P₃` has the eigenvector `(τ², τ, 1)` with eigenvalue
  `τ³`, and the Collatz–Wielandt bound applies.
-/

open Filter Topology

/-! ### Word maxima in a monoid -/

namespace Monoid

variable {M α : Type*} [Monoid M]

/-- Splitting a word of length `m + n` into its first `m` and last `n` letters. -/
lemma prod_ofFn_add (T : α → M) {m n : ℕ} (w : Fin (m + n) → α) :
    (List.ofFn (T ∘ w)).prod =
      (List.ofFn (T ∘ fun i : Fin m => w (i.castLE (Nat.le_add_right m n)))).prod *
        (List.ofFn (T ∘ fun i : Fin n => w (i.natAdd m))).prod := by
  rw [List.ofFn_add, List.prod_append]
  rfl

/-- The product along the `n`-fold repetition of a word is the `n`-th power of its product. -/
lemma prod_ofFn_repeat (T : α → M) {k : ℕ} (w : Fin k → α) (n : ℕ) :
    (List.ofFn (T ∘ Fin.repeat n w)).prod = (List.ofFn (T ∘ w)).prod ^ n := by
  change (List.ofFn (Fin.repeat n (T ∘ w))).prod = _
  rw [List.ofFn_fin_repeat, List.prod_flatten, List.map_replicate, List.prod_replicate]

variable [Fintype α] [Nonempty α]

/-- The maximum of `a` over the products of `n` letters of the alphabet `T`. -/
noncomputable def sphereMax (T : α → M) (a : M → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun w : Fin n → α => a (List.ofFn (T ∘ w)).prod

lemma le_sphereMax (T : α → M) (a : M → ℝ) {n : ℕ} (w : Fin n → α) :
    a (List.ofFn (T ∘ w)).prod ≤ sphereMax T a n :=
  Finset.le_sup' (fun w : Fin n → α => a (List.ofFn (T ∘ w)).prod) (Finset.mem_univ w)

lemma sphereMax_le (T : α → M) (a : M → ℝ) {n : ℕ} {r : ℝ}
    (h : ∀ w : Fin n → α, a (List.ofFn (T ∘ w)).prod ≤ r) : sphereMax T a n ≤ r :=
  Finset.sup'_le _ _ fun w _ => h w

lemma sphereMax_nonneg (T : α → M) {a : M → ℝ} (ha : ∀ g, 0 ≤ a g) (n : ℕ) :
    0 ≤ sphereMax T a n := by
  obtain ⟨w⟩ : Nonempty (Fin n → α) := inferInstance
  exact (ha _).trans (le_sphereMax T a w)

/-- **Quasi-submultiplicativity passes to word maxima.** -/
theorem sphereMax_add_le (T : α → M) (a : M → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ g, 0 ≤ a g)
    (hsub : ∀ g h, a (g * h) ≤ C * a g * a h) (m n : ℕ) :
    sphereMax T a (m + n) ≤ C * sphereMax T a m * sphereMax T a n := by
  refine sphereMax_le T a fun w => ?_
  rw [prod_ofFn_add]
  refine (hsub _ _).trans ?_
  have h1 := le_sphereMax T a fun i : Fin m => w (i.castLE (Nat.le_add_right m n))
  have h2 := le_sphereMax T a fun i : Fin n => w (i.natAdd m)
  have h0 := ha (List.ofFn (T ∘ fun i : Fin m => w (i.castLE (Nat.le_add_right m n)))).prod
  have h0' := ha (List.ofFn (T ∘ fun i : Fin n => w (i.natAdd m))).prod
  calc C * a _ * a _ ≤ C * sphereMax T a m * a _ := by gcongr
    _ ≤ _ := by
        gcongr
        exact mul_nonneg hC (h0.trans h1)

/-- **Fekete's lemma for word maxima.** A quasi-submultiplicative function `a ≥ 0` has word
maxima with an exponential rate `ρ`, and every length `k ≥ 1` certifies
`ρ ≤ (C max_{|w| = k} a(T_w))^{1/k}`. -/
theorem exists_rate_sphereMax (T : α → M) (a : M → ℝ) {C : ℝ} (hC : 0 < C) (ha : ∀ g, 0 ≤ a g)
    (hsub : ∀ g h, a (g * h) ≤ C * a g * a h) :
    ∃ ρ : ℝ, Tendsto (fun n : ℕ => sphereMax T a n ^ (n : ℝ)⁻¹) atTop (𝓝 ρ) ∧
      (∀ k : ℕ, k ≠ 0 → ρ ≤ (C * sphereMax T a k) ^ (k : ℝ)⁻¹) := by
  obtain ⟨ρ, h1, h2, -⟩ := Real.exists_rate_of_submul hC (sphereMax_nonneg T ha)
    (sphereMax_add_le T a hC.le ha hsub)
  exact ⟨ρ, h1, h2⟩

end Monoid

/-! ### The joint spectral radius of a family of real matrices -/

namespace Matrix

open scoped Matrix.Norms.Operator

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]

/-- The **joint spectral radius** of a finite nonempty family of real square matrices
(Rota–Strang, Indag. Math. 22 (1960)): the limit of `(max_{|w| = n} ‖A_w‖)^{1/n}` over the
products `A_w` of `n` matrices of the family, for the `ℓ∞` operator norm. The limit exists
(`Matrix.tendsto_jointSpectralRadius`). -/
noncomputable def jointSpectralRadius (A : α → Matrix ι ι ℝ) : ℝ :=
  limUnder atTop fun n : ℕ => Monoid.sphereMax A (‖·‖) n ^ (n : ℝ)⁻¹

lemma exists_rate_sphereMax_norm (A : α → Matrix ι ι ℝ) :
    ∃ ρ : ℝ, Tendsto (fun n : ℕ => Monoid.sphereMax A (‖·‖) n ^ (n : ℝ)⁻¹) atTop (𝓝 ρ) ∧
      (∀ k : ℕ, k ≠ 0 → ρ ≤ (1 * Monoid.sphereMax A (‖·‖) k) ^ (k : ℝ)⁻¹) :=
  Monoid.exists_rate_sphereMax A (‖·‖) one_pos (fun _ => norm_nonneg _)
    (fun g h => by rw [one_mul]; exact norm_mul_le g h)

/-- The word maxima `(max_{|w| = n} ‖A_w‖)^{1/n}` converge to the joint spectral radius. -/
theorem tendsto_jointSpectralRadius (A : α → Matrix ι ι ℝ) :
    Tendsto (fun n : ℕ => Monoid.sphereMax A (‖·‖) n ^ (n : ℝ)⁻¹) atTop
      (𝓝 (jointSpectralRadius A)) := by
  obtain ⟨ρ, h, -⟩ := exists_rate_sphereMax_norm A
  exact tendsto_nhds_limUnder ⟨ρ, h⟩

theorem jointSpectralRadius_nonneg (A : α → Matrix ι ι ℝ) : 0 ≤ jointSpectralRadius A :=
  ge_of_tendsto' (tendsto_jointSpectralRadius A) fun n =>
    Real.rpow_nonneg (Monoid.sphereMax_nonneg A (fun _ => norm_nonneg _) n) _

/-- **Upper certificates.** Every length `k ≥ 1` bounds the joint spectral radius:
`JSR ≤ (max_{|w| = k} ‖A_w‖)^{1/k}`. -/
theorem jointSpectralRadius_le (A : α → Matrix ι ι ℝ) {k : ℕ} (hk : k ≠ 0) :
    jointSpectralRadius A ≤ Monoid.sphereMax A (‖·‖) k ^ (k : ℝ)⁻¹ := by
  obtain ⟨ρ, h, h2⟩ := exists_rate_sphereMax_norm A
  rw [tendsto_nhds_unique (tendsto_jointSpectralRadius A) h]
  simpa using h2 k hk

/-- If every product of `n` matrices of the family has norm at most `C rⁿ`, with `r ≥ 0`, then
`JSR ≤ r`. -/
theorem jointSpectralRadius_le_of_norm_le (A : α → Matrix ι ι ℝ) {C r : ℝ} (hr : 0 ≤ r)
    (h : ∀ (n : ℕ) (w : Fin n → α), ‖(List.ofFn (A ∘ w)).prod‖ ≤ C * r ^ n) :
    jointSpectralRadius A ≤ r := by
  have hC : 0 < max C 1 := lt_max_of_lt_right one_pos
  have hmax : ∀ n, Monoid.sphereMax A (‖·‖) n ≤ max C 1 * r ^ n := fun n =>
    Monoid.sphereMax_le A _ fun w =>
      (h n w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr n))
  have hlim : Tendsto (fun n : ℕ => max C 1 ^ (n : ℝ)⁻¹ * r) atTop (𝓝 r) := by
    simpa using (Real.tendsto_const_rpow_inv hC).mul_const r
  refine le_of_tendsto_of_tendsto (tendsto_jointSpectralRadius A) hlim ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  calc Monoid.sphereMax A (‖·‖) n ^ (n : ℝ)⁻¹ ≤ (max C 1 * r ^ n) ^ (n : ℝ)⁻¹ :=
        Real.rpow_le_rpow (Monoid.sphereMax_nonneg A (fun _ => norm_nonneg _) n) (hmax n)
          (by positivity)
    _ = max C 1 ^ (n : ℝ)⁻¹ * r := by
        rw [Real.mul_rpow hC.le (pow_nonneg hr n), Real.pow_rpow_inv_natCast hr hn]

/-- **Lower bound by one word.** For a word `w` of length `k ≥ 1`,
`gelfandRadius(A_w)^{1/k} ≤ JSR`: the powers `A_wⁿ` are products of `nk` letters. -/
theorem gelfandRadius_rpow_le_jointSpectralRadius (A : α → Matrix ι ι ℝ) {k : ℕ} (hk : k ≠ 0)
    (w : Fin k → α) :
    gelfandRadius (List.ofFn (A ∘ w)).prod ^ (k : ℝ)⁻¹ ≤ jointSpectralRadius A := by
  set P := (List.ofFn (A ∘ w)).prod
  have h1 : ∀ n : ℕ, ‖P ^ n‖ ≤ Monoid.sphereMax A (‖·‖) (n * k) := fun n => by
    rw [← Monoid.prod_ofFn_repeat A w n]
    exact Monoid.le_sphereMax A (‖·‖) (Fin.repeat n w)
  have hsub : Tendsto (fun n : ℕ => Monoid.sphereMax A (‖·‖) (n * k) ^ ((n * k : ℕ) : ℝ)⁻¹)
      atTop (𝓝 (jointSpectralRadius A)) :=
    (tendsto_jointSpectralRadius A).comp
      (tendsto_id.atTop_mul_const' (Nat.pos_of_ne_zero hk))
  have hlhs : Tendsto (fun n : ℕ => ‖P ^ n‖ ^ ((n * k : ℕ) : ℝ)⁻¹) atTop
      (𝓝 (gelfandRadius P ^ (k : ℝ)⁻¹)) := by
    refine ((tendsto_gelfandRadius P).rpow_const (Or.inr (by positivity))).congr fun n => ?_
    rw [← Real.rpow_mul (norm_nonneg _), Nat.cast_mul, mul_inv]
  refine le_of_tendsto_of_tendsto hlhs hsub (Eventually.of_forall fun n => ?_)
  exact Real.rpow_le_rpow (norm_nonneg _) (h1 n) (by positivity)

/-- **Upper certificate from a cone norm.** Let the family consist of matrices with
nonnegative entries, and let `f` be a function on nonnegative vectors with
`‖v‖ ≤ f v ≤ C ‖v‖` and `f (A_a v) ≤ ρ f v` for every letter `a`. Then `JSR ≤ ρ`. -/
theorem jointSpectralRadius_le_of_cone {A : α → Matrix ι ι ℝ} (hA : ∀ a i j, 0 ≤ A a i j)
    (f : (ι → ℝ) → ℝ) {C ρ : ℝ} (hρ : 0 ≤ ρ) (hlo : ∀ v, 0 ≤ v → ‖v‖ ≤ f v)
    (hhi : ∀ v, 0 ≤ v → f v ≤ C * ‖v‖) (hf : ∀ a v, 0 ≤ v → f (A a *ᵥ v) ≤ ρ * f v) :
    jointSpectralRadius A ≤ ρ := by
  have hword : ∀ (l : List α) (v : ι → ℝ), 0 ≤ v →
      0 ≤ (l.map A).prod *ᵥ v ∧ f ((l.map A).prod *ᵥ v) ≤ ρ ^ l.length * f v := by
    intro l
    induction l with
    | nil => intro v hv; simpa using hv
    | cons a l ih =>
      intro v hv
      obtain ⟨h0, h1⟩ := ih v hv
      rw [List.map_cons, List.prod_cons, ← mulVec_mulVec, List.length_cons, pow_succ']
      refine ⟨mulVec_nonneg (hA a) h0, (hf a _ h0).trans ?_⟩
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 hρ
  refine jointSpectralRadius_le_of_norm_le A (C := C * ‖(1 : ι → ℝ)‖) hρ fun n w => ?_
  have hP : ∀ i j, 0 ≤ (List.ofFn (A ∘ w)).prod i j :=
    list_prod_apply_nonneg _ fun B hB i j => by
      obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ B).1 hB
      exact hA _ i j
  have h1 : (0 : ι → ℝ) ≤ 1 := fun _ => zero_le_one
  obtain ⟨-, hw⟩ := hword (List.ofFn w) 1 h1
  rw [List.map_ofFn, List.length_ofFn] at hw
  have hP1 := mul_norm_le_norm_mulVec hP one_pos fun _ => le_rfl
  rw [one_mul] at hP1
  calc ‖(List.ofFn (A ∘ w)).prod‖ ≤ ‖(List.ofFn (A ∘ w)).prod *ᵥ 1‖ := hP1
    _ ≤ f ((List.ofFn (A ∘ w)).prod *ᵥ 1) := hlo _ (mulVec_nonneg hP h1)
    _ ≤ ρ ^ n * f 1 := hw
    _ ≤ ρ ^ n * (C * ‖(1 : ι → ℝ)‖) := mul_le_mul_of_nonneg_left (hhi 1 h1) (pow_nonneg hρ n)
    _ = C * ‖(1 : ι → ℝ)‖ * ρ ^ n := mul_comm _ _

/-! ### Two unipotent matrices -/

/-- **The joint spectral radius of a pair of unipotent matrices.** For `s ≥ 1`,
`JSR([[1, s], [0, 1]], [[1, 0], [s, 1]]) = ρ_s = (s + √(s² + 4))/2`, the larger root of
`x² = s x + 1`. The product of the two letters has determinant one and trace `2 + s²`, hence
Gelfand radius `ρ_s²`; on nonnegative vectors `f(x, y) = max(x + ρ_s y, ρ_s x + y)` satisfies
`f(Av) ≤ ρ_s f(v)` and `f(Bv) ≤ ρ_s f(v)`, which uses `(s - 1)(ρ_s - 1) ≥ 0`. At `s = 1` this is
the golden ratio. -/
theorem jointSpectralRadius_unipotent_pair {s : ℝ} (hs : 1 ≤ s) :
    jointSpectralRadius ![!![1, s; 0, 1], !![1, 0; s, 1]] = (s + √(s ^ 2 + 4)) / 2 := by
  set ρ := (s + √(s ^ 2 + 4)) / 2 with hρdef
  have hsq : √(s ^ 2 + 4) ^ 2 = s ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have h2 : 2 ≤ √(s ^ 2 + 4) := by
    rw [show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hρ1 : 1 < ρ := by rw [hρdef]; linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hρsq : ρ ^ 2 = s * ρ + 1 := by rw [hρdef]; nlinarith [hsq]
  apply le_antisymm
  · -- the cone norm `max(x + ρ y, ρ x + y)`
    refine jointSpectralRadius_le_of_cone (C := 1 + ρ) ?_
      (fun v => max (v 0 + ρ * v 1) (ρ * v 0 + v 1)) hρ0 ?_ ?_ ?_
    · intro a i j
      fin_cases a <;> fin_cases i <;> fin_cases j <;> simp <;> linarith
    · intro v hv
      have h0 : 0 ≤ v 0 := hv 0
      have h1 : 0 ≤ v 1 := hv 1
      refine (pi_norm_le_iff_of_nonneg
        (le_max_of_le_left (add_nonneg h0 (mul_nonneg hρ0 h1)))).2 fun i => ?_
      rw [Real.norm_of_nonneg (hv i)]
      fin_cases i
      · exact le_max_of_le_left (by simp only [Fin.zero_eta]; nlinarith)
      · exact le_max_of_le_right (by simp only [Fin.mk_one]; nlinarith)
    · intro v hv
      have h0 : 0 ≤ v 0 := hv 0
      have h1 : 0 ≤ v 1 := hv 1
      have n0 : v 0 ≤ ‖v‖ := (le_abs_self _).trans (by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v 0)
      have n1 : v 1 ≤ ‖v‖ := (le_abs_self _).trans (by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v 1)
      refine max_le ?_ ?_ <;> nlinarith
    · intro a v hv
      have h0 : 0 ≤ v 0 := hv 0
      have h1 : 0 ≤ v 1 := hv 1
      have hρs : 0 ≤ (s - 1) * (ρ - 1) := mul_nonneg (by linarith) (by linarith)
      fin_cases a
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Matrix.empty_val']
        refine max_le ?_ ?_
        · refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_left _ _) hρ0)
          have e : ρ * (v 0 + ρ * v 1) - (1 * v 0 + s * v 1 + ρ * (0 * v 0 + 1 * v 1)) =
              (ρ - 1) * v 0 + (s - 1) * (ρ - 1) * v 1 := by linear_combination v 1 * hρsq
          nlinarith [mul_nonneg (by linarith : 0 ≤ ρ - 1) h0, mul_nonneg hρs h1]
        · refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (le_max_left _ _) hρ0)
          linear_combination (-v 1) * hρsq
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, mulVec, dotProduct,
          Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
          Matrix.empty_val']
        refine max_le ?_ ?_
        · refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (le_max_right _ _) hρ0)
          linear_combination (-v 0) * hρsq
        · refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_right _ _) hρ0)
          have e : ρ * (ρ * v 0 + v 1) - (ρ * (1 * v 0 + 0 * v 1) + (s * v 0 + 1 * v 1)) =
              (s - 1) * (ρ - 1) * v 0 + (ρ - 1) * v 1 := by linear_combination v 0 * hρsq
          nlinarith [mul_nonneg (by linarith : 0 ≤ ρ - 1) h1, mul_nonneg hρs h0]
  · -- the word `AB`
    have hAB : (List.ofFn (![!![1, s; 0, 1], !![1, 0; s, 1]] ∘ ![0, 1])).prod =
        thurstonA s 1 * thurstonB s 1 := by
      simp [List.ofFn_succ, thurstonA, thurstonB]
    have hl : 1 < ρ ^ 2 := by nlinarith
    have hρinv : (ρ ^ 2)⁻¹ = (ρ - s) ^ 2 := by
      rw [← inv_pow]
      congr 1
      apply inv_eq_of_mul_eq_one_right
      linear_combination hρsq
    have hgr : gelfandRadius (thurstonA s 1 * thurstonB s 1) = ρ ^ 2 :=
      gelfandRadius_thurston hl (by rw [hρinv]; linear_combination 2 * hρsq)
    have := gelfandRadius_rpow_le_jointSpectralRadius
      ![!![1, s; 0, 1], !![1, 0; s, 1]] two_ne_zero ![0, 1]
    rwa [hAB, hgr, Nat.cast_ofNat, ← Nat.cast_ofNat (R := ℝ) (n := 2),
      Real.pow_rpow_inv_natCast hρ0 two_ne_zero] at this

/-! ### The triangle -/

/-- **A lower bound for the triangle.** Let `G` be the adjacency matrix of the triangle and
`P_i = 1 + e_i G_{i*}` (the identity with `G_{i*}` added to row `i`). Every real `τ` with
`τ³ = τ² + τ + 1` is at most the joint spectral radius of `P₁, P₂, P₃`: the product
`P₁P₂P₃ = [[4, 3, 2], [2, 2, 1], [1, 1, 1]]` has the eigenvector `(τ², τ, 1)` with eigenvalue
`τ³`, so its Gelfand radius is at least `τ³` (Collatz–Wielandt). -/
theorem le_jointSpectralRadius_triangle {τ : ℝ} (h : τ ^ 3 = τ ^ 2 + τ + 1) :
    τ ≤ jointSpectralRadius ![!![1, 1, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 1, 1; 0, 0, 1],
      !![1, 0, 0; 0, 1, 0; 1, 1, 1]] := by
  set P : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ := ![!![1, 1, 1; 0, 1, 0; 0, 0, 1],
    !![1, 0, 0; 1, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 1, 1, 1]] with hP
  have hτ : 0 < τ := by nlinarith [sq_nonneg (τ + 1 / 2), sq_nonneg τ]
  set M := (List.ofFn (P ∘ ![0, 1, 2])).prod with hM
  have hMv : M *ᵥ ![τ ^ 2, τ, 1] = τ ^ 3 • ![τ ^ 2, τ, 1] := by
    funext i
    fin_cases i <;>
      simp [hM, hP, List.ofFn_succ, mulVec, dotProduct, Fin.sum_univ_three]
    · linear_combination -(τ ^ 2 + τ + 2) * h
    · linear_combination -(τ + 1) * h
    · linear_combination -h
  have hM0 : ∀ i j, 0 ≤ M i j :=
    list_prod_apply_nonneg _ fun B hB i j => by
      obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ B).1 hB
      simp only [Function.comp_apply]
      fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [hP]
  have hv0 : (0 : Fin 3 → ℝ) ≤ ![τ ^ 2, τ, 1] := by
    intro i
    fin_cases i <;> simp <;> positivity
  have hv : (![τ ^ 2, τ, 1] : Fin 3 → ℝ) ≠ 0 := fun h0 => by
    have := congrFun h0 2
    simp at this
  have hgr : τ ^ 3 ≤ gelfandRadius M :=
    le_gelfandRadius_of_smul_le_mulVec hM0 hv0 hv hMv.ge
  have hw := gelfandRadius_rpow_le_jointSpectralRadius P three_ne_zero ![0, 1, 2]
  refine le_trans ?_ hw
  calc τ = (τ ^ 3) ^ ((3 : ℕ) : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast hτ.le three_ne_zero).symm
    _ ≤ gelfandRadius M ^ ((3 : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow (by positivity) hgr (by positivity)

/-- The tribonacci constant: `x³ = x² + x + 1` has a root in `(1.8, 1.9)`. -/
theorem exists_tribonacci : ∃ τ : ℝ, 1.8 < τ ∧ τ < 1.9 ∧ τ ^ 3 = τ ^ 2 + τ + 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - x - 1) (Set.Icc 1.8 1.9) := by
    fun_prop
  obtain ⟨τ, ⟨h1, h2⟩, hτ⟩ :=
    intermediate_value_Ioo (by norm_num) hcont (show (0 : ℝ) ∈ Set.Ioo _ _ by norm_num)
  exact ⟨τ, h1, h2, by linarith⟩

/-- **The triangle has joint spectral radius at least the tribonacci constant**
`τ ∈ (1.8, 1.9)`, `τ³ = τ² + τ + 1`. -/
theorem exists_tribonacci_le_jointSpectralRadius_triangle :
    ∃ τ : ℝ, 1.8 < τ ∧ τ < 1.9 ∧ τ ^ 3 = τ ^ 2 + τ + 1 ∧
      τ ≤ jointSpectralRadius ![!![1, 1, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 1, 1; 0, 0, 1],
        !![1, 0, 0; 0, 1, 0; 1, 1, 1]] := by
  obtain ⟨τ, h1, h2, h⟩ := exists_tribonacci
  exact ⟨τ, h1, h2, h, le_jointSpectralRadius_triangle h⟩

end Matrix
