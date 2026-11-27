/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import K3Twists.Topology.Order.Selection
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Mass.Directional

/-!
# Radial limits of the mass at a finite period

Let `Z_*` be a positive period of a K3 surface, possibly on root hyperplanes, `R_*` the roots it
kills, and `σ_a` (`0 < a ≤ a₀`) a lift to the space of stability conditions of the straight ray
`Z_a = Z_* + aV`. For a fixed object `E`, at every point of the ray the mass is a sum
`Σ_γ n_γ |Z_a(γ)|` over the classes of the stable factors of the HN factors of `E` (the stable
factors of a semistable object have charges on its ray), and on each compact segment `[b, a₀]`,
`0 < b`, of the lifted ray only finitely many such sums occur: the objects whose mass at some point
of a compact set is at most that of `E` have finitely many classes (Bridgeland, arXiv:math/0307164,
Lemma 9.2 and the proof of Proposition 9.3). The ray `(0, a₀]` itself need not lie in a compact
set, and the proofs use only the segments. The charge of a stable
class `γ` either vanishes at `Z_*` (`γ ∈ R_*`, and then `|Z_a(γ)| = a |V(γ)|` increases with `a`)
or satisfies
`|V(γ)| ≤ L |Z_a(γ)|`, with `L = K ‖V‖` for the constant `K` of the punctured support bound
`‖v‖ ≤ K |Z(v)|` (`Mukai.exists_punctured_supportBound`, for the classes with `v² ≥ -2` outside
`R_*`; stable classes have `v² ≥ -2`).

From these inputs (`RadialRayHypotheses`), `a ↦ e^{La} m_a(E)` is nondecreasing on `(0, a₀]`
(`RadialRayHypotheses.monotoneOn_exp_mul_mass`). Each candidate sum is, by a derivative computation
for the classes outside `R_*` (`monotoneOn_exp_mul_norm_add_mul`) and directly for those in `R_*`,
and the selection lemma `monotoneOn_of_continuousOn_of_selection` transfers this to the continuous
mass, whatever the order in which the candidates are selected. So the **radial limit**
`m_*(E) = lim_{a → 0+} m_a(E)` exists (`RadialRayHypotheses.tendsto_radialMass`) and
`m_*(E) ≤ e^{La} m_a(E)` (`RadialRayHypotheses.radialMass_le`). It depends a priori on the
direction `V` and on the lift. No analyticity of the path is used.

If moreover a root class `γ` has, at every point of the ray, a representative in a set `𝒮` (the
spherical objects) that is semistable there (Kikuta–Koseki–Ouchi, arXiv:2504.12253, Lemma 3.4,
in every Picard rank), then the class infimum of the radial limit is the modulus of the limiting
period: `d_{m_*}(γ) = |Z_*(γ)|` (`RadialRayHypotheses.classInf_radialProfile`). The lower bound
passes to the limit from `m_a ≥ |Z_a|`; the upper bound evaluates `m_* ≤ e^{La} m_a` on the
semistable representatives at each `a`, which may vary with `a`.

## Real objects

Mathlib has no triangulated category carrying a slicing, so no field has an instance from geometry:
the missing input is the derived category of a K3 surface with its space of stability conditions.
`K3TwistsTest/RadialLimitModel.lean` checks that the fields can hold together, on the constant
ray at one prestability condition.

## Main definitions

* `RadialRayHypotheses C v`: a lifted ray `σ_a`, `0 < a ≤ a₀`, with charges `Z_* + aV`, continuous
  masses and finitely many candidate sums on each compact segment `[b, a₀]`.
* `RadialRayHypotheses.radialMass`, `RadialRayHypotheses.radialProfile`: the radial limit `m_*`.

## Main results

* `monotoneOn_exp_mul_norm_add_mul`: if `‖z‖ ≤ L ‖w + a z‖` on an interval, `e^{La} ‖w + a z‖` is
  monotone there.
* `monotoneOn_exp_mul_finsuppSum`: the same for the sums `Σ n_γ |Z_* (γ) + a V(γ)|`.
* `RadialRayHypotheses.monotoneOn_exp_mul_mass`, `RadialRayHypotheses.tendsto_radialMass`,
  `RadialRayHypotheses.radialMass_le`: the one-sided bound and the radial limit.
* `RadialRayHypotheses.classInf_radialProfile`: `d_{m_*} = |Z_*|` on root classes with semistable
  spherical representatives along the ray.
-/

noncomputable section

open Filter Topology Set Real

/-! ### Charges along a ray -/

/-- **A charge moving along a ray.** If `‖z‖ ≤ L ‖w + a z‖` on an interval `s`, then
`a ↦ e^{La} ‖w + a z‖` is monotone on `s`. The square `e^{2La} ‖w + az‖²` has derivative
`2 e^{2La} (L ‖w + az‖² + Re(z̄ (w + az))) ≥ 0`. -/
theorem monotoneOn_exp_mul_norm_add_mul {w z : ℂ} {L : ℝ} {s : Set ℝ} (hs : s.OrdConnected)
    (h : ∀ a ∈ s, ‖z‖ ≤ L * ‖w + a * z‖) :
    MonotoneOn (fun a : ℝ ↦ exp (L * a) * ‖w + a * z‖) s := by
  set P : ℝ → ℝ := fun a ↦ (w.re + a * z.re) ^ 2 + (w.im + a * z.im) ^ 2 with hP
  have hnorm : ∀ a : ℝ, ‖w + a * z‖ = √(P a) := fun a ↦ by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp [P]
  set g : ℝ → ℝ := fun a ↦ exp (2 * L * a) * P a with hg
  have hP0 : ∀ a, 0 ≤ P a := fun a ↦ by positivity
  have hsq : ∀ a, exp (L * a) * ‖w + a * z‖ = √(g a) := fun a ↦ by
    have hga : g a = exp (L * a) ^ 2 * P a := by
      simp only [hg, sq, ← Real.exp_add]
      ring_nf
    rw [hnorm, hga, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (exp_pos _).le]
  have hderiv : ∀ a, HasDerivAt g (exp (2 * L * a) *
      (2 * L * P a + (2 * (w.re + a * z.re) * z.re + 2 * (w.im + a * z.im) * z.im))) a := by
    intro a
    have h1 : HasDerivAt (fun a ↦ exp (2 * L * a)) (exp (2 * L * a) * (2 * L)) a := by
      have := ((hasDerivAt_id a).const_mul (2 * L)).exp
      simpa using this
    have hx : HasDerivAt (fun a : ℝ ↦ w.re + a * z.re) z.re a := by
      simpa using ((hasDerivAt_id a).mul_const z.re).const_add w.re
    have hy : HasDerivAt (fun a : ℝ ↦ w.im + a * z.im) z.im a := by
      simpa using ((hasDerivAt_id a).mul_const z.im).const_add w.im
    have h2 : HasDerivAt P (2 * (w.re + a * z.re) * z.re + 2 * (w.im + a * z.im) * z.im) a := by
      convert (hx.pow 2).add (hy.pow 2) using 1
      simp only [Nat.cast_ofNat]
      ring
    convert h1.mul h2 using 1
    ring
  have hmono : MonotoneOn g s := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg hs.convex
      (fun a _ ↦ (hderiv a).continuousAt.continuousWithinAt)
      (fun a _ ↦ (hderiv a).hasDerivWithinAt) fun a ha ↦ ?_
    have ha' : a ∈ s := interior_subset ha
    refine mul_nonneg (exp_pos _).le ?_
    set x := w.re + a * z.re
    set y := w.im + a * z.im
    have hPa : P a = x ^ 2 + y ^ 2 := rfl
    have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    -- Cauchy–Schwarz in the plane: `|x Re z + y Im z| ≤ √P ‖z‖ ≤ L P`
    have hcs : (x * z.re + y * z.im) ^ 2 ≤ (√(P a) * ‖z‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hP0 a), hz, hPa]
      nlinarith [sq_nonneg (x * z.im - y * z.re)]
    have habs : |x * z.re + y * z.im| ≤ √(P a) * ‖z‖ :=
      abs_le_of_sq_le_sq' hcs (by positivity) |>.elim (fun h1 h2 ↦ abs_le.2 ⟨h1, h2⟩)
    have hL : √(P a) * ‖z‖ ≤ L * P a := by
      have := mul_le_mul_of_nonneg_left (h a ha') (Real.sqrt_nonneg (P a))
      rw [hnorm] at this
      calc √(P a) * ‖z‖ ≤ √(P a) * (L * √(P a)) := this
        _ = L * P a := by rw [mul_left_comm, Real.mul_self_sqrt (hP0 a)]
    have := (abs_le.1 (habs.trans hL)).1
    linarith
  intro a ha b hb hab
  simp only [hsq]
  exact Real.sqrt_le_sqrt (hmono ha hb hab)

/-- **A charge moving along a path.** Let `f : ℝ → ℂ` have derivative `f'` and `Λ` derivative `λ`
on an interval `s`, with `‖f'(t)‖ ≤ λ(t) ‖f(t)‖`. Then `t ↦ e^{Λ(t)} ‖f(t)‖` is monotone and
`t ↦ e^{-Λ(t)} ‖f(t)‖` is antitone on `s`. -/
theorem monotoneOn_exp_mul_norm_of_hasDerivAt {f f' : ℝ → ℂ} {Λ lam : ℝ → ℝ} {s : Set ℝ}
    (hs : s.OrdConnected) (hf : ∀ t ∈ s, HasDerivAt f (f' t) t)
    (hΛ : ∀ t ∈ s, HasDerivAt Λ (lam t) t) (h : ∀ t ∈ s, ‖f' t‖ ≤ lam t * ‖f t‖) :
    MonotoneOn (fun t ↦ exp (Λ t) * ‖f t‖) s ∧ AntitoneOn (fun t ↦ exp (-Λ t) * ‖f t‖) s := by
  set P : ℝ → ℝ := fun t ↦ (f t).re ^ 2 + (f t).im ^ 2 with hP
  have hnorm : ∀ t, ‖f t‖ = √(P t) := fun t ↦ Complex.norm_eq_sqrt_sq_add_sq _
  have hP0 : ∀ t, 0 ≤ P t := fun t ↦ by positivity
  have hre : ∀ t ∈ s, HasDerivAt (fun t ↦ (f t).re) (f' t).re t := fun t ht ↦
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht)
  have him : ∀ t ∈ s, HasDerivAt (fun t ↦ (f t).im) (f' t).im t := fun t ht ↦
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht)
  have hPd : ∀ t ∈ s, HasDerivAt P (2 * (f t).re * (f' t).re + 2 * (f t).im * (f' t).im) t :=
    fun t ht ↦ by
      convert ((hre t ht).pow 2).add ((him t ht).pow 2) using 1
      simp only [Nat.cast_ofNat]
      ring
  -- Cauchy–Schwarz: `|Re f Re f' + Im f Im f'| ≤ λ P`
  have hcs : ∀ t ∈ s, |(f t).re * (f' t).re + (f t).im * (f' t).im| ≤ lam t * P t := fun t ht ↦ by
    have h1 : ((f t).re * (f' t).re + (f t).im * (f' t).im) ^ 2 ≤ (√(P t) * ‖f' t‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hP0 t), Complex.sq_norm, Complex.normSq_apply]
      nlinarith [sq_nonneg ((f t).re * (f' t).im - (f t).im * (f' t).re)]
    have h2 : |(f t).re * (f' t).re + (f t).im * (f' t).im| ≤ √(P t) * ‖f' t‖ :=
      abs_le_of_sq_le_sq' h1 (by positivity) |>.elim (fun a b ↦ abs_le.2 ⟨a, b⟩)
    have h3 := mul_le_mul_of_nonneg_left (h t ht) (Real.sqrt_nonneg (P t))
    rw [hnorm] at h3
    calc _ ≤ √(P t) * ‖f' t‖ := h2
      _ ≤ √(P t) * (lam t * √(P t)) := h3
      _ = lam t * P t := by rw [mul_left_comm, Real.mul_self_sqrt (hP0 t)]
  have hconv : Convex ℝ s := hs.convex
  have hsq : ∀ (c : ℝ) t, exp (c * Λ t) * ‖f t‖ = √(exp (2 * c * Λ t) * P t) := fun c t ↦ by
    have : exp (2 * c * Λ t) = exp (c * Λ t) ^ 2 := by rw [sq, ← Real.exp_add]; ring_nf
    rw [hnorm, this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (exp_pos _).le]
  have hgd : ∀ c : ℝ, ∀ t ∈ s, HasDerivAt (fun t ↦ exp (2 * c * Λ t) * P t)
      (exp (2 * c * Λ t) * (2 * c * lam t * P t +
        (2 * (f t).re * (f' t).re + 2 * (f t).im * (f' t).im))) t := fun c t ht ↦ by
    have h1 := ((hΛ t ht).const_mul (2 * c)).exp
    convert h1.mul (hPd t ht) using 1
    ring
  have hcont : ∀ c : ℝ, ContinuousOn (fun t ↦ exp (2 * c * Λ t) * P t) s := fun c t ht ↦
    (hgd c t ht).continuousAt.continuousWithinAt
  constructor
  · have hm : MonotoneOn (fun t ↦ exp (2 * 1 * Λ t) * P t) s :=
      monotoneOn_of_hasDerivWithinAt_nonneg hconv (hcont 1)
        (fun t ht ↦ (hgd 1 t (interior_subset ht)).hasDerivWithinAt) fun t ht ↦ by
          have := (abs_le.1 (hcs t (interior_subset ht))).1
          refine mul_nonneg (exp_pos _).le ?_
          linarith
    intro a ha b hb hab
    have := Real.sqrt_le_sqrt (hm ha hb hab)
    simpa only [← hsq, one_mul] using this
  · have ha : AntitoneOn (fun t ↦ exp (2 * (-1) * Λ t) * P t) s :=
      antitoneOn_of_hasDerivWithinAt_nonpos hconv (hcont (-1))
        (fun t ht ↦ (hgd (-1) t (interior_subset ht)).hasDerivWithinAt) fun t ht ↦ by
          have := (abs_le.1 (hcs t (interior_subset ht))).2
          refine mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le ?_
          linarith
    intro a ha' b hb hab
    have := Real.sqrt_le_sqrt (ha ha' hb hab)
    simpa only [← hsq, neg_one_mul] using this

/-- **The variation estimate along a path.** Let the positive continuous function `m` on an interval
`s` be at every point one of finitely many sums `Σ_γ n_j(γ) ‖f_γ(t)‖`, where every `f_γ` that occurs
has `‖f_γ'‖ ≤ λ ‖f_γ‖` and `Λ' = λ` on `s`. Then `|log m(t) - log m(u)| ≤ Λ(t) - Λ(u)` for `u ≤ t`
in `s`. For the mass of an object along a lifted `C¹` path of stability conditions, take
`f_γ(t) = |Z_t(γ)|`, real-valued with the norm of `Z_t(γ)`, over the classes of its stable factors,
and `λ = max(K ‖Ż‖, max_δ |d/dt log |Z_t(δ)||)` over the kernel roots `δ`. At a kernel root
`|f_δ'| = |d/dt log |Z_t(δ)|| · |Z_t(δ)|`; for the other classes
`|d/dt |Z_t(γ)|| ≤ |Ż_t(γ)| ≤ ‖Ż‖ ‖γ‖ ≤ K ‖Ż‖ |Z_t(γ)|` by the punctured support bound. The choice
`f_γ = Z_t(γ)` would need `|Ż_t(δ)| / |Z_t(δ)|` in place of `|d/dt log |Z_t(δ)||`, which is larger
wherever the argument of `Z_t(δ)` moves. With no kernel roots, `λ = K ‖Ż‖` and this is the
root-free variation estimate. -/
theorem abs_log_sub_le_of_selection {ι Λc : Type*} [Finite ι] {s : Set ℝ} (hs : s.OrdConnected)
    {m : ℝ → ℝ} (hm : ContinuousOn m s) (hpos : ∀ t ∈ s, 0 < m t) (n : ι → Λc →₀ ℕ)
    {f f' : Λc → ℝ → ℂ} {Λ lam : ℝ → ℝ} (hΛ : ∀ t ∈ s, HasDerivAt Λ (lam t) t)
    (hf : ∀ j γ, n j γ ≠ 0 → ∀ t ∈ s, HasDerivAt (f γ) (f' γ t) t)
    (hrate : ∀ j γ, n j γ ≠ 0 → ∀ t ∈ s, ‖f' γ t‖ ≤ lam t * ‖f γ t‖)
    (hsel : ∀ t ∈ s, ∃ j, m t = (n j).sum fun γ k ↦ k * ‖f γ t‖) {u t : ℝ} (hu : u ∈ s)
    (ht : t ∈ s) (hut : u ≤ t) : |log (m t) - log (m u)| ≤ Λ t - Λ u := by
  -- each candidate sum is monotone after the weight `e^{Λ}` and antitone after `e^{-Λ}`
  have hcand : ∀ j, MonotoneOn (fun t ↦ exp (Λ t) * (n j).sum fun γ k ↦ k * ‖f γ t‖) s ∧
      AntitoneOn (fun t ↦ exp (-Λ t) * (n j).sum fun γ k ↦ k * ‖f γ t‖) s := fun j ↦ by
    have hγ := fun γ (hγ : γ ∈ (n j).support) ↦ monotoneOn_exp_mul_norm_of_hasDerivAt hs
      (hf j γ (Finsupp.mem_support_iff.1 hγ)) hΛ (hrate j γ (Finsupp.mem_support_iff.1 hγ))
    refine ⟨fun a ha b hb hab ↦ ?_, fun a ha b hb hab ↦ ?_⟩
    · simp only [Finsupp.sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun γ hγ' ↦ ?_
      rw [mul_left_comm, mul_left_comm (exp (Λ b))]
      exact mul_le_mul_of_nonneg_left ((hγ γ hγ').1 ha hb hab) (Nat.cast_nonneg _)
    · simp only [Finsupp.sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun γ hγ' ↦ ?_
      rw [mul_left_comm, mul_left_comm (exp (-Λ a))]
      exact mul_le_mul_of_nonneg_left ((hγ γ hγ').2 ha hb hab) (Nat.cast_nonneg _)
  have hΛc : ContinuousOn Λ s := fun t ht ↦ (hΛ t ht).continuousAt.continuousWithinAt
  have hup : MonotoneOn (fun t ↦ exp (Λ t) * m t) s :=
    monotoneOn_of_continuousOn_of_selection hs ((continuous_exp.comp_continuousOn hΛc).mul hm)
      (g := fun j t ↦ exp (Λ t) * (n j).sum fun γ k ↦ k * ‖f γ t‖) (fun j ↦ (hcand j).1)
      fun t ht ↦ (hsel t ht).imp fun j hj ↦ by simp only [hj]
  have hdown : MonotoneOn (fun t ↦ -(exp (-Λ t) * m t)) s :=
    monotoneOn_of_continuousOn_of_selection hs
      ((continuous_exp.comp_continuousOn hΛc.neg).mul hm).neg
      (g := fun j t ↦ -(exp (-Λ t) * (n j).sum fun γ k ↦ k * ‖f γ t‖))
      (fun j a ha b hb hab ↦ neg_le_neg ((hcand j).2 ha hb hab))
      fun t ht ↦ (hsel t ht).imp fun j hj ↦ by simp only [hj]
  have h1 := hup hu ht hut
  have h2 := neg_le_neg_iff.1 (hdown hu ht hut)
  have hmu := hpos u hu
  have hmt := hpos t ht
  have l1 := Real.log_le_log (by positivity) h1
  have l2 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (exp_pos _).ne' hmu.ne', Real.log_mul (exp_pos _).ne' hmt.ne', Real.log_exp,
    Real.log_exp] at l1 l2
  rw [abs_le]
  constructor <;> linarith

/-- A charge vanishing at the end of the ray: `a ↦ e^{La} ‖a z‖` is monotone on `[0, ∞)` for
`L ≥ 0`. -/
theorem monotoneOn_exp_mul_norm_mul {z : ℂ} {L : ℝ} (hL : 0 ≤ L) :
    MonotoneOn (fun a : ℝ ↦ exp (L * a) * ‖(a : ℂ) * z‖) (Ici 0) := by
  intro a ha b hb hab
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ a from ha), abs_of_nonneg (show (0 : ℝ) ≤ b from hb)]
  have he : exp (L * a) ≤ exp (L * b) := exp_le_exp.2 (mul_le_mul_of_nonneg_left hab hL)
  rw [← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul he hab ha (exp_pos _).le) (norm_nonneg _)

/-- A class is **radial** for `w`, `z` on `s` if `w = 0` or `‖z‖ ≤ L ‖w + a z‖` on `s`; then
`a ↦ e^{La} ‖w + a z‖` is monotone on every interval `s ⊆ [0, ∞)`. -/
theorem monotoneOn_exp_mul_norm_of_radial {w z : ℂ} {L : ℝ} (hL : 0 ≤ L) {s : Set ℝ}
    (hs : s.OrdConnected) (hs0 : s ⊆ Ici 0) (h : w = 0 ∨ ∀ a ∈ s, ‖z‖ ≤ L * ‖w + a * z‖) :
    MonotoneOn (fun a : ℝ ↦ exp (L * a) * ‖w + a * z‖) s := by
  rcases h with rfl | h
  · simpa using (monotoneOn_exp_mul_norm_mul (z := z) hL).mono hs0
  · exact monotoneOn_exp_mul_norm_add_mul hs h

/-- **Sums of radial charges.** For multiplicities `n : Λ →₀ ℕ` whose classes are radial,
`a ↦ e^{La} Σ_γ n_γ ‖Z_*(γ) + a V(γ)‖` is monotone on every interval `s ⊆ [0, ∞)`. -/
theorem monotoneOn_exp_mul_finsuppSum {Λ : Type*} (Z₀ V : Λ → ℂ) (n : Λ →₀ ℕ) {L : ℝ}
    (hL : 0 ≤ L) {s : Set ℝ} (hs : s.OrdConnected) (hs0 : s ⊆ Ici 0)
    (h : ∀ γ, n γ ≠ 0 → Z₀ γ = 0 ∨ ∀ a ∈ s, ‖V γ‖ ≤ L * ‖Z₀ γ + a * V γ‖) :
    MonotoneOn (fun a : ℝ ↦ exp (L * a) * n.sum fun γ k ↦ k * ‖Z₀ γ + a * V γ‖) s := by
  intro a ha b hb hab
  simp only [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun γ hγ ↦ ?_
  have hm := monotoneOn_exp_mul_norm_of_radial (w := Z₀ γ) (z := V γ) hL hs hs0
    (h γ (Finsupp.mem_support_iff.1 hγ)) ha hb hab
  simp only at hm
  rw [mul_left_comm, mul_left_comm (exp (L * b))]
  exact mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)

/-! ### Rays of stability conditions -/

namespace CategoryTheory.Triangulated

open CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (C) in
/-- **A lifted ray to a finite period.** Prestability conditions `σ_a`, `0 < a ≤ a₀`, with charges
`Z_* + aV` on the class lattice, continuous masses and, on each compact segment `[b, a₀]` with
`0 < b`, finitely many candidate sums for the mass of each object. See the module docstring for the
sources of the fields. -/
structure RadialRayHypotheses {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ) where
  /-- The prestability condition at the point `a` of the ray. -/
  cond : ℝ → PreStabilityCondition.WithClassMap C v
  /-- The length of the ray. -/
  a₀ : ℝ
  a₀_pos : 0 < a₀
  /-- The limiting period `Z_*`. -/
  Z₀ : Λ →+ ℂ
  /-- The direction `V` of the ray. -/
  V : Λ →+ ℂ
  /-- The charge at `a` is `Z_* + aV`. -/
  charge_eq : ∀ a ∈ Ioc 0 a₀, ∀ γ, (cond a).Z γ = Z₀ γ + a * V γ
  /-- The rate `L = K ‖V‖`, with `K` the constant of the punctured support bound. -/
  L : ℝ
  L_nonneg : 0 ≤ L
  /-- The mass of every object is continuous along the ray (Bridgeland, arXiv:math/0212237,
  §8). -/
  continuousOn_mass : ∀ E, ContinuousOn (fun a ↦ (cond a).mass E) (Ioc 0 a₀)
  /-- **Finitely many candidate sums on each compact segment.** For each object `E` and each
  segment `[b, a₀]` with `0 < b` there are finitely many multiplicity functions `n_j` such that at
  every point of the segment the mass of `E` is `Σ_γ n_j(γ) |Z_a(γ)|` for one of them (the classes
  of the stable factors of the HN factors, finitely many with bounded multiplicities on a compact
  set of stability conditions: Bridgeland, arXiv:math/0307164, Lemma 9.2 and the proof of
  Proposition 9.3), and every class that occurs is killed by `Z_*` or satisfies
  `|V(γ)| ≤ L |Z_a(γ)|` on the segment (the punctured support bound, for classes with `v² ≥ -2`
  outside the kernel roots). Nothing is assumed on the whole ray `(0, a₀]` at once, which need not
  lie in a compact set. -/
  finite_selection : ∀ E : C, ∀ b ∈ Ioc 0 a₀, ∃ (N : ℕ) (n : Fin N → Λ →₀ ℕ),
    (∀ j γ, n j γ ≠ 0 → Z₀ γ = 0 ∨ ∀ a ∈ Icc b a₀, ‖V γ‖ ≤ L * ‖Z₀ γ + a * V γ‖) ∧
      ∀ a ∈ Icc b a₀, ∃ j, (cond a).mass E = (n j).sum fun γ k ↦ k * ‖Z₀ γ + a * V γ‖

namespace RadialRayHypotheses

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ} (I : RadialRayHypotheses C v)

/-- **The one-sided bound along the ray**: `a ↦ e^{La} m_a(E)` is nondecreasing on `(0, a₀]`. For
`u ≤ t` on the ray, the selection lemma is applied on the compact segment `[u, a₀]`, which has
finitely many candidate sums. -/
theorem monotoneOn_exp_mul_mass (E : C) :
    MonotoneOn (fun a ↦ exp (I.L * a) * (I.cond a).mass E) (Ioc 0 I.a₀) := by
  intro u hu t ht hut
  obtain ⟨N, n, hrad, hsel⟩ := I.finite_selection E u hu
  have hs : (Icc u I.a₀).OrdConnected := ordConnected_Icc
  have hmono : MonotoneOn (fun a ↦ exp (I.L * a) * (I.cond a).mass E) (Icc u I.a₀) := by
    refine monotoneOn_of_continuousOn_of_selection hs
      ((continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
        ((I.continuousOn_mass E).mono (Icc_subset_Ioc hu.1 le_rfl)))
      (g := fun j a ↦ exp (I.L * a) * (n j).sum fun γ k ↦ k * ‖I.Z₀ γ + a * I.V γ‖)
      (fun j ↦ monotoneOn_exp_mul_finsuppSum I.Z₀ I.V (n j) I.L_nonneg hs
        (fun _ ha ↦ hu.1.le.trans ha.1) fun γ hγ ↦ hrad j γ hγ) fun a ha ↦ ?_
    obtain ⟨j, hj⟩ := hsel a ha
    exact ⟨j, by simp only [hj]⟩
  exact hmono ⟨le_rfl, hu.2⟩ ⟨hut, ht.2⟩ hut

/-- The **radial limit** `m_*(E) = lim_{a → 0+} m_a(E)`, as the infimum of `e^{La} m_a(E)` over
`(0, a₀)`. -/
def radialMass (E : C) : ℝ :=
  sInf ((fun a ↦ exp (I.L * a) * (I.cond a).mass E) '' Ioo 0 I.a₀)

private lemma bddBelow_image (E : C) :
    BddBelow ((fun a ↦ exp (I.L * a) * (I.cond a).mass E) '' Ioo 0 I.a₀) :=
  ⟨0, by rintro _ ⟨a, -, rfl⟩; exact mul_nonneg (exp_pos _).le ((I.cond a).mass_nonneg E)⟩

lemma radialMass_nonneg (E : C) : 0 ≤ I.radialMass E :=
  le_csInf ((nonempty_Ioo.2 I.a₀_pos).image _)
    (by rintro _ ⟨a, -, rfl⟩; exact mul_nonneg (exp_pos _).le ((I.cond a).mass_nonneg E))

/-- `e^{La} m_a(E)` tends to the radial limit as `a → 0+`. -/
theorem tendsto_exp_mul_mass (E : C) :
    Tendsto (fun a ↦ exp (I.L * a) * (I.cond a).mass E) (𝓝[>] 0) (𝓝 (I.radialMass E)) :=
  MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 I.a₀_pos)
    ((I.monotoneOn_exp_mul_mass E).mono Ioo_subset_Ioc_self) (I.bddBelow_image E)

/-- **The radial limit exists**: `m_a(E) → m_*(E)` as `a → 0+`. -/
theorem tendsto_radialMass (E : C) :
    Tendsto (fun a ↦ (I.cond a).mass E) (𝓝[>] 0) (𝓝 (I.radialMass E)) := by
  have he : Tendsto (fun a : ℝ ↦ exp (-(I.L * a))) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun a : ℝ ↦ exp (-(I.L * a)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have := he.mul (I.tendsto_exp_mul_mass E)
  rw [one_mul] at this
  refine this.congr fun a ↦ ?_
  rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]

/-- `m_*(E) ≤ e^{La} m_a(E)` at every point of the ray. -/
theorem radialMass_le (E : C) {a : ℝ} (ha : a ∈ Ioc 0 I.a₀) :
    I.radialMass E ≤ exp (I.L * a) * (I.cond a).mass E := by
  rcases ha.2.lt_or_eq with h | rfl
  · exact csInf_le (I.bddBelow_image E) ⟨a, ⟨ha.1, h⟩, rfl⟩
  · obtain ⟨b, hb⟩ := nonempty_Ioo.2 I.a₀_pos
    exact (csInf_le (I.bddBelow_image E) ⟨b, hb, rfl⟩).trans
      (I.monotoneOn_exp_mul_mass E ⟨hb.1, hb.2.le⟩ ha hb.2.le)

/-- The radial limit as a profile. -/
def radialProfile : Profile C :=
  Profile.ofFun fun E ↦ ⟨I.radialMass E, I.radialMass_nonneg E⟩

@[simp]
lemma coe_radialProfile_apply (E : C) : (I.radialProfile E : ℝ) = I.radialMass E := rfl

/-- The mass profiles converge to the radial limit profile, pointwise, as `a → 0+`. -/
theorem tendsto_massProfile :
    Tendsto (fun a ↦ (I.cond a).massProfile) (𝓝[>] 0) (𝓝 I.radialProfile) :=
  Profile.tendsto_nhds_iff.2 fun E ↦ NNReal.tendsto_coe.1 (I.tendsto_radialMass E)

/-- The charges converge to the limiting period on every class. -/
theorem tendsto_charge (γ : Λ) :
    Tendsto (fun a ↦ (I.cond a).Z γ) (𝓝[>] 0) (𝓝 (I.Z₀ γ)) := by
  have hev : (fun a : ℝ ↦ I.Z₀ γ + a * I.V γ) =ᶠ[𝓝[>] 0] fun a ↦ (I.cond a).Z γ := by
    filter_upwards [Ioo_mem_nhdsGT I.a₀_pos] with a ha
    exact (I.charge_eq a ⟨ha.1, ha.2.le⟩ γ).symm
  refine Tendsto.congr' hev ?_
  have : Continuous fun a : ℝ ↦ I.Z₀ γ + a * I.V γ := by fun_prop
  simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds

/-- **The class infimum of the radial limit.** If at every point of the ray the class `γ` has a
representative in `𝒮` that is semistable there (for `𝒮` the spherical objects of a K3 surface and
`γ` a root: Kikuta–Koseki–Ouchi, arXiv:2504.12253, Lemma 3.4), then
`inf {m_*(S) : S ∈ 𝒮, v(S) = γ} = |Z_*(γ)|`. -/
theorem classInf_radialProfile {𝒮 : Set C} {γ : Λ}
    (hrep : ∀ a ∈ Ioc 0 I.a₀, ∃ S ∈ 𝒮, classOf C v S = γ ∧ ∃ φ, (I.cond a).slicing.P φ S) :
    (Profile.classInf 𝒮 (classOf C v) I.radialProfile γ : ℝ) = ‖I.Z₀ γ‖ := by
  obtain ⟨S₀, hS₀, hS₀γ, -⟩ := hrep I.a₀ ⟨I.a₀_pos, le_rfl⟩
  have hne : (Profile.classFibre 𝒮 (classOf C v) γ).Nonempty := ⟨S₀, hS₀, hS₀γ⟩
  refine le_antisymm ?_ ?_
  · -- `d_{m_*}(γ) ≤ e^{La} |Z_a(γ)|` for every `a`, and the right side tends to `|Z_*(γ)|`
    have hbound : ∀ a ∈ Ioc 0 I.a₀, (Profile.classInf 𝒮 (classOf C v) I.radialProfile γ : ℝ) ≤
        exp (I.L * a) * ‖(I.cond a).Z γ‖ := fun a ha ↦ by
      obtain ⟨S, hS, hSγ, φ, hφ⟩ := hrep a ha
      have h1 := NNReal.coe_le_coe.2
        (Profile.classInf_le_of_mem (μ := I.radialProfile) (⟨hS, hSγ⟩ :
          S ∈ Profile.classFibre 𝒮 (classOf C v) γ))
      refine h1.trans ((I.radialMass_le S ha).trans_eq ?_)
      rw [(I.cond a).mass_eq_norm_charge_of_semistable hφ,
        PreStabilityCondition.WithClassMap.charge_def, hSγ]
    have hlim : Tendsto (fun a ↦ exp (I.L * a) * ‖(I.cond a).Z γ‖) (𝓝[>] 0)
        (𝓝 (exp (I.L * 0) * ‖I.Z₀ γ‖)) := by
      have he : Tendsto (fun a : ℝ ↦ exp (I.L * a)) (𝓝[>] 0) (𝓝 (exp (I.L * 0))) :=
        ((by fun_prop : Continuous fun a : ℝ ↦ exp (I.L * a)).tendsto 0).mono_left
          nhdsWithin_le_nhds
      exact he.mul (I.tendsto_charge γ).norm
    rw [mul_zero, exp_zero, one_mul] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT I.a₀_pos] with a ha
    exact hbound a ⟨ha.1, ha.2.le⟩
  · -- `|Z_a ∘ v| ≤ m_a` passes to the limit
    refine Profile.le_classInf_of_tendsto (fs := fun a γ ↦ ‖(I.cond a).Z γ‖) I.tendsto_massProfile
      (fun γ ↦ (I.tendsto_charge γ).norm) (Eventually.of_forall fun a S _ ↦ ?_) hne
    exact (I.cond a).norm_charge_le_mass S

end RadialRayHypotheses

end CategoryTheory.Triangulated
