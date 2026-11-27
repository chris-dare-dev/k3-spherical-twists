/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.GroupAction.MassComparison
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The point-mass corollary

Let `X` be a K3 surface with `Pic X = ℤH`, `σ` a stability condition in the distinguished
component `Stab†(X)`, `x` a closed point and `Φ` a finite word of spherical twists. The
corollary of the article "Harder–Narasimhan towers of spherical twist words on a Picard-rank-one
K3 surface" states

  `lim_{n→∞} m_σ(Φ^{±n} 𝒪_x)^{1/n} = exp h_cat(Φ) = exp h_cat(Φ⁻¹)`,

uniformly in `x` and in `σ` at bounded distance from a reference condition; the same limit along
`σ_n` with `d(σ_n, τ) = o(n)` and arbitrary points `x_n`; the comparison
`c e^{-d} p(W) ≤ m_σ(W 𝒪_x) ≤ C e^{d} p(W)` for **every** word; and the rate per letter
`exp(h_cat(Φ)/ℓ)` along the prefixes of a periodic word of period `ℓ`.

This file proves all of these from the inputs collected in `PointMassHypotheses`. Mathlib does not
yet have derived categories of K3 surfaces, Bridgeland stability or categorical entropy, so the
geometric facts enter as named fields; each field's docstring gives its source (a lemma of the
article, or a published theorem). `PointMassHypotheses` extends `MassComparisonHypotheses` (the
comparison of masses with total Hom from the split generator `G`) by the rank-one point fields.
The constants `C`, `c` of the two-sided comparison `c h(G, V) ≤ m_τ(V) ≤ C h(G, V)` and the
entropy `h_cat` are no longer inputs: `C = m_τ(G)/C₁` comes from the upper comparison
`dhkk_comparison`, `c` from the twist triangles of the summands `S_i` (the lower comparison
`MassComparisonHypotheses.hom_G_le_mul_mass`), and `h_cat(Φ) = lim log h(G, Φⁿ G)/n` exists by
Fekete's lemma. The distance bound `δ` of the comparison is at most Bridgeland's metric.
Everything after the fields is proved here: the comparison for a fixed period, the two-sided
estimate, Fekete's lemma, the identification of the limit and the treatment of standard words.

The notation follows the article: `h(U, V) = Σ_j dim Hom(U, V[j])`, `R(U)` is the sum of the
generic ranks of the ordinary cohomology sheaves of `U`, `S_i = A^{-i}` (`i = 0, 1, 2`) for a very
ample `A = 𝒪(bH)` with `ν = A²/2`, `G = S₀ ⊕ S₁ ⊕ S₂`, `H(W) = h(G, WG)` and
`p(W) = Σ_i R(W⁻¹ S_i)`.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open Filter Topology Real Finset

/-- The inputs of the point-mass corollary.

`Obj` stands for the isomorphism classes of objects of `D^b(X)`, `Γ` for a group of exact
autoequivalences containing the spherical twists and acting on them, `Stab` for the distinguished
component `Stab†(X)` with Bridgeland's metric (on which `Γ` acts) and `Pt` for the closed points.
The summands `S_i` of the split generator `G` are the three line bundles `A^{-i}`, `i = 0, 1, 2`.
-/
structure PointMassHypotheses (Obj Γ Stab Pt : Type*) [Group Γ] [MulAction Γ Obj]
    [PseudoMetricSpace Stab] [MulAction Γ Stab]
    extends MassComparisonHypotheses Obj Γ Stab (Fin 3) where
  /-- `R(U) = Σ_q rk 𝓗^q(U)`, the sum of the generic ranks of the cohomology sheaves. -/
  rank : Obj → ℝ
  /-- The skyscraper sheaves `𝒪_x`. -/
  point : Pt → Obj
  /-- The reference geometric condition `τ = σ_{ia}`, `a > 1/√d`. -/
  τ : Stab
  /-- Standard autoequivalences: compositions of a shift, a line-bundle tensor and an
  automorphism of `X`. -/
  Standard : Γ → Prop
  /-- `ν = A²/2`. -/
  ν : ℝ
  ν_pos : 0 < ν
  /-- The distance bound of the comparison is at most Bridgeland's metric (Bridgeland,
  arXiv:math/0212237, Proposition 8.1). -/
  δ_le_dist : ∀ σ σ', δ σ σ' ≤ dist σ σ'
  rank_nonneg : ∀ U, 0 ≤ rank U
  /-- The point test `h(E, 𝒪_x) = R(E)` for a spherical `E` (the article's point-measurement
  lemma: the cohomology sheaves of a spherical object are rigid vector bundles, by Mukai's
  inequality and local freeness). -/
  hom_point : ∀ U x, Spherical U → hom U (point x) = rank U
  /-- `ν R(E) ≤ h(E, G)` for a spherical `E` (the article's point-measurement lemma: the point
  test for the length-`2ν` intersection of two sections of `A`, through its Koszul resolution by
  `S₂, S₁², S₀`). -/
  nu_rank_le : ∀ U, Spherical U → ν * rank U ≤ hom U G
  /-- **Lemma A.1 of the article.** For a fixed `F` with `R(F) > 0` there is `C_F` with
  `h(E, G) ≤ C_F (R(E) + h(E, F))` for every spherical `E`. -/
  fixedTest : ∀ F, 0 < rank F →
    ∃ CF, 0 ≤ CF ∧ ∀ U, Spherical U → hom U G ≤ CF * (rank U + hom U F)
  /-- **Lemma A.2 of the article.** If `R(Φ 𝒪_x) = 0` at one point, `Φ` is standard. -/
  standard_of_rank_zero : ∀ (Φ : Γ) x, rank (Φ • point x) = 0 → Standard Φ
  /-- Powers of a standard autoequivalence are standard. -/
  standard_zpow : ∀ Φ, Standard Φ → ∀ n : ℤ, Standard (Φ ^ n)
  /-- A standard autoequivalence sends a point to a shifted point, whose mass at the reference
  condition is `|Z_τ(𝒪_x)| = 1`. -/
  standard_mass : ∀ Φ, Standard Φ → ∀ x, mass τ (Φ • point x) = 1
  /-- For a standard autoequivalence `H(Φⁿ)` grows at most quadratically: by Riemann–Roch and
  Kodaira vanishing it is `18 + 12ν + 9du²n²`
  (`AlgebraicGeometry.K3.PicardRankOne.standard_H_formula`). -/
  standard_hom : ∀ Φ, Standard Φ → ∃ A B : ℝ, ∀ n : ℕ, hom G (Φ ^ n • G) ≤ A + B * n ^ 2
  /-- The image of a point is nonzero, so its mass is positive. -/
  mass_pos : ∀ σ (W : Γ) x, 0 < mass σ (W • point x)

namespace PointMassHypotheses

variable {Obj Γ Stab Pt : Type*} [Group Γ] [MulAction Γ Obj] [PseudoMetricSpace Stab]
  [MulAction Γ Stab] (I : PointMassHypotheses Obj Γ Stab Pt)

/-! ### Former fields

Sixteen inputs that `PointMassHypotheses` now inherits from `MassComparisonHypotheses` were once
its own fields: `G`, `K`, `K_pos`, `S`, `Spherical`, `hcat`, `hom`, `hom_G`, `hom_comm`,
`hom_diag`, `hom_smul`, `mass`, `mass_smul`, `one_le_hom_G`, `spherical_S` and `spherical_smul`.
Dot notation such as `I.hom` reaches the inherited fields as before. Fifteen of them are still
fields, through the parent, and Lean reserves the name `PointMassHypotheses.f` of a field `f`, so
those full names cannot be declared again; their projections are now `MassComparisonHypotheses.f`
(and `MassDistanceBound.mass`). The entropy `hcat` is no longer a field: it is the definition
`MassComparisonHypotheses.hcat`, and the abbreviation below keeps its old name. -/

/-- Categorical entropy at parameter `0`, `h_cat(Φ) = lim log h(G, Φⁿ G)/n` (`hcat_spec`): the
definition `MassComparisonHypotheses.hcat`, under the name of the former field. -/
noncomputable abbrev hcat (Φ : Γ) : ℝ := I.toMassComparisonHypotheses.hcat Φ

/-! ### The constants of the comparison -/

/-- The constant of the upper mass estimate, `C = m_τ(G)/C₁`. -/
noncomputable def C : ℝ := I.mass I.τ I.G / I.C₁

/-- The constant of the lower mass estimate, `c = 1/L_τ`. -/
noncomputable def c : ℝ := (I.lowerConst I.τ)⁻¹

theorem C_pos : 0 < I.C := div_pos (I.mass_G_pos I.τ) I.C₁_pos

theorem c_pos : 0 < I.c := inv_pos.mpr (I.lowerConst_pos I.τ)

/-- `m_τ(V) ≤ C h(G, V)` (the article's point-measurement lemma), from the upper comparison. -/
theorem mass_le_hom (U : Obj) : I.mass I.τ U ≤ I.C * I.hom I.G U :=
  I.mass_le_mul_hom I.τ U

/-- `c h(G, V) ≤ m_τ(V)` (the article's point-measurement lemma), from the twist triangles of the
`S_i`: the lower comparison. -/
theorem hom_le_mass (U : Obj) : I.c * I.hom I.G U ≤ I.mass I.τ U := by
  have h := I.hom_G_le_mul_mass I.τ U
  have hL := I.lowerConst_pos I.τ
  rw [c, inv_mul_le_iff₀ hL]
  exact h

/-- Bridgeland's metric bounds the change of mass (Bridgeland, arXiv:math/0212237,
Proposition 8.1), through the distance bound `δ ≤ d`. -/
theorem mass_le_exp_dist (σ σ' : Stab) (U : Obj) :
    I.mass σ U ≤ exp (dist σ σ') * I.mass σ' U :=
  (I.mass_le_exp_δ σ σ' U).trans (mul_le_mul_of_nonneg_right
    (exp_le_exp.mpr (I.δ_le_dist σ σ')) (I.mass_nonneg σ' U))

/-- The entropy formula `h_cat(Φ) = lim log h(G, Φⁿ G)/n` (Dimitrov–Haiden–Katzarkov–Kontsevich,
arXiv:1307.8418, Theorem 2.6, at `t = 0`). -/
theorem hcat_spec (Φ : Γ) :
    Tendsto (fun n : ℕ => log (I.hom I.G (Φ ^ n • I.G)) / n) atTop (𝓝 (I.hcat Φ)) :=
  I.tendsto_hcat Φ

/-- `H(W) = h(G, WG)`. -/
def H (W : Γ) : ℝ := I.hom I.G (W • I.G)

/-- `p(W) = Σ_i R(W⁻¹ S_i)`, the point measurement. -/
def p (W : Γ) : ℝ := ∑ i, I.rank (W⁻¹ • I.S i)

/-! ### Moving autoequivalences across Hom -/

lemma hom_smul_left (g : Γ) (U V : Obj) : I.hom (g • U) V = I.hom U (g⁻¹ • V) := by
  calc I.hom (g • U) V = I.hom (g • U) (g • (g⁻¹ • V)) := by rw [smul_inv_smul]
    _ = I.hom U (g⁻¹ • V) := I.hom_smul g U _

lemma hom_G_smul (g : Γ) (V : Obj) : I.hom I.G (g • V) = I.hom (g⁻¹ • I.G) V := by
  rw [I.hom_smul_left, inv_inv]

lemma H_eq_sum (W : Γ) : I.H W = ∑ i, I.hom (W⁻¹ • I.S i) I.G := by
  simp only [H, I.hom_G, I.hom_smul_left, inv_inv]

lemma H_pos (W : Γ) : 0 < I.H W := lt_of_lt_of_le one_pos (I.one_le_hom_G W)

lemma p_nonneg (W : Γ) : 0 ≤ I.p W := sum_nonneg fun _ _ => I.rank_nonneg _

/-- **The point measurement**: `h(G, W 𝒪_x) = p(W)` at every closed point. -/
theorem pointTest (W : Γ) (x : Pt) : I.hom I.G (W • I.point x) = I.p W := by
  simp only [p, I.hom_G]
  refine sum_congr rfl fun i _ => ?_
  rw [← I.hom_point _ x (I.spherical_smul _ _ (I.spherical_S i)), I.hom_smul_left, inv_inv]

/-- `ν p(W) ≤ H(W)`. -/
theorem nu_p_le_H (W : Γ) : I.ν * I.p W ≤ I.H W := by
  rw [p, mul_sum, H_eq_sum]
  exact sum_le_sum fun i _ => I.nu_rank_le _ (I.spherical_smul _ _ (I.spherical_S i))

lemma p_pos (W : Γ) (x : Pt) : 0 < I.p W := by
  have h1 := I.mass_le_hom (W • I.point x)
  have h2 := I.mass_pos I.τ W x
  rw [I.pointTest] at h1
  by_contra h
  have : I.p W = 0 := le_antisymm (not_lt.mp h) (I.p_nonneg W)
  rw [this, mul_zero] at h1
  linarith

/-! ### The two-sided estimate for every word -/

/-- **The uniform estimate.** For every word `W`, point `x` and stability condition `σ`,
`c e^{-d(σ,τ)} p(W) ≤ m_σ(W 𝒪_x) ≤ C e^{d(σ,τ)} p(W)`. -/
theorem uniform_estimate (W : Γ) (x : Pt) (σ : Stab) :
    I.c * exp (-dist σ I.τ) * I.p W ≤ I.mass σ (W • I.point x) ∧
      I.mass σ (W • I.point x) ≤ I.C * exp (dist σ I.τ) * I.p W := by
  have hτσ := I.mass_le_exp_dist I.τ σ (W • I.point x)
  have hστ := I.mass_le_exp_dist σ I.τ (W • I.point x)
  have hup := I.mass_le_hom (W • I.point x)
  have hlo := I.hom_le_mass (W • I.point x)
  rw [I.pointTest] at hup hlo
  rw [dist_comm] at hτσ
  have he : 0 < exp (dist σ I.τ) := exp_pos _
  constructor
  · rw [exp_neg]
    have : I.c * I.p W ≤ exp (dist σ I.τ) * I.mass σ (W • I.point x) := hlo.trans hτσ
    rw [mul_comm I.c, mul_assoc, ← div_eq_inv_mul, div_le_iff₀ he]
    linarith
  · calc I.mass σ (W • I.point x) ≤ exp (dist σ I.τ) * I.mass I.τ (W • I.point x) := hστ
      _ ≤ exp (dist σ I.τ) * (I.C * I.p W) := mul_le_mul_of_nonneg_left hup he.le
      _ = I.C * exp (dist σ I.τ) * I.p W := by ring

/-- The logarithmic form of the uniform estimate: replacing the point mass of **any** prefix by
`p(W)` costs at most `d(σ, τ) + max(|log c|, |log C|)` on the logarithmic scale. -/
theorem abs_log_mass_sub_log_p_le (W : Γ) (x : Pt) (σ : Stab) :
    |log (I.mass σ (W • I.point x)) - log (I.p W)| ≤
      dist σ I.τ + max |log I.c| |log I.C| := by
  obtain ⟨hlo, hup⟩ := I.uniform_estimate W x σ
  have hp := I.p_pos W x
  have hm := I.mass_pos σ W x
  have hlo' := log_le_log (by have := I.c_pos; positivity) hlo
  have hup' := log_le_log hm hup
  rw [log_mul (by have := I.c_pos; positivity) hp.ne', log_mul I.c_pos.ne' (exp_pos _).ne',
    log_exp] at hlo'
  rw [log_mul (by have := I.C_pos; positivity) hp.ne', log_mul I.C_pos.ne' (exp_pos _).ne',
    log_exp] at hup'
  rw [abs_le]
  constructor
  · have := neg_abs_le (log I.c)
    have := le_max_left |log I.c| |log I.C|
    linarith
  · have := le_abs_self (log I.C)
    have := le_max_right |log I.c| |log I.C|
    linarith

/-- **Arbitrary prefixes.** Along any sequence of words `W_n`, points `x_n` and stability
conditions `σ_n` with `d(σ_n, τ) = o(n)`, the point mass and `p(W_n)` have the same exponential
behaviour: their normalized logarithms differ by a sequence tending to zero. -/
theorem tendsto_log_mass_div_sub (W : ℕ → Γ) (x : ℕ → Pt) (σ : ℕ → Stab)
    (hσ : Tendsto (fun n : ℕ => dist (σ n) I.τ / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => log (I.mass (σ n) (W n • I.point (x n))) / n -
      log (I.p (W n)) / n) atTop (𝓝 0) := by
  refine tendsto_log_div_sub_of_bound (e := fun n => dist (σ n) I.τ + max |log I.c| |log I.C|)
    (fun n => I.abs_log_mass_sub_log_p_le (W n) (x n) (σ n)) ?_
  have h2 : Tendsto (fun n : ℕ => max |log I.c| |log I.C| / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa [add_div] using hσ.add h2

/-! ### Comparison for a fixed period -/

/-- **Comparison for a fixed period** (the article's lemma of that name). For a nonstandard `Φ`
there is `J > 0` such that
`H(W) ≤ J p(W)` for every word `W` commuting with `Φ`. -/
theorem exists_H_le_mul_p [Nonempty Pt] (Φ : Γ) (hΦ : ¬ I.Standard Φ) :
    ∃ J > 0, ∀ W : Γ, Commute W Φ → I.H W ≤ J * I.p W := by
  obtain ⟨x₀⟩ := ‹Nonempty Pt›
  set F := Φ • I.point x₀ with hFdef
  have hF : 0 < I.rank F := lt_of_le_of_ne (I.rank_nonneg F)
    (fun h => hΦ (I.standard_of_rank_zero Φ x₀ h.symm))
  obtain ⟨CF, hCF0, hCF⟩ := I.fixedTest F hF
  have hHΦ := I.H_pos Φ
  refine ⟨CF * (1 + I.K * I.H Φ) + 1, by have := I.K_pos; positivity, fun W hW => ?_⟩
  -- `H(W) ≤ C_F (p(W) + p(WΦ))`
  have h1 : I.H W ≤ CF * (I.p W + I.p (W * Φ)) := by
    have hsum : ∑ i, I.hom (W⁻¹ • I.S i) F = I.p (W * Φ) := by
      rw [← I.pointTest (W * Φ) x₀, I.hom_G, hFdef]
      refine sum_congr rfl fun i _ => ?_
      rw [I.hom_smul_left, inv_inv, mul_smul]
    rw [H_eq_sum, ← hsum, p, ← sum_add_distrib, mul_sum]
    exact sum_le_sum fun i _ => hCF _ (I.spherical_smul _ _ (I.spherical_S i))
  -- `p(WΦ) ≤ K H(Φ) p(W)`
  have h2 : I.p (W * Φ) ≤ I.K * I.H Φ * I.p W := by
    rw [← I.pointTest (W * Φ) x₀, ← I.pointTest W x₀, hW.eq, mul_smul, I.hom_G_smul]
    calc I.hom (Φ⁻¹ • I.G) (W • I.point x₀)
        ≤ I.K * I.hom (Φ⁻¹ • I.G) I.G * I.hom I.G (W • I.point x₀) := I.hom_diag _ _
      _ = I.K * I.H Φ * I.hom I.G (W • I.point x₀) := by
        rw [I.hom_smul_left, inv_inv]; rfl
  have hp := I.p_nonneg W
  calc I.H W ≤ CF * (I.p W + I.p (W * Φ)) := h1
    _ ≤ CF * (I.p W + I.K * I.H Φ * I.p W) := by gcongr
    _ = CF * (1 + I.K * I.H Φ) * I.p W := by ring
    _ ≤ (CF * (1 + I.K * I.H Φ) + 1) * I.p W := by nlinarith

/-! ### The generator orbit -/

/-- `H(Φ^{m+n}) ≤ K H(Φ^m) H(Φ^n)`. -/
theorem H_pow_add_le (Φ : Γ) (m n : ℕ) :
    I.H (Φ ^ (m + n)) ≤ I.K * I.H (Φ ^ m) * I.H (Φ ^ n) := by
  simp only [H]
  rw [pow_add, mul_smul, I.hom_G_smul]
  calc I.hom ((Φ ^ m)⁻¹ • I.G) (Φ ^ n • I.G)
      ≤ I.K * I.hom ((Φ ^ m)⁻¹ • I.G) I.G * I.hom I.G (Φ ^ n • I.G) := I.hom_diag _ _
    _ = I.K * I.hom I.G (Φ ^ m • I.G) * I.hom I.G (Φ ^ n • I.G) := by
      rw [I.hom_smul_left, inv_inv]

/-- `H(W⁻¹) = H(W)`, by Serre duality and invariance of total Hom. -/
theorem H_inv (W : Γ) : I.H W⁻¹ = I.H W := by
  simp only [H]
  rw [I.hom_G_smul, inv_inv, I.hom_comm]

/-- `h_cat(Φ⁻¹) = h_cat(Φ)`. -/
theorem hcat_inv (Φ : Γ) : I.hcat Φ⁻¹ = I.hcat Φ := by
  refine tendsto_nhds_unique (I.hcat_spec Φ⁻¹) ?_
  refine (I.hcat_spec Φ).congr fun n => ?_
  have := I.H_inv (Φ ^ n)
  simp only [H] at this
  rw [inv_pow, this]

/-- `H(Φⁿ)^{1/n} → exp h_cat(Φ)`. -/
theorem tendsto_H_pow (Φ : Γ) :
    Tendsto (fun n : ℕ => I.H (Φ ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 (exp (I.hcat Φ))) :=
  tendsto_rpow_inv_of_log_div (fun _ => I.H_pos _) (I.hcat_spec Φ)

/-- **Certified upper bounds.** Each finite block `k ≥ 1` gives `exp h_cat(Φ) ≤ (K H(Φ^k))^{1/k}`,
and these bounds converge to `exp h_cat(Φ)`. -/
theorem rate_certified (Φ : Γ) :
    (∀ k : ℕ, k ≠ 0 → exp (I.hcat Φ) ≤ (I.K * I.H (Φ ^ k)) ^ (k : ℝ)⁻¹) ∧
      Tendsto (fun k : ℕ => (I.K * I.H (Φ ^ k)) ^ (k : ℝ)⁻¹) atTop (𝓝 (exp (I.hcat Φ))) := by
  obtain ⟨ρ, hρ, hbound, hconv⟩ :=
    exists_rate_of_submul (H := fun n => I.H (Φ ^ n)) I.K_pos (fun n => (I.H_pos _).le)
      (I.H_pow_add_le Φ)
  have := tendsto_nhds_unique hρ (I.tendsto_H_pow Φ)
  subst this
  exact ⟨hbound, hconv⟩

/-- For a standard `Φ`, `h_cat(Φ) = 0`. -/
theorem hcat_eq_zero_of_standard {Φ : Γ} (hΦ : I.Standard Φ) : I.hcat Φ = 0 := by
  obtain ⟨A, B, hAB⟩ := I.standard_hom Φ hΦ
  exact tendsto_nhds_unique (I.hcat_spec Φ)
    (tendsto_log_div_zero_of_poly (fun n => I.one_le_hom_G _) hAB)

/-! ### The corollary -/

/-- **The point-mass corollary, uniform form.** For every word `Φ` and every `D₀`,
`m_σ(Φⁿ 𝒪_x)^{1/n} → exp h_cat(Φ)` uniformly in the point `x` and in the stability condition `σ`
with `d(σ, τ) ≤ D₀`. -/
theorem tendstoUniformly_pointMass [Nonempty Pt] (Φ : Γ) (D₀ : ℝ) :
    TendstoUniformly
      (fun (n : ℕ) (q : Pt × {σ : Stab // dist σ I.τ ≤ D₀}) =>
        I.mass q.2.1 (Φ ^ n • I.point q.1) ^ (n : ℝ)⁻¹)
      (fun _ => exp (I.hcat Φ)) atTop := by
  by_cases hΦ : I.Standard Φ
  · -- a standard word moves a point to a shifted point: the mass stays in `[e^{-D₀}, e^{D₀}]`
    rw [I.hcat_eq_zero_of_standard hΦ, exp_zero]
    have hstd : ∀ n : ℕ, I.Standard (Φ ^ n) := fun n => by
      simpa using I.standard_zpow Φ hΦ n
    refine tendstoUniformly_rpow_inv_of_bounds (H := fun _ => 1) (c := exp (-D₀))
      (C := exp D₀) (exp_pos _) (exp_pos _) (fun _ => zero_le_one) (fun q n => ?_)
      (fun q n => ?_) (by simp)
    · have h := I.mass_le_exp_dist I.τ q.2.1 (Φ ^ n • I.point q.1)
      rw [I.standard_mass _ (hstd n), dist_comm] at h
      have hd := q.2.2
      rw [mul_one, exp_neg]
      rw [inv_le_iff_one_le_mul₀ (exp_pos _)]
      calc 1 ≤ exp (dist q.2.1 I.τ) * I.mass q.2.1 (Φ ^ n • I.point q.1) := h
        _ ≤ exp D₀ * I.mass q.2.1 (Φ ^ n • I.point q.1) := by
          gcongr
          exact (I.mass_pos _ _ _).le
        _ = I.mass q.2.1 (Φ ^ n • I.point q.1) * exp D₀ := mul_comm _ _
    · have h := I.mass_le_exp_dist q.2.1 I.τ (Φ ^ n • I.point q.1)
      rw [I.standard_mass _ (hstd n), mul_one] at h
      rw [mul_one]
      exact h.trans (exp_le_exp.mpr q.2.2)
  · -- otherwise `(c/J) e^{-D₀} H(Φⁿ) ≤ m_σ(Φⁿ 𝒪_x) ≤ (C/ν) e^{D₀} H(Φⁿ)`
    obtain ⟨J, hJ, hHJ⟩ := I.exists_H_le_mul_p Φ hΦ
    have hcomm : ∀ n : ℕ, Commute (Φ ^ n) Φ := fun n => (Commute.refl Φ).pow_left n
    refine tendstoUniformly_rpow_inv_of_bounds (H := fun n => I.H (Φ ^ n))
      (c := I.c * exp (-D₀) / J) (C := I.C * exp D₀ / I.ν)
      (by have := I.c_pos; positivity) (by have := I.C_pos; have := I.ν_pos; positivity)
      (fun n => (I.H_pos _).le) (fun q n => ?_) (fun q n => ?_) (I.tendsto_H_pow Φ)
    · obtain ⟨hlo, -⟩ := I.uniform_estimate (Φ ^ n) q.1 q.2.1
      have hHp := hHJ _ (hcomm n)
      have hp := I.p_nonneg (Φ ^ n)
      have hd : exp (-D₀) ≤ exp (-dist q.2.1 I.τ) := exp_le_exp.mpr (neg_le_neg q.2.2)
      calc I.c * exp (-D₀) / J * I.H (Φ ^ n) ≤ I.c * exp (-D₀) / J * (J * I.p (Φ ^ n)) := by
            gcongr
            have := I.c_pos; positivity
        _ = I.c * exp (-D₀) * I.p (Φ ^ n) := by field_simp
        _ ≤ I.c * exp (-dist q.2.1 I.τ) * I.p (Φ ^ n) := by
            have := I.c_pos; gcongr
        _ ≤ _ := hlo
    · obtain ⟨-, hup⟩ := I.uniform_estimate (Φ ^ n) q.1 q.2.1
      have hνp := I.nu_p_le_H (Φ ^ n)
      have hν := I.ν_pos
      have hp := I.p_nonneg (Φ ^ n)
      calc I.mass q.2.1 (Φ ^ n • I.point q.1) ≤ I.C * exp (dist q.2.1 I.τ) * I.p (Φ ^ n) := hup
        _ ≤ I.C * exp D₀ * I.p (Φ ^ n) := by
            have := I.C_pos; gcongr; exact q.2.2
        _ ≤ I.C * exp D₀ * (I.H (Φ ^ n) / I.ν) := by
            have := I.C_pos
            gcongr
            rw [le_div_iff₀ hν]; linarith
        _ = I.C * exp D₀ / I.ν * I.H (Φ ^ n) := by ring

/-- **The point-mass corollary.** For every word `Φ`, closed point `x` and stability condition
`σ` in the distinguished component, `lim m_σ(Φⁿ 𝒪_x)^{1/n} = exp h_cat(Φ)`. -/
theorem tendsto_pointMass [Nonempty Pt] (Φ : Γ) (x : Pt) (σ : Stab) :
    Tendsto (fun n : ℕ => I.mass σ (Φ ^ n • I.point x) ^ (n : ℝ)⁻¹) atTop
      (𝓝 (exp (I.hcat Φ))) :=
  (I.tendstoUniformly_pointMass Φ (dist σ I.τ)).tendsto_at (x, ⟨σ, le_rfl⟩)

/-- **The point-mass corollary for negative powers**:
`lim m_σ(Φ⁻ⁿ 𝒪_x)^{1/n} = exp h_cat(Φ⁻¹) = exp h_cat(Φ)`. -/
theorem tendsto_pointMass_inv [Nonempty Pt] (Φ : Γ) (x : Pt) (σ : Stab) :
    Tendsto (fun n : ℕ => I.mass σ (Φ⁻¹ ^ n • I.point x) ^ (n : ℝ)⁻¹) atTop
      (𝓝 (exp (I.hcat Φ))) := by
  simpa [I.hcat_inv] using I.tendsto_pointMass Φ⁻¹ x σ

/-- **Varying points and conditions.** The same limit holds along any points `x_n` and
stability conditions `σ_n` with `d(σ_n, τ) = o(n)`. -/
theorem tendsto_log_pointMass_of_sublinear [Nonempty Pt] (Φ : Γ) (x : ℕ → Pt)
    (σ : ℕ → Stab) (hσ : Tendsto (fun n : ℕ => dist (σ n) I.τ / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => log (I.mass (σ n) (Φ ^ n • I.point (x n))) / n) atTop
      (𝓝 (I.hcat Φ)) := by
  -- compare with `p(Φⁿ)`, whose normalized logarithm tends to `h_cat(Φ)` (the case `σ_n = τ`)
  have hp : Tendsto (fun n : ℕ => log (I.p (Φ ^ n)) / n) atTop (𝓝 (I.hcat Φ)) := by
    obtain ⟨x₀⟩ := ‹Nonempty Pt›
    have h0 := I.tendsto_log_mass_div_sub (fun n => Φ ^ n) (fun _ => x₀) (fun _ => I.τ)
      (by simp)
    have h1 : Tendsto (fun n : ℕ => log (I.mass I.τ (Φ ^ n • I.point x₀)) / n) atTop
        (𝓝 (I.hcat Φ)) := by
      have := tendsto_log_div_of_rpow_inv (fun n => I.mass_pos I.τ (Φ ^ n) x₀) (exp_pos _)
        (I.tendsto_pointMass Φ x₀ I.τ)
      rwa [log_exp] at this
    have := h1.sub h0
    rw [sub_zero] at this
    exact this.congr fun n => by ring
  have := (I.tendsto_log_mass_div_sub (fun n => Φ ^ n) x σ hσ).add hp
  rw [zero_add] at this
  exact this.congr fun n => by ring

/-! ### The rate per letter -/

/-- The prefix of length `N` of the infinite word `… letter 1 · letter 0`:
`W₀ = 1`, `W_{N+1} = letter N · W_N`. -/
def prefixWord (letter : ℕ → Γ) : ℕ → Γ
  | 0 => 1
  | N + 1 => letter N * prefixWord letter N

lemma prefixWord_add {letter : ℕ → Γ} {ℓ : ℕ} (hper : ∀ j, letter (j + ℓ) = letter j)
    (k r : ℕ) :
    prefixWord letter (ℓ * k + r) = prefixWord letter r * prefixWord letter (ℓ * k) := by
  have hshift : ∀ j, letter (ℓ * k + j) = letter j := by
    intro j
    induction k generalizing j with
    | zero => simp
    | succ k ih =>
      rw [show ℓ * (k + 1) + j = (ℓ * k + j) + ℓ by ring, hper, ih]
  induction r with
  | zero => simp [prefixWord]
  | succ r ih =>
    rw [show ℓ * k + (r + 1) = (ℓ * k + r) + 1 by ring, prefixWord, ih, hshift, prefixWord,
      mul_assoc]

lemma prefixWord_mul {letter : ℕ → Γ} {ℓ : ℕ} (hper : ∀ j, letter (j + ℓ) = letter j) (k : ℕ) :
    prefixWord letter (ℓ * k) = prefixWord letter ℓ ^ k := by
  induction k with
  | zero => simp [prefixWord]
  | succ k ih =>
    have := prefixWord_add hper k ℓ
    rw [show ℓ * (k + 1) = ℓ * k + ℓ by ring, this, ih, pow_succ']

/-- **The rate per letter.** Along the prefixes `W_N` of a periodic word with period `ℓ ≥ 1`,
whose period is `Φ = W_ℓ`, the point mass grows at the rate `exp(h_cat(Φ)/ℓ)` per letter,
including all incomplete periods. -/
theorem tendsto_log_pointMass_prefix [Nonempty Pt] (letter : ℕ → Γ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hper : ∀ j, letter (j + ℓ) = letter j) (x : Pt) (σ : Stab) :
    Tendsto (fun N : ℕ => log (I.mass σ (prefixWord letter N • I.point x)) / N) atTop
      (𝓝 (I.hcat (prefixWord letter ℓ) / ℓ)) := by
  set Φ := prefixWord letter ℓ
  set a : ℕ → ℝ := fun N => log (I.mass σ (prefixWord letter N • I.point x))
  -- after whole periods
  have hwhole : Tendsto (fun k : ℕ => a (ℓ * k) / k) atTop (𝓝 (I.hcat Φ)) := by
    have := tendsto_log_div_of_rpow_inv (fun n => I.mass_pos σ (Φ ^ n) x) (exp_pos _)
      (I.tendsto_pointMass Φ x σ)
    rw [log_exp] at this
    refine this.congr fun k => ?_
    simp only [a, prefixWord_mul hper]
    rfl
  -- an incomplete period `W_r` changes the logarithm of the mass by at most `d(W_r⁻¹ σ, σ)`
  set D : ℝ := ∑ r ∈ range ℓ, dist ((prefixWord letter r)⁻¹ • σ) σ
  have hclose : ∀ N, |a N - a (ℓ * (N / ℓ))| ≤ D := by
    intro N
    set k := N / ℓ
    set r := N % ℓ
    have hN : N = ℓ * k + r := (Nat.div_add_mod N ℓ).symm
    have hr : r < ℓ := Nat.mod_lt N hℓ
    set g := prefixWord letter r
    set E := prefixWord letter (ℓ * k) • I.point x
    have hEN : prefixWord letter N • I.point x = g • E := by
      rw [hN, prefixWord_add hper, mul_smul]
    have hmass : I.mass σ (g • E) = I.mass (g⁻¹ • σ) E := by
      rw [← I.mass_smul g (g⁻¹ • σ) E, smul_inv_smul]
    have hE : E = Φ ^ k • I.point x := by simp only [E, prefixWord_mul hper]; rfl
    have hpos1 : 0 < I.mass (g⁻¹ • σ) E := by rw [hE]; exact I.mass_pos _ _ _
    have hpos2 : 0 < I.mass σ E := by rw [hE]; exact I.mass_pos _ _ _
    have hdr : dist (g⁻¹ • σ) σ ≤ D :=
      single_le_sum (f := fun r => dist ((prefixWord letter r)⁻¹ • σ) σ)
        (fun _ _ => dist_nonneg) (mem_range.mpr hr)
    have h1 := I.mass_le_exp_dist (g⁻¹ • σ) σ E
    have h2 := I.mass_le_exp_dist σ (g⁻¹ • σ) E
    have l1 := log_le_log hpos1 h1
    have l2 := log_le_log hpos2 h2
    rw [log_mul (exp_pos _).ne' hpos2.ne', log_exp] at l1
    rw [log_mul (exp_pos _).ne' hpos1.ne', log_exp, dist_comm] at l2
    simp only [a]
    rw [hEN, hmass, abs_le]
    constructor <;> linarith
  exact tendsto_log_div_of_period hℓ hwhole hclose

end PointMassHypotheses

end AlgebraicGeometry.K3.PicardRankOne
