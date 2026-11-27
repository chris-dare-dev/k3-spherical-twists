/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.PointMass

/-!
# Orbit growth of a filling profile

Let a group `Γ` of autoequivalences act on objects, with counts `h(U, V) ≥ 0` (total `Ext`
dimensions: symmetric by Serre duality, `Γ`-invariant), a split generator `G = ⊕_k S_k` with the
diagonal estimate `h(U, V) ≤ K h(U, G) h(G, V)`, and `H(W) = h(G, W G) ≥ 1`. A **profile** is a
nonnegative function `μ` on objects; on the translates of the summands it gives
`P(W) = Σ_k μ(W⁻¹ S_k)`. Fix one autoequivalence `Φ` and a `Γ`-stable test class `T` containing
the `S_k`, and assume the generation bound `P(gW) ≤ K' H(g) P(W)` and, on `T`,

* **(Dom)** `ν μ(E) ≤ h(E, G)`, with `ν > 0`;
* **(Fill)** `h(E, G) ≤ C (μ(E) + μ(Φ⁻¹ E))`.

These are the inputs `FillingHypotheses`. This file proves from them the categorical form of the
comparison lemma: for every `W` commuting with `Φ`,

  `ν P(W) ≤ H(W) ≤ C (1 + K' H(Φ)) P(W)`

(`FillingHypotheses.nu_mul_P_le_H`, `FillingHypotheses.H_le_mul_P`), and hence
`P(Φ^{±n})^{1/n} → exp h_cat(Φ)`, where `h_cat(Φ) = lim log H(Φⁿ)/n` exists by Fekete's lemma
(`FillingHypotheses.tendsto_P_pow`, `FillingHypotheses.tendsto_P_inv_pow`). The proof is
elementary: `H(W) = Σ_k h(W⁻¹ S_k, G)`, so (Dom) bounds `H(W)` below term by term, (Fill) bounds
it above by `C (P(W) + P(WΦ))`, and `WΦ = ΦW` with the generation bound gives
`P(WΦ) ≤ K' H(Φ) P(W)`.

(Fill) is a condition on each `Φ`, not a property of the surface, and the theorem is not a
pseudo-Anosov criterion: it does not say which autoequivalences satisfy (Fill). For the point
profile on a K3 surface of Picard rank one, (Fill) holds for every nonstandard `Φ` (by the
article's fixed-object test) and fails for a standard one; beyond Picard rank one it can fail even
on surfaces without `(−2)`-curves (see `FillingHypotheses.fill`).

## The point-mass instance

For the inputs `PointMassHypotheses` of the point-mass corollary and a nonstandard `Φ`,
`PointMassHypotheses.toFillingHypotheses` takes the rank `μ = R` (the point profile `h(-, 𝒪_x)` on
spherical objects), the spherical objects as the test class and `K' = K`; (Fill) is the article's
fixed-object test at `F = Φ 𝒪_x`. Its `P` is the point measurement `p`, so the filling theorem
re-derives the article's comparison for a fixed period
(`PointMassHypotheses.exists_H_le_mul_p_of_filling`) and the rates
`p(Φ^{±n})^{1/n} → exp h_cat(Φ)` (`PointMassHypotheses.tendsto_p_pow`,
`PointMassHypotheses.tendsto_p_inv_pow`). Two more facts of the rank-one structure:

* **Point–profile duality.** The point profile `μ_x = h(-, 𝒪_x)` satisfies
  `μ_x(W⁻¹ E) = h(E, W 𝒪_x)`: the arrow action moves it to the profile of `W 𝒪_x`. It equals `R`
  on spherical objects, so the point measurement `h(G, W 𝒪_x) = Σ_k μ_x(W⁻¹ S_k) = p(W)` is the
  evaluation of the boundary point `R` on the translates `W⁻¹ S_k`.
* **A fixed point has entropy zero**: if `Φ 𝒪_x = 𝒪_x`, then `h_cat(Φ) = 0`.

## Real objects

The counts of the instance of interest are the total `Ext` dimensions on the derived category of
a K3 surface, acted on by its autoequivalences, and the profile is the point profile. Mathlib has
neither, so there is no instance from geometry: the missing input is the 2-Calabi–Yau category
`D^b(X)` with its spherical twists. The point-mass instance is built from the inputs
`PointMassHypotheses`, and `K3TwistsTest/FillingProfileModel.lean` checks that the fields can hold
together.

## Main definitions

* `FillingHypotheses Obj Γ κ`: the inputs of the filling theorem.
* `FillingHypotheses.H W = h(G, W G)`, `FillingHypotheses.P W = Σ_k μ(W⁻¹ S_k)` and
  `FillingHypotheses.hcat Ψ = lim log H(Ψⁿ)/n`.
* `PointMassHypotheses.pointProfile x = h(-, 𝒪_x)`.
* `PointMassHypotheses.toFillingHypotheses Φ hΦ`: the point-mass instance.

## Main results

* `FillingHypotheses.H_mul_le`: `H(gW) ≤ K H(g) H(W)`; `FillingHypotheses.tendsto_hcat`: the
  limit defining `h_cat` exists.
* `FillingHypotheses.nu_mul_P_le_H`, `FillingHypotheses.H_le_mul_P`: the filling comparison.
* `FillingHypotheses.tendsto_P_pow_of_commute`: `P(Ψⁿ)^{1/n} → exp h_cat(Ψ)` for every `Ψ`
  commuting with `Φ`; `FillingHypotheses.tendsto_P_pow`, `FillingHypotheses.tendsto_P_inv_pow`:
  the cases `Ψ = Φ^{±1}`.
* `PointMassHypotheses.pointProfile_smul`, `PointMassHypotheses.pointProfile_eq_rank`,
  `PointMassHypotheses.pointTest_eq_sum_pointProfile`: point–profile duality.
* `PointMassHypotheses.exists_H_le_mul_p_of_filling`, `PointMassHypotheses.tendsto_p_pow`,
  `PointMassHypotheses.tendsto_p_inv_pow`: the comparison for a fixed period and the rates, from
  the filling theorem.
* `PointMassHypotheses.hcat_eq_zero_of_smul_point_eq`: a fixed point has entropy zero.

## Implementation notes

As in `MassComparison.lean`, objects are a type `Obj` with an action of a group `Γ`, standing for
isomorphism classes of objects of a triangulated category, and counts and profiles are real
functions on it. A profile here is a function `Obj → ℝ` with a nonnegativity field rather than a
`Profile Obj` (an `ℝ≥0`-valued function), to match the real counts.

## References

* D. Orlov, *Remarks on generators and dimensions of triangulated categories*, arXiv:0804.1163,
  Theorem 4 (the diagonal estimate).
* G. Dimitrov, F. Haiden, L. Katzarkov, M. Kontsevich, *Dynamical systems and categories*,
  arXiv:1307.8418, Theorem 2.6 (categorical entropy from total `Ext`).
* M. Fekete, Math. Z. 17 (1923) (Fekete's lemma).

## Tags

categorical entropy, profile, spherical twist, point measurement
-/

open Filter Topology Real Finset

/-! ### The inputs -/

/-- **The inputs of the filling theorem.** `Obj` stands for the isomorphism classes of objects of a
2-Calabi–Yau triangulated category (on a K3 surface, `D^b(X)`), `Γ` for a group of exact
autoequivalences acting on them, `G = ⊕_k S_k` for a split generator, `μ` for a profile, `T` for a
class of test objects and `Φ` for one autoequivalence, whose orbit is measured. The counts
`h(U, V)` are total `Ext` dimensions. -/
structure FillingHypotheses (Obj Γ κ : Type*) [Group Γ] [MulAction Γ Obj] [Fintype κ] where
  /-- `h(U, V) = Σ_j dim Ext^j(U, V)`, the total `Ext` dimension. -/
  hom : Obj → Obj → ℝ
  /-- Counts are nonnegative. -/
  hom_nonneg : ∀ U V, 0 ≤ hom U V
  /-- Serre duality in a 2-Calabi–Yau category: `Ext^j(U, V) ≅ Ext^{2 - j}(V, U)^*`. -/
  hom_comm : ∀ U V, hom U V = hom V U
  /-- An autoequivalence preserves graded `Ext` spaces. -/
  hom_smul : ∀ (g : Γ) (U V : Obj), hom (g • U) (g • V) = hom U V
  /-- The split generator `G = ⊕_k S_k`. -/
  G : Obj
  /-- The summands of the split generator. -/
  S : κ → Obj
  /-- Total `Ext` is additive on `G = ⊕_k S_k`. -/
  hom_G : ∀ V, hom G V = ∑ k, hom (S k) V
  /-- The constant of the diagonal estimate. -/
  K : ℝ
  /-- The constant of the diagonal estimate is positive. -/
  K_pos : 0 < K
  /-- The diagonal estimate `h(U, V) ≤ K h(U, G) h(G, V)`, from Orlov's generation theorem
  (arXiv:0804.1163, Theorem 4) for the diagonal of `X × X`, as in
  `MassComparisonHypotheses.hom_diag`. -/
  hom_diag : ∀ U V, hom U V ≤ K * hom U G * hom G V
  /-- `W G ≠ 0`, so its total `Ext` from `G` is at least one. -/
  one_le_hom_G : ∀ W : Γ, 1 ≤ hom G (W • G)
  /-- The profile. -/
  μ : Obj → ℝ
  /-- The profile is nonnegative. -/
  μ_nonneg : ∀ E, 0 ≤ μ E
  /-- The test class. -/
  T : Obj → Prop
  /-- The summands of the generator are test objects. -/
  T_S : ∀ k, T (S k)
  /-- Autoequivalences preserve the test class. -/
  T_smul : ∀ (g : Γ) E, T E → T (g • E)
  /-- The constant of the generation bound. -/
  K' : ℝ
  /-- **The generation bound** `P(gW) ≤ K' H(g) P(W)`, for `P(W) = Σ_k μ(W⁻¹ S_k)` and
  `H(g) = h(G, g G)`. It holds for every shift-invariant profile that is subadditive on exact
  triangles and additive on direct sums, through the diagonal resolution: the resolution of the
  diagonal behind the diagonal estimate (Orlov, arXiv:0804.1163, Theorem 4) builds each object `U`,
  up to a direct summand, from copies of `Ext^*(G, U) ⊗ G` in a bounded number of cones. Applying
  `W⁻¹` to this tower for `U = g⁻¹ S_k` gives `μ(W⁻¹ g⁻¹ S_k) ≤ K' h(G, g⁻¹ S_k) P(W)`, whose sum
  over `k` is `K' H(g⁻¹) P(W) = K' H(g) P(W)`. This deduction for a general profile has no
  published proof and no human review; it is kept as a field. For the point profile in Picard rank
  one it is proved from the point measurement
  (`AlgebraicGeometry.K3.PicardRankOne.PointMassHypotheses.p_mul_le`). -/
  generation : ∀ g W : Γ,
    ∑ k, μ ((g * W)⁻¹ • S k) ≤ K' * hom G (g • G) * ∑ k, μ (W⁻¹ • S k)
  /-- The constant of (Dom). -/
  ν : ℝ
  /-- The constant of (Dom) is positive. -/
  ν_pos : 0 < ν
  /-- **(Dom)** `ν μ(E) ≤ h(E, G)` for every test object `E`: the counts from the generator
  dominate the profile. For the point profile in Picard rank one this is the article's
  point-measurement lemma (`AlgebraicGeometry.K3.PicardRankOne.PointMassHypotheses.nu_rank_le`). -/
  dom : ∀ E, T E → ν * μ E ≤ hom E G
  /-- The autoequivalence whose orbit is measured. -/
  Φ : Γ
  /-- The constant of (Fill). -/
  C : ℝ
  /-- **(Fill)** `h(E, G) ≤ C (μ(E) + μ(Φ⁻¹ E))` for every test object `E`: the profile and its
  translate by `Φ` together see the counts from the generator.

  In Picard rank one it holds for every nonstandard `Φ`, for the point profile `μ = h(-, 𝒪_x)` on
  spherical objects: this is the article's fixed-object test at `F = Φ 𝒪_x`, since
  `h(E, Φ 𝒪_x) = h(Φ⁻¹ E, 𝒪_x)`, with the article's lemma on standard words for `R(F) > 0`
  (`AlgebraicGeometry.K3.PicardRankOne.PointMassHypotheses.exists_fill`). Beyond Picard rank one
  it has to be checked for each `Φ`, and it can fail even on K3 surfaces without `(−2)`-curves: on
  one with Néron–Severi lattice `⟨2⟩ ⊕ ⟨−6⟩` the line bundles `𝒪(D)` with `D² = −4` are
  orthogonal to `𝒪_X`, so `T_{𝒪_X}` fixes them, while `h(𝒪(D), G)` is unbounded. For a standard
  `Φ` it fails already in Picard rank one. -/
  fill : ∀ E, T E → hom E G ≤ C * (μ E + μ (Φ⁻¹ • E))

namespace FillingHypotheses

variable {Obj Γ κ : Type*} [Group Γ] [MulAction Γ Obj] [Fintype κ]
  (I : FillingHypotheses Obj Γ κ)

/-! ### The orbit sums -/

/-- `H(W) = h(G, W G)`. -/
def H (W : Γ) : ℝ := I.hom I.G (W • I.G)

/-- `P(W) = Σ_k μ(W⁻¹ S_k)`: the profile on the translates of the summands. -/
def P (W : Γ) : ℝ := ∑ k, I.μ (W⁻¹ • I.S k)

/-- `h(gU, V) = h(U, g⁻¹V)`. -/
lemma hom_smul_left (g : Γ) (U V : Obj) : I.hom (g • U) V = I.hom U (g⁻¹ • V) := by
  calc I.hom (g • U) V = I.hom (g • U) (g • (g⁻¹ • V)) := by rw [smul_inv_smul]
    _ = I.hom U (g⁻¹ • V) := I.hom_smul g U _

/-- `h(G, gV) = h(g⁻¹G, V)`. -/
lemma hom_G_smul (g : Γ) (V : Obj) : I.hom I.G (g • V) = I.hom (g⁻¹ • I.G) V := by
  rw [I.hom_smul_left, inv_inv]

/-- `H(W) = Σ_k h(W⁻¹ S_k, G)`: the count from the generator on the translates of the
summands. -/
lemma H_eq_sum (W : Γ) : I.H W = ∑ k, I.hom (W⁻¹ • I.S k) I.G := by
  simp only [H, I.hom_G, I.hom_smul_left, inv_inv]

/-- `H(W) ≥ 1 > 0`. -/
lemma H_pos (W : Γ) : 0 < I.H W := lt_of_lt_of_le one_pos (I.one_le_hom_G W)

/-- `P(W) ≥ 0`. -/
lemma P_nonneg (W : Γ) : 0 ≤ I.P W := sum_nonneg fun _ _ => I.μ_nonneg _

/-- The generation bound `P(gW) ≤ K' H(g) P(W)`. -/
theorem P_mul_le (g W : Γ) : I.P (g * W) ≤ I.K' * I.H g * I.P W := I.generation g W

/-! ### Submultiplicativity and categorical entropy -/

/-- **Submultiplicativity of `H`**: `H(gW) ≤ K H(g) H(W)`, from the diagonal estimate. -/
theorem H_mul_le (g W : Γ) : I.H (g * W) ≤ I.K * I.H g * I.H W := by
  simp only [H]
  rw [mul_smul, I.hom_G_smul]
  calc I.hom (g⁻¹ • I.G) (W • I.G)
      ≤ I.K * I.hom (g⁻¹ • I.G) I.G * I.hom I.G (W • I.G) := I.hom_diag _ _
    _ = I.K * I.hom I.G (g • I.G) * I.hom I.G (W • I.G) := by
      rw [I.hom_smul_left, inv_inv]

/-- `H(Ψ^{m+n}) ≤ K H(Ψ^m) H(Ψ^n)`. -/
theorem H_pow_add_le (Ψ : Γ) (m n : ℕ) :
    I.H (Ψ ^ (m + n)) ≤ I.K * I.H (Ψ ^ m) * I.H (Ψ ^ n) := by
  rw [pow_add]
  exact I.H_mul_le _ _

/-- `H(W⁻¹) = H(W)`, by Serre duality and invariance of total `Ext`. -/
theorem H_inv (W : Γ) : I.H W⁻¹ = I.H W := by
  simp only [H]
  rw [I.hom_G_smul, inv_inv, I.hom_comm]

/-- **Categorical entropy** `h_cat(Ψ) = lim log h(G, Ψⁿ G)/n`
(Dimitrov–Haiden–Katzarkov–Kontsevich, arXiv:1307.8418, Theorem 2.6, at `t = 0`; the limit exists
by `tendsto_hcat`). -/
noncomputable def hcat (Ψ : Γ) : ℝ :=
  limUnder atTop fun n : ℕ => log (I.H (Ψ ^ n)) / n

/-- The limit defining `h_cat` exists: Fekete's lemma for `H(Ψ^{m+n}) ≤ K H(Ψ^m) H(Ψ^n)`. -/
theorem tendsto_hcat (Ψ : Γ) :
    Tendsto (fun n : ℕ => log (I.H (Ψ ^ n)) / n) atTop (𝓝 (I.hcat Ψ)) := by
  obtain ⟨ρ, hρ, -, -⟩ :=
    exists_rate_of_submul (H := fun n => I.H (Ψ ^ n)) I.K_pos (fun n => (I.H_pos _).le)
      (I.H_pow_add_le Ψ)
  have hρ1 : 1 ≤ ρ := by
    refine ge_of_tendsto hρ (Eventually.of_forall fun n => ?_)
    exact one_le_rpow (I.one_le_hom_G _) (by positivity)
  have h := tendsto_log_div_of_rpow_inv (fun n => I.H_pos (Ψ ^ n)) (by linarith) hρ
  rw [hcat, h.limUnder_eq]
  exact h

/-- `h_cat(Ψ⁻¹) = h_cat(Ψ)`. -/
theorem hcat_inv (Ψ : Γ) : I.hcat Ψ⁻¹ = I.hcat Ψ := by
  refine tendsto_nhds_unique (I.tendsto_hcat Ψ⁻¹) ?_
  refine (I.tendsto_hcat Ψ).congr fun n => ?_
  rw [inv_pow, I.H_inv]

/-- `H(Ψⁿ)^{1/n} → exp h_cat(Ψ)`. -/
theorem tendsto_H_pow (Ψ : Γ) :
    Tendsto (fun n : ℕ => I.H (Ψ ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 (exp (I.hcat Ψ))) :=
  tendsto_rpow_inv_of_log_div (fun _ => I.H_pos _) (I.tendsto_hcat Ψ)

/-! ### The filling comparison -/

/-- **The lower comparison** `ν P(W) ≤ H(W)`, for every `W`: (Dom) on each translate
`W⁻¹ S_k`. -/
theorem nu_mul_P_le_H (W : Γ) : I.ν * I.P W ≤ I.H W := by
  rw [P, mul_sum, H_eq_sum]
  exact sum_le_sum fun k _ => I.dom _ (I.T_smul _ _ (I.T_S k))

/-- `H(W) ≤ C (P(W) + P(WΦ))`, for every `W`: (Fill) on each translate `W⁻¹ S_k`, whose
translate by `Φ⁻¹` is `(WΦ)⁻¹ S_k`. -/
theorem H_le_mul_P_add (W : Γ) : I.H W ≤ I.C * (I.P W + I.P (W * I.Φ)) := by
  rw [H_eq_sum, P, P, ← sum_add_distrib, mul_sum]
  refine sum_le_sum fun k _ => ?_
  rw [mul_inv_rev, mul_smul]
  exact I.fill _ (I.T_smul _ _ (I.T_S k))

/-- The constant of (Fill) is positive: `1 ≤ H(1) ≤ C (P(1) + P(Φ))`. -/
lemma C_pos : 0 < I.C := by
  have h1 : 1 ≤ I.H 1 := I.one_le_hom_G 1
  have h2 := I.H_le_mul_P_add 1
  have h3 := I.P_nonneg 1
  have h4 := I.P_nonneg (1 * I.Φ)
  by_contra hC
  have hC' : I.C ≤ 0 := not_lt.mp hC
  nlinarith

/-- **The filling comparison** `H(W) ≤ C (1 + K' H(Φ)) P(W)` for every `W` commuting with `Φ`:
(Fill) gives `H(W) ≤ C (P(W) + P(WΦ))`, and `P(WΦ) = P(ΦW) ≤ K' H(Φ) P(W)` by the generation
bound. -/
theorem H_le_mul_P {W : Γ} (hW : Commute W I.Φ) :
    I.H W ≤ I.C * (1 + I.K' * I.H I.Φ) * I.P W := by
  have h1 := I.H_le_mul_P_add W
  have h2 : I.P (W * I.Φ) ≤ I.K' * I.H I.Φ * I.P W := by
    rw [hW.eq]
    exact I.P_mul_le I.Φ W
  have hC := I.C_pos.le
  calc I.H W ≤ I.C * (I.P W + I.P (W * I.Φ)) := h1
    _ ≤ I.C * (I.P W + I.K' * I.H I.Φ * I.P W) := by gcongr
    _ = I.C * (1 + I.K' * I.H I.Φ) * I.P W := by ring

/-- The constant `C (1 + K' H(Φ))` of the filling comparison is positive:
`1 ≤ H(1) ≤ C (1 + K' H(Φ)) P(1)`. -/
lemma C_mul_one_add_pos : 0 < I.C * (1 + I.K' * I.H I.Φ) := by
  have h1 : 1 ≤ I.H 1 := I.one_le_hom_G 1
  have h2 := I.H_le_mul_P (Commute.one_left I.Φ)
  have h3 := I.P_nonneg 1
  by_contra h
  have h' : I.C * (1 + I.K' * I.H I.Φ) ≤ 0 := not_lt.mp h
  nlinarith

/-! ### Orbit growth -/

/-- **Orbit growth of a filling profile.** For every `Ψ` commuting with `Φ`,
`P(Ψⁿ)^{1/n} → exp h_cat(Ψ)`: by the filling comparison, `P(Ψⁿ)` lies between
`H(Ψⁿ)/(C (1 + K' H(Φ)))` and `H(Ψⁿ)/ν`. -/
theorem tendsto_P_pow_of_commute {Ψ : Γ} (hΨ : Commute Ψ I.Φ) :
    Tendsto (fun n : ℕ => I.P (Ψ ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 (exp (I.hcat Ψ))) := by
  have hJ := I.C_mul_one_add_pos
  have hν := I.ν_pos
  refine tendsto_rpow_inv_of_bounds (H := fun n => I.H (Ψ ^ n)) (inv_pos.mpr hJ)
    (inv_pos.mpr hν) (fun n => (I.H_pos _).le) (Eventually.of_forall fun n => ?_)
    (Eventually.of_forall fun n => ?_) (I.tendsto_H_pow Ψ)
  · rw [inv_mul_le_iff₀ hJ]
    exact I.H_le_mul_P (hΨ.pow_left n)
  · rw [le_inv_mul_iff₀ hν]
    exact I.nu_mul_P_le_H _

/-- **Orbit growth of a filling profile along the powers of `Φ`**:
`P(Φⁿ)^{1/n} → exp h_cat(Φ)`. -/
theorem tendsto_P_pow :
    Tendsto (fun n : ℕ => I.P (I.Φ ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 (exp (I.hcat I.Φ))) :=
  I.tendsto_P_pow_of_commute (Commute.refl I.Φ)

/-- **Orbit growth of a filling profile along the negative powers of `Φ`**:
`P(Φ⁻ⁿ)^{1/n} → exp h_cat(Φ⁻¹) = exp h_cat(Φ)`. -/
theorem tendsto_P_inv_pow :
    Tendsto (fun n : ℕ => I.P (I.Φ⁻¹ ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 (exp (I.hcat I.Φ))) := by
  have h := I.tendsto_P_pow_of_commute (Commute.refl I.Φ).inv_left
  rwa [I.hcat_inv] at h

end FillingHypotheses

namespace AlgebraicGeometry.K3.PicardRankOne.PointMassHypotheses

variable {Obj Γ Stab Pt : Type*} [Group Γ] [MulAction Γ Obj] [PseudoMetricSpace Stab]
  [MulAction Γ Stab] (I : PointMassHypotheses Obj Γ Stab Pt)

/-! ### Point–profile duality -/

/-- The **point profile** `μ_x = h(-, 𝒪_x)` of a closed point `x`, as a function on objects. -/
def pointProfile (x : Pt) (E : Obj) : ℝ := I.hom E (I.point x)

/-- `μ_x(W⁻¹ E) = h(E, W 𝒪_x)`: under the arrow action `(W • μ)(E) = μ(W⁻¹ E)`, the translate by
`W` of the point profile of `𝒪_x` is the profile `h(-, W 𝒪_x)` of `W 𝒪_x` (for `ℝ≥0`-valued
profiles this is `Profile.homToProfile_smul`). -/
theorem pointProfile_smul (W : Γ) (x : Pt) (E : Obj) :
    I.pointProfile x (W⁻¹ • E) = I.hom E (W • I.point x) := by
  rw [pointProfile, I.hom_smul_left, inv_inv]

/-- On spherical objects the point profile is the rank, `μ_x(E) = R(E)`: the point test
`hom_point`. -/
theorem pointProfile_eq_rank (x : Pt) {E : Obj} (hE : I.Spherical E) :
    I.pointProfile x E = I.rank E :=
  I.hom_point E x hE

/-- **The point measurement through the point profile**: `h(G, W 𝒪_x) = Σ_k μ_x(W⁻¹ S_k)`. With
`p_eq_sum_pointProfile` this is `pointTest`, `h(G, W 𝒪_x) = Σ_k R(W⁻¹ S_k) = p(W)`: the point
measurement is the evaluation of the boundary point `R` on the translates `W⁻¹ S_k`. -/
theorem pointTest_eq_sum_pointProfile (W : Γ) (x : Pt) :
    I.hom I.G (W • I.point x) = ∑ k, I.pointProfile x (W⁻¹ • I.S k) := by
  rw [I.hom_G]
  exact sum_congr rfl fun k _ => (I.pointProfile_smul W x (I.S k)).symm

/-- `p(W) = Σ_k μ_x(W⁻¹ S_k)` at every closed point `x`: the point measurement is the point
profile on the translates of the summands. -/
theorem p_eq_sum_pointProfile (W : Γ) (x : Pt) :
    I.p W = ∑ k, I.pointProfile x (W⁻¹ • I.S k) :=
  sum_congr rfl fun k _ =>
    (I.pointProfile_eq_rank x (I.spherical_smul _ _ (I.spherical_S k))).symm

/-! ### The point-mass instance -/

/-- **The generation bound for the rank**: `p(gW) ≤ K H(g) p(W)`. By the point measurement and the
diagonal estimate, `p(gW) = h(G, gW 𝒪_x) = h(g⁻¹ G, W 𝒪_x) ≤ K h(g⁻¹ G, G) h(G, W 𝒪_x)
= K H(g) p(W)`. -/
theorem p_mul_le [Nonempty Pt] (g W : Γ) : I.p (g * W) ≤ I.K * I.H g * I.p W := by
  obtain ⟨x⟩ := ‹Nonempty Pt›
  rw [← I.pointTest (g * W) x, ← I.pointTest W x, mul_smul, I.hom_G_smul]
  calc I.hom (g⁻¹ • I.G) (W • I.point x)
      ≤ I.K * I.hom (g⁻¹ • I.G) I.G * I.hom I.G (W • I.point x) := I.hom_diag _ _
    _ = I.K * I.H g * I.hom I.G (W • I.point x) := by
      rw [I.hom_smul_left, inv_inv]
      rfl

/-- **(Fill) for the rank in Picard rank one.** For a nonstandard `Φ` there is `C ≥ 0` with
`h(E, G) ≤ C (R(E) + R(Φ⁻¹ E))` for every spherical `E`: the article's fixed-object test
(`fixedTest`) at `F = Φ 𝒪_x`, where `R(F) > 0` by its lemma on standard words
(`standard_of_rank_zero`) and
`h(E, Φ 𝒪_x) = μ_x(Φ⁻¹ E) = R(Φ⁻¹ E)` by point–profile duality. -/
theorem exists_fill [Nonempty Pt] (Φ : Γ) (hΦ : ¬ I.Standard Φ) :
    ∃ C, 0 ≤ C ∧ ∀ E, I.Spherical E → I.hom E I.G ≤ C * (I.rank E + I.rank (Φ⁻¹ • E)) := by
  obtain ⟨x⟩ := ‹Nonempty Pt›
  have hF : 0 < I.rank (Φ • I.point x) := lt_of_le_of_ne (I.rank_nonneg _)
    fun h => hΦ (I.standard_of_rank_zero Φ x h.symm)
  obtain ⟨C, hC, hCF⟩ := I.fixedTest _ hF
  refine ⟨C, hC, fun E hE => ?_⟩
  rw [← I.pointProfile_eq_rank x (I.spherical_smul Φ⁻¹ E hE), I.pointProfile_smul]
  exact hCF E hE

/-- **The point-mass instance of the filling theorem.** For a nonstandard `Φ`, the inputs of the
point-mass corollary give inputs of the filling theorem: the profile is the rank `μ = R` (the
point profile `h(-, 𝒪_x)` on spherical objects, `pointProfile_eq_rank`), the test class is the
spherical objects, `K' = K` (`p_mul_le`), (Dom) is `nu_rank_le` and (Fill) is the article's
fixed-object test (`exists_fill`). Its orbit sum `P` is the point measurement `p`. -/
noncomputable def toFillingHypotheses (Φ : Γ) (hΦ : ¬ I.Standard Φ) [Nonempty Pt] :
    FillingHypotheses Obj Γ (Fin 3) where
  hom := I.hom
  hom_nonneg := I.hom_nonneg
  hom_comm := I.hom_comm
  hom_smul := I.hom_smul
  G := I.G
  S := I.S
  hom_G := I.hom_G
  K := I.K
  K_pos := I.K_pos
  hom_diag := I.hom_diag
  one_le_hom_G := I.one_le_hom_G
  μ := I.rank
  μ_nonneg := I.rank_nonneg
  T := I.Spherical
  T_S := I.spherical_S
  T_smul := I.spherical_smul
  K' := I.K
  generation := I.p_mul_le
  ν := I.ν
  ν_pos := I.ν_pos
  dom := I.nu_rank_le
  Φ := Φ
  C := (I.exists_fill Φ hΦ).choose
  fill := (I.exists_fill Φ hΦ).choose_spec.2

section Instance

variable [Nonempty Pt] (Φ : Γ) (hΦ : ¬ I.Standard Φ)

/-- The orbit sum of the point-mass instance is the point measurement `p`. -/
lemma toFillingHypotheses_P (W : Γ) : (I.toFillingHypotheses Φ hΦ).P W = I.p W := rfl

/-- The count `H` of the point-mass instance is `H(W) = h(G, W G)`. -/
lemma toFillingHypotheses_H (W : Γ) : (I.toFillingHypotheses Φ hΦ).H W = I.H W := rfl

/-- The categorical entropy of the point-mass instance is `h_cat`. -/
lemma toFillingHypotheses_hcat (Ψ : Γ) : (I.toFillingHypotheses Φ hΦ).hcat Ψ = I.hcat Ψ := rfl

end Instance

/-- **Comparison for a fixed period, from the filling theorem.** For a nonstandard `Φ` there is
`J > 0` with `H(W) ≤ J p(W)` for every `W` commuting with `Φ`: the filling comparison of the
point-mass instance, with `J = C (1 + K H(Φ))`. This re-derives the article's comparison for a
fixed period (`exists_H_le_mul_p`) from the filling theorem. -/
theorem exists_H_le_mul_p_of_filling [Nonempty Pt] (Φ : Γ) (hΦ : ¬ I.Standard Φ) :
    ∃ J > 0, ∀ W : Γ, Commute W Φ → I.H W ≤ J * I.p W :=
  ⟨_, (I.toFillingHypotheses Φ hΦ).C_mul_one_add_pos,
    fun _ hW => (I.toFillingHypotheses Φ hΦ).H_le_mul_P hW⟩

/-- **The point measurement along the powers of a nonstandard word**, from the filling theorem:
`p(Φⁿ)^{1/n} → exp h_cat(Φ)`. -/
theorem tendsto_p_pow [Nonempty Pt] (Φ : Γ) (hΦ : ¬ I.Standard Φ) :
    Tendsto (fun n : ℕ => I.p (Φ ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 (exp (I.hcat Φ))) :=
  (I.toFillingHypotheses Φ hΦ).tendsto_P_pow

/-- **The point measurement along the negative powers of a nonstandard word**, from the filling
theorem: `p(Φ⁻ⁿ)^{1/n} → exp h_cat(Φ)`. -/
theorem tendsto_p_inv_pow [Nonempty Pt] (Φ : Γ) (hΦ : ¬ I.Standard Φ) :
    Tendsto (fun n : ℕ => I.p (Φ⁻¹ ^ n) ^ (n : ℝ)⁻¹) atTop (𝓝 (exp (I.hcat Φ))) :=
  (I.toFillingHypotheses Φ hΦ).tendsto_P_inv_pow

/-! ### A fixed point has entropy zero -/

/-- **A fixed point has entropy zero.** If `Φ 𝒪_x = 𝒪_x`, then `h_cat(Φ) = 0`: the masses
`m_σ(Φⁿ 𝒪_x) = m_σ(𝒪_x) > 0` are constant, so their `n`-th roots tend to `1`, while by the
point-mass corollary (`tendsto_pointMass`) they tend to `exp h_cat(Φ)`. This is the statement
inside the rank-one structure behind the failure of the point-mass corollary on K3 surfaces with
`(−2)`-curves; it is not a statement beyond Picard rank one. -/
theorem hcat_eq_zero_of_smul_point_eq {Φ : Γ} {x : Pt} (h : Φ • I.point x = I.point x) :
    I.hcat Φ = 0 := by
  have : Nonempty Pt := ⟨x⟩
  have hpow : ∀ n : ℕ, Φ ^ n • I.point x = I.point x := fun n => by
    induction n with
    | zero => rw [pow_zero, one_smul]
    | succ n ih => rw [pow_succ, mul_smul, h, ih]
  have hm : 0 < I.mass I.τ (I.point x) := by
    simpa using I.mass_pos I.τ 1 x
  have hconst : Tendsto (fun n : ℕ => I.mass I.τ (Φ ^ n • I.point x) ^ (n : ℝ)⁻¹) atTop
      (𝓝 1) := by
    simp only [hpow]
    exact tendsto_const_rpow_inv hm
  exact (exp_eq_one_iff _).mp (tendsto_nhds_unique (I.tendsto_pointMass Φ x I.τ) hconst)

end AlgebraicGeometry.K3.PicardRankOne.PointMassHypotheses
