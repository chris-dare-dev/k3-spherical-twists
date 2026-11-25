/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Complex.Sector
import K3Twists.LinearAlgebra.Lattice.Mukai.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# The support property on the real Mukai lattice

Let `V` be a finite-dimensional real normed space with a bilinear form `B`, `q(v) = B v v`, and
let `Z : V →ₗ[ℝ] W` be a charge. The classes are a set `Γ ⊆ V` with finitely many points in every
ball (`∀ R, {v ∈ Γ | ‖v‖ ≤ R}` finite), as the image of an integral lattice is. The case of
interest is the real Mukai lattice `V = MukaiLattice ℝ E` of a finite-dimensional real quadratic
space `(E, b)`, with `B = mukaiForm b` and `Γ` the image of an integral Mukai lattice
`MukaiLattice ℤ N` along a real model `N → E` (`Mukai.realModel`).

## The support property

`SupportProperty Z S D` says `‖v‖ ≤ D ‖Z v‖` for every `v ∈ S`: the support property of
Kontsevich and Soibelman (arXiv:0811.2435).

* `SupportProperty.finite_norm_le`: under the support property only finitely many classes of `Γ`
  have `‖Z v‖ ≤ M`.
* `exists_finsler`, **Finsler's lemma** (P. Finsler, Comment. Math. Helv. 9, 1937): if `q < 0`
  on `ker Z ∖ 0`, there are `ε > 0` and `C` with `q(v) ≤ -ε ‖v‖² + C ‖Z v‖²` for every
  `v`. This is the compactness step: on classes with `q ≥ -2` it gives
  `ε ‖v‖² ≤ 2 + C ‖Z v‖²`.
* `exists_supportProperty`: if `ker Z` is negative definite and **no class of `Γ` with
  `q ≥ -2` lies in `ker Z`**, the support property holds on `{v ∈ Γ | q(v) ≥ -2}`. The
  homogeneous bound needs a discreteness step: the classes too short for the compactness bound
  are finitely many, and none is in `ker Z`.
* `not_supportProperty_of_mem_ker`: the second hypothesis is necessary for any constant `D`. It is
  necessary for a constant `D` and for estimates whose only input is `D`; through root
  hyperplanes the punctured form of the support bound applies instead.
* `exists_finsler_ball`, `exists_punctured_supportBound`, **the punctured support bound**: at a
  charge `Z₀` with negative-definite kernel there are `η > 0` and `K` with `‖v‖ ≤ K ‖Z v‖` for
  every charge `Z` with `‖Z - Z₀‖ < η` and every class of `Γ` with `q(v) ≥ -2` and `Z₀ v ≠ 0`,
  that is, off the roots `R_*` of the kernel. So the only root hyperplanes meeting the ball are
  those of `R_*` (`exists_ball_ker_subset`). `exists_supportProperty` is proved as its case
  `R_* = ∅`, at `Z = Z₀`.
* `negDef_orthogonal_of_posPlane`, **signature `(2, n)`**: if `B` is symmetric and nondegenerate
  with no positive-definite subspace of dimension `3` (`sigPos ≤ 2`), the orthogonal complement
  of a positive-definite plane is negative definite. So the kernel of the charge
  `v ↦ B(Ω₁, v) + i B(Ω₂, v)` of a positive period is negative definite
  (`negDef_ker_realCharge`).
* `card_mul_cos_le_of_sector`: **stable constituents in a strict sector.** If classes `v_i` of
  norm at least `μ` with the support property have charges in the sector of phase `φ` and
  half-width `b ≤ 1/2`, their number `k` satisfies `k μ cos(πb) ≤ D p_φ(Σ v_i)`, and each has
  `‖v_i‖ cos(πb) ≤ D p_φ(Σ v_i)`.

## The completed square and the root test

On the real Mukai lattice of `(E, b)`, with `H ∈ E`, `b(H, H) = h > 0`, `β ⊥ H`, real `x` and `a`,
the **normalized charge** is

```
Z(r, c, s) = x r - s + b(β, c) + i (b(H, c) - a r)            (normalizedCharge),
```

the charge `⟪Ω₁, -⟫ + i ⟪Ω₂, -⟫` with `Ω₁ = (1, β, -x)`, `Ω₂ = (0, H, a)`. Put
`δ = 2x + b(β, β) - a²/h`; for `h > 0` the charge plane is positive exactly when `δ > 0`. For a
root `v = (r, c, s)` (`⟪v, v⟫ = -2`) with `r ≠ 0` and `Im Z(v) = 0`, that is `b(H, c) = a r`,
write `c/r = (a/h) H + u` with `u ⊥ H`. Then (`re_normalizedCharge_div_rank`, the
**completed square**)

```
Re Z(v) / r = δ/2 - b(u - β, u - β)/2 - 1/r².
```

If `b` is negative semidefinite on `H^⊥` (the Hodge index theorem on a Néron–Severi lattice), a
root of positive rank with `Im Z = 0` and `Re Z ≤ 0` has `r² ≤ 2/δ` and
`-b(u - β, u - β) ≤ 2/r² - δ` (`rank_sq_le_of_re_nonpos`, `neg_le_of_re_nonpos`), and
`0 < Re Z` for every such root once `δ > 2` (`re_normalizedCharge_pos`). If `b` is negative
definite on `H^⊥`, the violating roots of rank at least one in `Γ` are finitely many
(`finite_violations`): **the root test** for the chamber of a fixed imaginary part, a finite
search over the ranks `r² ≤ 2/δ` and the ellipsoids `-b(u - β, u - β) ≤ 2/r² - δ`. In Picard
rank one `u = β = 0`, and the completed square is the height `1/(dr²)` of a puncture
(`AlgebraicGeometry.K3.PicardRankOne.height_puncture`); `finite_obstacles` there is its
rank-one shadow.

## The real model

`realModel f : MukaiLattice ℤ N →ₗ[ℤ] MukaiLattice ℝ E`, `(r, c, s) ↦ (r, f c, s)`, for a
`ℤ`-linear `f : N → E`. If `b_E(f x, f y) = b(x, y)` it preserves the Mukai form
(`pairing_realModel`), and if `f` has finitely many points in every ball so does the image
(`finite_realModel_norm_le`), the hypothesis on `Γ` above.
-/

open Real

namespace Mukai

section Finsler

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedAddCommGroup V] in
/-- `B (t • v) (t • v) = t² B v v`. -/
theorem bilinForm_smul_smul [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V) (t : ℝ)
    (v : V) : B (t • v) (t • v) = t ^ 2 * B v v := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- A unit vector in the direction of `v ≠ 0`, and `v` as its multiple. -/
private theorem eq_norm_smul_unit {v : V} (hv : v ≠ 0) :
    ‖‖v‖⁻¹ • v‖ = 1 ∧ v = ‖v‖ • (‖v‖⁻¹ • v) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

variable [FiniteDimensional ℝ V]

/-- A bilinear form on a finite-dimensional real normed space is continuous on the diagonal. -/
theorem continuous_bilinForm_apply_self (B : LinearMap.BilinForm ℝ V) :
    Continuous fun v => B v v := by
  let B' : V →ₗ[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B
  exact (LinearMap.continuous_of_finiteDimensional B').clm_apply continuous_id

/-- A bilinear form is bounded on the diagonal: `|B v v| ≤ M ‖v‖²`. -/
theorem exists_abs_bilinForm_le (B : LinearMap.BilinForm ℝ V) :
    ∃ M ≥ 0, ∀ v, |B v v| ≤ M * ‖v‖ ^ 2 := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : V) 1).exists_bound_of_continuousOn
    (continuous_bilinForm_apply_self B).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨hu, hvu⟩ := eq_norm_smul_unit hv
  have h1 := hM _ (mem_sphere_zero_iff_norm.mpr hu)
  rw [Real.norm_eq_abs] at h1
  have key : ∀ (t : ℝ) (w : V), 0 ≤ t → |B w w| ≤ M → ‖w‖ = 1 →
      |B (t • w) (t • w)| ≤ max M 0 * ‖t • w‖ ^ 2 := by
    intro t w ht hw hn
    rw [bilinForm_smul_smul, abs_mul, norm_smul, Real.norm_of_nonneg ht, hn, mul_one,
      abs_of_nonneg (sq_nonneg t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hw.trans (le_max_left _ _)) (sq_nonneg t)
  have := key ‖v‖ _ (norm_nonneg _) h1 hu
  rwa [← hvu] at this

/-- **Finsler's lemma.** If `B v v < 0` for every nonzero `v` in the kernel of `Z`, there are
`ε > 0` and `C ≥ 0` with `B v v ≤ -ε ‖v‖² + C ‖Z v‖²` for every `v`.

Proof: `max(‖Z v‖², -B v v)` is positive on the unit sphere, so at least some `ε > 0` there
(compactness); where `‖Z v‖² ≥ ε` the bound `|B v v| ≤ M` is absorbed by `C = (M + ε)/ε`, and
elsewhere `B v v ≤ -ε`. Homogeneity extends the bound from the sphere. -/
theorem exists_finsler (B : LinearMap.BilinForm ℝ V) (Z : V →ₗ[ℝ] W)
    (hB : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ v, B v v ≤ -ε * ‖v‖ ^ 2 + C * ‖Z v‖ ^ 2 := by
  set S := Metric.sphere (0 : V) 1
  have hS : IsCompact S := isCompact_sphere 0 1
  have hZc : Continuous fun v => ‖Z v‖ ^ 2 :=
    ((LinearMap.continuous_of_finiteDimensional Z).norm).pow 2
  have hqc := continuous_bilinForm_apply_self B
  -- the bound on the unit sphere
  have hunit : ∃ ε > 0, ∃ C ≥ 0, ∀ v ∈ S, B v v ≤ -ε + C * ‖Z v‖ ^ 2 := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · refine ⟨1, one_pos, 0, le_rfl, fun v hv => ?_⟩
      rw [hSe] at hv
      exact absurd hv (Set.notMem_empty _)
    obtain ⟨v₀, hv₀, hmin⟩ := hS.exists_isMinOn hSne
      (hZc.max hqc.neg).continuousOn
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hqc.continuousOn
    have hpos : ∀ v ∈ S, 0 < max (‖Z v‖ ^ 2) (-B v v) := by
      intro v hv
      have hv0 : v ≠ 0 := ne_zero_of_mem_unit_sphere ⟨v, hv⟩
      by_cases hZ : Z v = 0
      · exact lt_max_of_lt_right (neg_pos.mpr (hB v hZ hv0))
      · exact lt_max_of_lt_left (by positivity)
    set ε := max (‖Z v₀‖ ^ 2) (-B v₀ v₀)
    have hε : 0 < ε := hpos v₀ hv₀
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM v₀ hv₀)
    refine ⟨ε, hε, (M + ε) / ε, by positivity, fun v hv => ?_⟩
    have hle : ε ≤ max (‖Z v‖ ^ 2) (-B v v) := hmin hv
    have hqM : B v v ≤ M := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hM v hv)
    rcases le_max_iff.mp hle with h | h
    · have : (M + ε) / ε * ε ≤ (M + ε) / ε * ‖Z v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h (by positivity)
      rw [div_mul_cancel₀ _ hε.ne'] at this
      linarith
    · have : 0 ≤ (M + ε) / ε * ‖Z v‖ ^ 2 := by positivity
      linarith
  obtain ⟨ε, hε, C, hC, hbound⟩ := hunit
  refine ⟨ε, hε, C, hC, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨hu, hvu⟩ := eq_norm_smul_unit hv
  have h1 := hbound _ (mem_sphere_zero_iff_norm.mpr hu)
  have key : ∀ (t : ℝ) (w : V), 0 ≤ t → B w w ≤ -ε + C * ‖Z w‖ ^ 2 → ‖w‖ = 1 →
      B (t • w) (t • w) ≤ -ε * ‖t • w‖ ^ 2 + C * ‖Z (t • w)‖ ^ 2 := by
    intro t w ht hw hn
    rw [bilinForm_smul_smul, map_smul, norm_smul, norm_smul, Real.norm_of_nonneg ht, hn,
      mul_one, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg t)]
  have := key ‖v‖ _ (norm_nonneg _) h1 hu
  rwa [← hvu] at this

end Finsler

/-! ### The support property -/

section SupportProperty

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]

/-- **The support property** with constant `D` for the charge `Z` on the classes `S`:
`‖v‖ ≤ D ‖Z v‖` for every `v ∈ S`. -/
def SupportProperty (Z : V → W) (S : Set V) (D : ℝ) : Prop :=
  ∀ v ∈ S, ‖v‖ ≤ D * ‖Z v‖

theorem SupportProperty.mono {Z : V → W} {S S' : Set V} {D : ℝ} (h : SupportProperty Z S D)
    (hS : S' ⊆ S) : SupportProperty Z S' D :=
  fun v hv => h v (hS hv)

theorem SupportProperty.mono_const {Z : V → W} {S : Set V} {D D' : ℝ}
    (h : SupportProperty Z S D) (hD : D ≤ D') : SupportProperty Z S D' :=
  fun v hv => (h v hv).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))

/-- The support property transfers along a comparison of charges: if `‖Z v‖ ≤ K ‖Z' v‖` on `S`
and `D ≥ 0`, the support property of `Z` with constant `D` gives that of `Z'` with `D K`. -/
theorem SupportProperty.of_norm_le {W' : Type*} [NormedAddCommGroup W'] {Z : V → W} {Z' : V → W'}
    {S : Set V} {D K : ℝ} (h : SupportProperty Z S D) (hD : 0 ≤ D)
    (hK : ∀ v ∈ S, ‖Z v‖ ≤ K * ‖Z' v‖) : SupportProperty Z' S (D * K) :=
  fun v hv => (h v hv).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hK v hv) hD)

/-- **Finiteness from the support property.** If the classes `S` lie in a set `Γ` with finitely
many points in every ball, only finitely many of them have `‖Z v‖ ≤ M`. -/
theorem SupportProperty.finite_norm_le {Z : V → W} {S Γ : Set V} {D : ℝ}
    (h : SupportProperty Z S D) (hSΓ : S ⊆ Γ) (hΓ : ∀ R : ℝ, {v | v ∈ Γ ∧ ‖v‖ ≤ R}.Finite)
    (M : ℝ) : {v | v ∈ S ∧ ‖Z v‖ ≤ M}.Finite := by
  refine (hΓ (max D 0 * M)).subset fun v ⟨hv, hZ⟩ => ⟨hSΓ hv, ?_⟩
  calc ‖v‖ ≤ D * ‖Z v‖ := h v hv
    _ ≤ max D 0 * ‖Z v‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max D 0 * M := mul_le_mul_of_nonneg_left hZ (le_max_right _ _)

/-- **The kernel condition is necessary.** A nonzero class of `S` in the kernel of `Z` violates
the support property for every constant `D`. -/
theorem not_supportProperty_of_mem_ker {Z : V → W} {S : Set V} {v : V} (hv : v ∈ S)
    (hv0 : v ≠ 0) (hZ : Z v = 0) (D : ℝ) : ¬SupportProperty Z S D := by
  intro h
  have := h v hv
  rw [hZ, norm_zero, mul_zero] at this
  exact hv0 (norm_le_zero_iff.mp this)

end SupportProperty

section Punctured

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Finsler's bound on a ball of charges.** If `B` is negative definite on the kernel of `Z₀`,
there are `ε, η > 0` and `C ≥ 0` with `B v v ≤ -ε ‖v‖² + C ‖Z v‖²` for every `v` and every charge
`Z` with `‖Z - Z₀‖ ≤ η`. -/
theorem exists_finsler_ball (B : LinearMap.BilinForm ℝ V) (Z₀ : V →L[ℝ] W)
    (hB : ∀ v, Z₀ v = 0 → v ≠ 0 → B v v < 0) :
    ∃ ε > 0, ∃ η > 0, ∃ C ≥ 0, ∀ Z : V →L[ℝ] W, ‖Z - Z₀‖ ≤ η →
      ∀ v, B v v ≤ -ε * ‖v‖ ^ 2 + C * ‖Z v‖ ^ 2 := by
  obtain ⟨ε, hε, C, hC, hF⟩ := exists_finsler B (Z₀ : V →ₗ[ℝ] W) hB
  set η := min 1 (ε / (4 * C + 1))
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : 2 * C * η ^ 2 ≤ ε / 2 := by
    have h1 : η ^ 2 ≤ η := by nlinarith
    have h2 : η ≤ ε / (4 * C + 1) := min_le_right _ _
    have h3 : 2 * C * (ε / (4 * C + 1)) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0 : ℝ) ≤ 2 * C)]
  refine ⟨ε / 2, by positivity, η, hη, 2 * C, by positivity, fun Z hZ v => ?_⟩
  have h1 : ‖Z₀ v‖ ≤ ‖Z v‖ + η * ‖v‖ := by
    have : ‖(Z₀ - Z) v‖ ≤ η * ‖v‖ :=
      ((Z₀ - Z).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (by rwa [norm_sub_rev]) (norm_nonneg _))
    calc ‖Z₀ v‖ = ‖Z v + (Z₀ - Z) v‖ := by simp
      _ ≤ ‖Z v‖ + ‖(Z₀ - Z) v‖ := norm_add_le _ _
      _ ≤ ‖Z v‖ + η * ‖v‖ := by linarith
  have h2 : ‖Z₀ v‖ ^ 2 ≤ 2 * ‖Z v‖ ^ 2 + 2 * η ^ 2 * ‖v‖ ^ 2 := by
    have h0 : 0 ≤ ‖Z₀ v‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖Z v‖ - η * ‖v‖)]
  have h3 := hF v
  change B v v ≤ -ε * ‖v‖ ^ 2 + C * ‖Z₀ v‖ ^ 2 at h3
  nlinarith [mul_le_mul_of_nonneg_left h2 hC, sq_nonneg ‖v‖]

/-- **The punctured support bound.** Let `B` be negative definite on the kernel of a charge `Z₀`,
and let the classes `Γ` have finitely many points in every ball. There are `η > 0` and `K` such
that `‖v‖ ≤ K ‖Z v‖` for every charge `Z` with `‖Z - Z₀‖ < η` and every class `v ∈ Γ` with
`B v v ≥ -2` and `Z₀ v ≠ 0`. In particular the only classes of `Γ` with `B v v ≥ -2` whose charge
vanishes somewhere on the ball are those with `Z₀ v = 0`: at a stratum, the roots `R_*` of the
kernel.

Proof: Finsler's bound on a ball handles the long classes; the short classes are finitely many,
and those with `Z₀ v ≠ 0` keep `‖Z v‖ ≥ min ‖Z₀ v‖/2` on a small enough ball. -/
theorem exists_punctured_supportBound (B : LinearMap.BilinForm ℝ V) (Z₀ : V →L[ℝ] W)
    (hB : ∀ v, Z₀ v = 0 → v ≠ 0 → B v v < 0) {Γ : Set V}
    (hΓ : ∀ R : ℝ, {v | v ∈ Γ ∧ ‖v‖ ≤ R}.Finite) :
    ∃ η > 0, ∃ K, ∀ Z : V →L[ℝ] W, ‖Z - Z₀‖ < η →
      ∀ v ∈ Γ, -2 ≤ B v v → Z₀ v ≠ 0 → ‖v‖ ≤ K * ‖Z v‖ := by
  obtain ⟨ε, hε, η₁, hη₁, C, hC, hF⟩ := exists_finsler_ball B Z₀ hB
  set R := max 1 (4 / ε)
  have hR : 1 ≤ R := le_max_left _ _
  -- the short classes off the kernel of `Z₀`
  set F := {v | v ∈ Γ ∧ ‖v‖ ≤ R ∧ Z₀ v ≠ 0}
  have hFfin : F.Finite := (hΓ R).subset fun v hv => ⟨hv.1, hv.2.1⟩
  obtain ⟨m, hm, hmle⟩ : ∃ m > 0, ∀ v ∈ F, m ≤ ‖Z₀ v‖ := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · exact ⟨1, one_pos, fun v hv => by rw [hFe] at hv; exact absurd hv (Set.notMem_empty _)⟩
    · obtain ⟨v₀, hv₀, hmin⟩ := Set.exists_min_image F (fun v => ‖Z₀ v‖) hFfin hFne
      exact ⟨‖Z₀ v₀‖, norm_pos_iff.mpr hv₀.2.2, hmin⟩
  set η₂ := m / (2 * R)
  have hη₂ : 0 < η₂ := by positivity
  set D₁ := Real.sqrt (2 * C / ε)
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, max D₁ (2 * R / m), fun Z hZ v hvΓ hv2 hZ₀ => ?_⟩
  have hZ₁ : ‖Z - Z₀‖ ≤ η₁ := hZ.le.trans (min_le_left _ _)
  have hZ₂ : ‖Z - Z₀‖ ≤ η₂ := hZ.le.trans (min_le_right _ _)
  by_cases hvR : ‖v‖ ≤ R
  · -- a short class: its charge stays away from zero on the ball
    have hmv := hmle v ⟨hvΓ, hvR, hZ₀⟩
    have hdiff : ‖(Z - Z₀) v‖ ≤ m / 2 := by
      calc ‖(Z - Z₀) v‖ ≤ ‖Z - Z₀‖ * ‖v‖ := (Z - Z₀).le_opNorm v
        _ ≤ η₂ * R := mul_le_mul hZ₂ hvR (norm_nonneg _) hη₂.le
        _ = m / 2 := by simp only [η₂]; field_simp
    have hZv : m / 2 ≤ ‖Z v‖ := by
      have : ‖Z₀ v‖ ≤ ‖Z v‖ + ‖(Z - Z₀) v‖ := by
        calc ‖Z₀ v‖ = ‖Z v - (Z - Z₀) v‖ := by simp
          _ ≤ ‖Z v‖ + ‖(Z - Z₀) v‖ := norm_sub_le _ _
      linarith
    calc ‖v‖ ≤ R := hvR
      _ = 2 * R / m * (m / 2) := by field_simp
      _ ≤ 2 * R / m * ‖Z v‖ := mul_le_mul_of_nonneg_left hZv (by positivity)
      _ ≤ max D₁ (2 * R / m) * ‖Z v‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · -- a long class: Finsler's bound is homogeneous
    push Not at hvR
    have h1 : 1 < ‖v‖ := hR.trans_lt hvR
    have h4 : 4 / ε < ‖v‖ ^ 2 := by
      have : 4 / ε < ‖v‖ := (le_max_right _ _).trans_lt hvR
      nlinarith
    have h4' : 4 < ε * ‖v‖ ^ 2 := by rwa [div_lt_iff₀' hε] at h4
    have hsq : ‖v‖ ^ 2 ≤ 2 * C / ε * ‖Z v‖ ^ 2 := by
      have := hF Z hZ₁ v
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]
      nlinarith
    have hD₁ : ‖v‖ ≤ D₁ * ‖Z v‖ := by
      have hc : 0 ≤ 2 * C / ε := by positivity
      rw [← abs_norm v, ← abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg (Z v)))]
      apply sq_le_sq.mp
      rw [mul_pow, Real.sq_sqrt hc]
      exact hsq
    exact hD₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- **Root hyperplanes near a period.** Under the hypotheses of the punctured support bound, a
class of `Γ` with `B v v ≥ -2` whose charge vanishes for some `Z` near `Z₀` is in the kernel of
`Z₀`: the only root hyperplanes meeting a small ball around `Z₀` are those of `R_*`. -/
theorem exists_ball_ker_subset (B : LinearMap.BilinForm ℝ V) (Z₀ : V →L[ℝ] W)
    (hB : ∀ v, Z₀ v = 0 → v ≠ 0 → B v v < 0) {Γ : Set V}
    (hΓ : ∀ R : ℝ, {v | v ∈ Γ ∧ ‖v‖ ≤ R}.Finite) :
    ∃ η > 0, ∀ Z : V →L[ℝ] W, ‖Z - Z₀‖ < η →
      ∀ v ∈ Γ, -2 ≤ B v v → Z v = 0 → Z₀ v = 0 := by
  obtain ⟨η, hη, K, hK⟩ := exists_punctured_supportBound B Z₀ hB hΓ
  refine ⟨η, hη, fun Z hZ v hvΓ hv2 hZv => ?_⟩
  by_contra hZ₀
  have := hK Z hZ v hvΓ hv2 hZ₀
  rw [hZv, norm_zero, mul_zero] at this
  exact hZ₀ (by rw [norm_le_zero_iff.mp this, map_zero])

end Punctured

section Existence

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **The support property from a negative-definite kernel.** If `B` is negative definite on the
kernel of `Z`, the classes `Γ` have finitely many points in every ball, and no nonzero class of
`Γ` with `B v v ≥ -2` lies in the kernel of `Z`, then the support property holds on the classes
of `Γ` with `B v v ≥ -2`.

This is the punctured support bound (`exists_punctured_supportBound`) at `Z = Z₀` when the root
set `R_*` of the kernel is empty. -/
theorem exists_supportProperty (B : LinearMap.BilinForm ℝ V) (Z : V →ₗ[ℝ] W)
    (hB : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) {Γ : Set V}
    (hΓ : ∀ R : ℝ, {v | v ∈ Γ ∧ ‖v‖ ≤ R}.Finite)
    (hZ : ∀ v ∈ Γ, v ≠ 0 → -2 ≤ B v v → Z v ≠ 0) :
    ∃ D, SupportProperty Z {v | v ∈ Γ ∧ -2 ≤ B v v} D := by
  set Z' : V →L[ℝ] W := LinearMap.toContinuousLinearMap Z
  obtain ⟨η, hη, K, hK⟩ := exists_punctured_supportBound B Z' hB hΓ
  refine ⟨K, fun v ⟨hvΓ, hv2⟩ => ?_⟩
  by_cases hv0 : v = 0
  · simp [hv0]
  exact hK Z' (by rwa [sub_self, norm_zero]) v hvΓ hv2 (hZ v hvΓ hv0 hv2)

end Existence

/-! ### Signature `(2, n)` -/

section Signature

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A family of `n` vectors on whose nonzero combinations `B` is positive spans a
positive-definite subspace of dimension `n`, so `n ≤ sigPos`. -/
theorem le_sigPos_of_forall_pos (B : LinearMap.BilinForm ℝ V) {n : ℕ} (v : Fin n → V)
    (h : ∀ g : Fin n → ℝ, g ≠ 0 → 0 < B (∑ i, g i • v i) (∑ i, g i • v i)) :
    n ≤ sigPos B.toQuadraticMap := by
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    have hg0 : g ≠ 0 := fun h0 => hi (congrFun h0 i)
    have := h g hg0
    rw [hg] at this
    simp at this
  have hpd : (B.toQuadraticMap.restrict (Submodule.span ℝ (Set.range v))).PosDef := by
    rintro ⟨x, hx⟩ hx0
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
    have hg0 : g ≠ 0 := by
      rintro rfl
      apply hx0
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hg
      exact Subtype.ext hg.symm
    have := h g hg0
    rw [hg] at this
    simpa [QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply] using this
  have := le_sigPos_of_posDef B.toQuadraticMap hpd
  rwa [finrank_span_eq_card hli, Fintype.card_fin] at this

/-- **Signature `(2, n)`: the orthogonal complement of a positive plane is negative definite.**
Let `B` be symmetric and nondegenerate with no positive-definite subspace of dimension three
(`sigPos ≤ 2`), and let `Ω₁`, `Ω₂` span a positive-definite plane. Then `B w w < 0` for every
nonzero `w` orthogonal to `Ω₁` and `Ω₂`.

Proof: a positive `w` would make the plane and `w` a positive-definite `3`-space; so the
complement is negative semidefinite, and an isotropic `w ≠ 0` in it pairs nontrivially with some
`y` (nondegeneracy), whose projection `y'` to the complement gives `B(w + t y', w + t y') > 0`
for a small `t` of the right sign. -/
theorem negDef_orthogonal_of_posPlane (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hnd : ∀ w, (∀ y, B w y = 0) → w = 0)
    (hsig : sigPos B.toQuadraticMap ≤ 2) {Ω₁ Ω₂ : V}
    (hΩ : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < B (a • Ω₁ + b • Ω₂) (a • Ω₁ + b • Ω₂))
    {w : V} (h₁ : B Ω₁ w = 0) (h₂ : B Ω₂ w = 0) (hw : w ≠ 0) : B w w < 0 := by
  -- the complement is negative semidefinite
  have hsemi : ∀ y, B Ω₁ y = 0 → B Ω₂ y = 0 → B y y ≤ 0 := by
    intro y hy₁ hy₂
    by_contra hpos
    push Not at hpos
    have h3 := le_sigPos_of_forall_pos B ![Ω₁, Ω₂, y] fun g hg => by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      set p := g 0 • Ω₁ + g 1 • Ω₂
      have hpy : B p y = 0 := by
        simp only [p, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hy₁, hy₂,
          smul_eq_mul, mul_zero, add_zero]
      have hyp : B y p = 0 := by rw [hB]; exact hpy
      have expand : B (p + g 2 • y) (p + g 2 • y) = B p p + g 2 ^ 2 * B y y := by
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hpy, hyp]
        ring
      rw [expand]
      by_cases h01 : g 0 ≠ 0 ∨ g 1 ≠ 0
      · have := hΩ (g 0) (g 1) h01
        nlinarith [sq_nonneg (g 2)]
      · push Not at h01
        have h2 : g 2 ≠ 0 := by
          intro h2
          apply hg
          funext i
          fin_cases i <;> simp [h01.1, h01.2, h2]
        have hp0 : p = 0 := by simp [p, h01.1, h01.2]
        simp only [hp0, map_zero, zero_add]
        have : 0 < g 2 ^ 2 := by positivity
        positivity
    omega
  refine lt_of_le_of_ne (hsemi w h₁ h₂) fun h0 => ?_
  -- an isotropic `w ≠ 0` in the complement pairs with some `y`
  obtain ⟨y, hy⟩ : ∃ y, B w y ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hw (hnd w hall)
  -- the Gram matrix of the plane
  set g₁₁ := B Ω₁ Ω₁
  set g₁₂ := B Ω₁ Ω₂
  set g₂₂ := B Ω₂ Ω₂
  have hg₁₁ : 0 < g₁₁ := by simpa using hΩ 1 0 (Or.inl one_ne_zero)
  have hΔ : 0 < g₁₁ * g₂₂ - g₁₂ ^ 2 := by
    have := hΩ (-g₁₂) g₁₁ (Or.inr hg₁₁.ne')
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB Ω₂ Ω₁] at this
    nlinarith
  -- the projection of `y` to the complement
  set y₁ := B Ω₁ y
  set y₂ := B Ω₂ y
  set Δ := g₁₁ * g₂₂ - g₁₂ ^ 2
  set a := (g₂₂ * y₁ - g₁₂ * y₂) / Δ
  set b' := (g₁₁ * y₂ - g₁₂ * y₁) / Δ
  set y' := y - (a • Ω₁ + b' • Ω₂)
  have hy'₁ : B Ω₁ y' = 0 := by
    simp only [y', map_sub, map_add, map_smul, smul_eq_mul, a, b']
    rw [show B Ω₁ Ω₁ = g₁₁ from rfl, show B Ω₁ Ω₂ = g₁₂ from rfl, show B Ω₁ y = y₁ from rfl]
    field_simp
    ring
  have hy'₂ : B Ω₂ y' = 0 := by
    simp only [y', map_sub, map_add, map_smul, smul_eq_mul, a, b']
    rw [show B Ω₂ Ω₁ = g₁₂ from hB Ω₂ Ω₁, show B Ω₂ Ω₂ = g₂₂ from rfl,
      show B Ω₂ y = y₂ from rfl]
    field_simp
    ring
  have hwy' : B w y' = B w y := by
    simp only [y', map_sub, map_add, map_smul, smul_eq_mul, hB w Ω₁, hB w Ω₂, h₁, h₂]
    ring
  -- a vector of the complement with positive square
  set c := B w y
  set e := B y' y'
  set t := c * (1 / (|e| + 1))
  have hz₁ : B Ω₁ (w + t • y') = 0 := by
    simp [map_add, map_smul, h₁, hy'₁]
  have hz₂ : B Ω₂ (w + t • y') = 0 := by
    simp [map_add, map_smul, h₂, hy'₂]
  have hzz := hsemi _ hz₁ hz₂
  have hexp : B (w + t • y') (w + t • y') = 2 * t * c + t ^ 2 * e := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB y' w, hwy', h0]
    ring
  rw [hexp] at hzz
  set σ := 1 / (|e| + 1)
  have hσ : 0 < σ := by positivity
  have hσe : σ * |e| < 1 := by
    rw [show σ * |e| = |e| / (|e| + 1) by ring, div_lt_one (by positivity)]
    linarith
  have hσe' : -1 < σ * e := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le e) hσ.le
    linarith
  have hc : 0 < c ^ 2 := by positivity
  have : 2 * t * c + t ^ 2 * e = σ * c ^ 2 * (2 + σ * e) := by
    simp only [t, σ]
    ring
  rw [this] at hzz
  have : 0 < σ * c ^ 2 * (2 + σ * e) := mul_pos (mul_pos hσ hc) (by linarith)
  linarith

end Signature

/-! ### Stable constituents in a strict sector -/

section Sector

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Stable constituents in a strict sector.** Let classes `v_i`, `i ∈ s`, of norm at least `μ`
satisfy the support property with constant `D ≥ 0`, and let their charges lie in the sector of
phase `φ` and half-width `0 ≤ b ≤ 1/2`. Then their number `k` satisfies
`k μ cos(πb) ≤ D p_φ(Z(Σ v_i))`, where `p_φ` is the projection onto the ray of phase `φ`: each
constituent uses at least `μ cos(πb)/D` of the projection of the total charge. -/
theorem card_mul_cos_le_of_sector {Z : V →ₗ[ℝ] ℂ} {S : Set V} {D : ℝ}
    (hD : SupportProperty Z S D) (hD0 : 0 ≤ D) {φ b μ : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2)
    {ι : Type*} (s : Finset ι) {v : ι → V} (hS : ∀ i ∈ s, v i ∈ S) (hμ : ∀ i ∈ s, μ ≤ ‖v i‖)
    (hsec : ∀ i ∈ s, Z (v i) ∈ Complex.sector φ b) :
    (s.card : ℝ) * μ * Real.cos (π * b) ≤ D * Complex.phaseProj φ (Z (∑ i ∈ s, v i)) := by
  have hcos : 0 ≤ Real.cos (π * b) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  have hsum : (s.card : ℝ) * μ * Real.cos (π * b) = ∑ _i ∈ s, μ * Real.cos (π * b) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  rw [hsum, map_sum, Complex.phaseProj_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  calc μ * Real.cos (π * b) ≤ ‖v i‖ * Real.cos (π * b) :=
        mul_le_mul_of_nonneg_right (hμ i hi) hcos
    _ ≤ D * ‖Z (v i)‖ * Real.cos (π * b) := mul_le_mul_of_nonneg_right (hD _ (hS i hi)) hcos
    _ ≤ D * Complex.phaseProj φ (Z (v i)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (Complex.norm_mul_cos_le_phaseProj (by linarith) (hsec i hi)) hD0

/-- Each constituent in a strict sector is bounded by the projection of the total charge:
`‖v_j‖ cos(πb) ≤ D p_φ(Z(Σ v_i))`. -/
theorem norm_mul_cos_le_of_sector {Z : V →ₗ[ℝ] ℂ} {S : Set V} {D : ℝ}
    (hD : SupportProperty Z S D) (hD0 : 0 ≤ D) {φ b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2)
    {ι : Type*} (s : Finset ι) {v : ι → V} (hS : ∀ i ∈ s, v i ∈ S)
    (hsec : ∀ i ∈ s, Z (v i) ∈ Complex.sector φ b) {j : ι} (hj : j ∈ s) :
    ‖v j‖ * Real.cos (π * b) ≤ D * Complex.phaseProj φ (Z (∑ i ∈ s, v i)) := by
  have hcos : 0 ≤ Real.cos (π * b) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  have hproj : ∀ i ∈ s, 0 ≤ Complex.phaseProj φ (Z (v i)) := fun i hi =>
    (mul_nonneg (norm_nonneg _) hcos).trans
      (Complex.norm_mul_cos_le_phaseProj (by linarith) (hsec i hi))
  rw [map_sum, Complex.phaseProj_sum]
  calc ‖v j‖ * Real.cos (π * b) ≤ D * ‖Z (v j)‖ * Real.cos (π * b) :=
        mul_le_mul_of_nonneg_right (hD _ (hS j hj)) hcos
    _ ≤ D * Complex.phaseProj φ (Z (v j)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (Complex.norm_mul_cos_le_phaseProj (by linarith) (hsec j hj)) hD0
    _ ≤ D * ∑ i ∈ s, Complex.phaseProj φ (Z (v i)) :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum hproj hj) hD0

end Sector

/-! ### Charges on the real Mukai lattice -/

/-- The Mukai form is nondegenerate when `b` is: `⟪v, (0, 0, 1)⟫ = -r`, `⟪v, (1, 0, 0)⟫ = -s` and
`⟪v, (0, y, 0)⟫ = b(c, y)`. -/
theorem eq_zero_of_forall_pairing_eq_zero {R N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] {b : N →ₗ[R] N →ₗ[R] R} (hb : ∀ x, (∀ y, b x y = 0) → x = 0)
    {v : MukaiLattice R N} (hv : ∀ w, pairing b v w = 0) : v = 0 := by
  obtain ⟨r, c, t⟩ := v
  have h1 := hv (0, 0, 1)
  have h2 := hv (1, 0, 0)
  simp only [pairing_mk, map_zero, mul_one, mul_zero, zero_mul, sub_zero, zero_sub,
    neg_eq_zero] at h1 h2
  have hc : c = 0 := hb c fun y => by simpa using hv (0, y, 0)
  rw [one_mul] at h2
  simp [h1, h2, hc]

section RealMukai

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : LinearMap.BilinForm ℝ E)

/-- The charge `Z(v) = ⟪Ω₁, v⟫ + i ⟪Ω₂, v⟫` of a real class `v`. -/
noncomputable def realCharge (Ω₁ Ω₂ : MukaiLattice ℝ E) : MukaiLattice ℝ E →ₗ[ℝ] ℂ where
  toFun v := ⟨pairing b Ω₁ v, pairing b Ω₂ v⟩
  map_add' v w := by apply Complex.ext <;> simp [pairing_add_right]
  map_smul' a v := by apply Complex.ext <;> simp [pairing_smul_right]

@[simp]
theorem re_realCharge (Ω₁ Ω₂ v : MukaiLattice ℝ E) :
    (realCharge b Ω₁ Ω₂ v).re = pairing b Ω₁ v :=
  rfl

@[simp]
theorem im_realCharge (Ω₁ Ω₂ v : MukaiLattice ℝ E) :
    (realCharge b Ω₁ Ω₂ v).im = pairing b Ω₂ v :=
  rfl

theorem realCharge_eq_zero_iff {Ω₁ Ω₂ v : MukaiLattice ℝ E} :
    realCharge b Ω₁ Ω₂ v = 0 ↔ pairing b Ω₁ v = 0 ∧ pairing b Ω₂ v = 0 := by
  rw [Complex.ext_iff]
  simp

/-- **The kernel of a positive period is negative definite** in signature `(2, n)`: if `b` is
symmetric and nondegenerate, the Mukai form has no positive-definite `3`-space, and `Ω₁`, `Ω₂`
span a positive-definite plane, then `⟪v, v⟫ < 0` for every nonzero real class with
`⟪Ω₁, v⟫ = ⟪Ω₂, v⟫ = 0`. -/
theorem negDef_ker_realCharge [FiniteDimensional ℝ E] (hb : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hsig : sigPos (mukaiForm b).toQuadraticMap ≤ 2)
    {Ω₁ Ω₂ : MukaiLattice ℝ E}
    (hΩ : ∀ a a' : ℝ, (a ≠ 0 ∨ a' ≠ 0) → 0 < selfPairing b (a • Ω₁ + a' • Ω₂))
    {v : MukaiLattice ℝ E} (hv : realCharge b Ω₁ Ω₂ v = 0) (hv0 : v ≠ 0) :
    selfPairing b v < 0 := by
  rw [realCharge_eq_zero_iff] at hv
  exact negDef_orthogonal_of_posPlane (mukaiForm b) (mukaiForm_comm b hb)
    (fun w hw => eq_zero_of_forall_pairing_eq_zero hnd hw) hsig hΩ hv.1 hv.2 hv0

/-- **The signature-`(2, n)` support property.** In signature `(2, n)`, at a positive period
`(Ω₁, Ω₂)`, if no nonzero class of `Γ` with `⟪v, v⟫ ≥ -2` has charge zero, the support property
holds on the classes of `Γ` with `⟪v, v⟫ ≥ -2`. -/
theorem exists_supportProperty_realCharge [FiniteDimensional ℝ E] (hb : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hsig : sigPos (mukaiForm b).toQuadraticMap ≤ 2)
    {Ω₁ Ω₂ : MukaiLattice ℝ E}
    (hΩ : ∀ a a' : ℝ, (a ≠ 0 ∨ a' ≠ 0) → 0 < selfPairing b (a • Ω₁ + a' • Ω₂))
    {Γ : Set (MukaiLattice ℝ E)} (hΓ : ∀ R : ℝ, {v | v ∈ Γ ∧ ‖v‖ ≤ R}.Finite)
    (hZ : ∀ v ∈ Γ, v ≠ 0 → -2 ≤ selfPairing b v → realCharge b Ω₁ Ω₂ v ≠ 0) :
    ∃ D, SupportProperty (realCharge b Ω₁ Ω₂) {v | v ∈ Γ ∧ -2 ≤ selfPairing b v} D :=
  exists_supportProperty (mukaiForm b) (realCharge b Ω₁ Ω₂)
    (fun _ hv hv0 => negDef_ker_realCharge b hb hnd hsig hΩ hv hv0) hΓ hZ

/-! ### The completed square and the root test -/

/-- The **normalized charge** `Z(r, c, s) = x r - s + b(β, c) + i (b(H, c) - a r)`, the charge of
`Ω₁ = (1, β, -x)` and `Ω₂ = (0, H, a)`. -/
noncomputable def normalizedCharge (x : ℝ) (β H : E) (a : ℝ) : MukaiLattice ℝ E →ₗ[ℝ] ℂ :=
  realCharge b (1, β, -x) (0, H, a)

variable {b}

theorem re_normalizedCharge (x : ℝ) (β H : E) (a : ℝ) (v : MukaiLattice ℝ E) :
    (normalizedCharge b x β H a v).re = x * v.1 - v.2.2 + b β v.2.1 := by
  simp only [normalizedCharge, re_realCharge, pairing]
  ring

theorem im_normalizedCharge (x : ℝ) (β H : E) (a : ℝ) (v : MukaiLattice ℝ E) :
    (normalizedCharge b x β H a v).im = b H v.2.1 - a * v.1 := by
  simp only [normalizedCharge, im_realCharge, pairing]
  ring

variable (b)

/-- `δ = 2x + b(β, β) - a²/b(H, H)`. For `b(H, H) > 0` the charge plane of the normalized
charge is positive exactly when `δ > 0`. -/
noncomputable def normalizedDelta (x : ℝ) (β H : E) (a : ℝ) : ℝ :=
  2 * x + b β β - a ^ 2 / b H H

/-- The part `u = c/r - (a/b(H, H)) H` of the slope of `v = (r, c, s)` transverse to `H`. -/
noncomputable def perpPart (H : E) (a : ℝ) (v : MukaiLattice ℝ E) : E :=
  v.1⁻¹ • v.2.1 - (a / b H H) • H

variable {b}

/-- On a class with `Im Z = 0` the transverse part is orthogonal to `H`. -/
theorem perpPart_orthogonal {H : E} {a : ℝ} (hH : b H H ≠ 0) {v : MukaiLattice ℝ E}
    (hr : v.1 ≠ 0) (him : b H v.2.1 = a * v.1) : b H (perpPart b H a v) = 0 := by
  simp only [perpPart, map_sub, map_smul, smul_eq_mul, him]
  field_simp
  ring

/-- **The completed square.** For a root `v = (r, c, s)` with `r ≠ 0` and `Im Z(v) = 0`, that is
`b(H, c) = a r`, the normalized charge has
`Re Z(v)/r = δ/2 - b(u - β, u - β)/2 - 1/r²`, where `u = c/r - (a/b(H, H)) H ⊥ H`. -/
theorem re_normalizedCharge_div_rank (hb : ∀ y z, b y z = b z y) {x a : ℝ} {β H : E}
    (hH : b H H ≠ 0) (hβH : b β H = 0) {v : MukaiLattice ℝ E} (hv : selfPairing b v = -2)
    (hr : v.1 ≠ 0) (him : b H v.2.1 = a * v.1) :
    (normalizedCharge b x β H a v).re / v.1 = normalizedDelta b x β H a / 2 -
      b (perpPart b H a v - β) (perpPart b H a v - β) / 2 - 1 / v.1 ^ 2 := by
  obtain ⟨r, c, t⟩ := v
  simp only at hr him
  rw [selfPairing_mk] at hv
  rw [re_normalizedCharge, normalizedDelta, perpPart]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hb c H, hb c β, hb H β, him, hβH]
  field_simp
  linear_combination (b H H) * hv

/-- **The root test: the rank bound.** If `b` is negative semidefinite on `H^⊥` and `δ > 0`, a
root of positive rank with `Im Z = 0` and `Re Z ≤ 0` has `r² ≤ 2/δ`. -/
theorem rank_sq_le_of_re_nonpos (hb : ∀ y z, b y z = b z y) {x a : ℝ} {β H : E}
    (hH : b H H ≠ 0) (hβH : b β H = 0) (hneg : ∀ w, b H w = 0 → b w w ≤ 0)
    {v : MukaiLattice ℝ E} (hv : selfPairing b v = -2) (hr : 0 < v.1)
    (him : b H v.2.1 = a * v.1) (hre : (normalizedCharge b x β H a v).re ≤ 0)
    (hδ : 0 < normalizedDelta b x β H a) : v.1 ^ 2 ≤ 2 / normalizedDelta b x β H a := by
  have hcs := re_normalizedCharge_div_rank hb hH hβH hv hr.ne' him (x := x)
  have hperp : b H (perpPart b H a v - β) = 0 := by
    rw [map_sub, perpPart_orthogonal hH hr.ne' him, hb H β, hβH, sub_zero]
  have hq := hneg _ hperp
  have hdiv : (normalizedCharge b x β H a v).re / v.1 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hre hr.le
  have h1 : normalizedDelta b x β H a / 2 ≤ 1 / v.1 ^ 2 := by linarith
  rw [le_div_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ hδ]
  linarith

/-- **The root test: the ellipsoid.** Under the hypotheses of `rank_sq_le_of_re_nonpos`, the
transverse part of the slope lies in the ellipsoid `-b(u - β, u - β) ≤ 2/r² - δ`. -/
theorem neg_le_of_re_nonpos (hb : ∀ y z, b y z = b z y) {x a : ℝ} {β H : E}
    (hH : b H H ≠ 0) (hβH : b β H = 0) {v : MukaiLattice ℝ E} (hv : selfPairing b v = -2)
    (hr : 0 < v.1) (him : b H v.2.1 = a * v.1) (hre : (normalizedCharge b x β H a v).re ≤ 0) :
    -b (perpPart b H a v - β) (perpPart b H a v - β) ≤
      2 / v.1 ^ 2 - normalizedDelta b x β H a := by
  have hcs := re_normalizedCharge_div_rank hb hH hβH hv hr.ne' him (x := x)
  have hdiv : (normalizedCharge b x β H a v).re / v.1 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hre hr.le
  have : 2 / v.1 ^ 2 = 2 * (1 / v.1 ^ 2) := by ring
  linarith

/-- **No violating root once `δ > 2`.** If `b` is negative semidefinite on `H^⊥` and `δ > 2`,
every root of rank at least one with `Im Z = 0` has `Re Z > 0`. -/
theorem re_normalizedCharge_pos (hb : ∀ y z, b y z = b z y) {x a : ℝ} {β H : E}
    (hH : b H H ≠ 0) (hβH : b β H = 0) (hneg : ∀ w, b H w = 0 → b w w ≤ 0)
    (hδ : 2 < normalizedDelta b x β H a) {v : MukaiLattice ℝ E} (hv : selfPairing b v = -2)
    (hr : 1 ≤ v.1) (him : b H v.2.1 = a * v.1) : 0 < (normalizedCharge b x β H a v).re := by
  by_contra hre
  push Not at hre
  have h := rank_sq_le_of_re_nonpos hb hH hβH hneg hv (by linarith) him hre (by linarith)
  have h2 : 2 / normalizedDelta b x β H a < 1 := (div_lt_one (by linarith)).mpr hδ
  nlinarith

/-- **The finite root test.** If `b(H, H) > 0`, `b` is negative definite on `H^⊥` and `δ > 0`,
then among classes `Γ` with finitely many points in every ball only finitely many roots of rank
at least one have `Im Z = 0` and `Re Z ≤ 0`: they have `r² ≤ 2/δ`, transverse part in a bounded
ellipsoid, and `s = (b(c, c) + 2)/(2r)`. -/
theorem finite_violations [FiniteDimensional ℝ E] (hb : ∀ y z, b y z = b z y) {x a : ℝ}
    {β H : E} (hH : 0 < b H H) (hβH : b β H = 0) (hneg : ∀ w, b H w = 0 → w ≠ 0 → b w w < 0)
    (hδ : 0 < normalizedDelta b x β H a) {Γ : Set (MukaiLattice ℝ E)}
    (hΓ : ∀ R : ℝ, {v | v ∈ Γ ∧ ‖v‖ ≤ R}.Finite) :
    {v | v ∈ Γ ∧ selfPairing b v = -2 ∧ 1 ≤ v.1 ∧ b H v.2.1 = a * v.1 ∧
      (normalizedCharge b x β H a v).re ≤ 0}.Finite := by
  obtain ⟨ε, hε, C, -, hF⟩ := exists_finsler b (b H) fun w hw hw0 => hneg w hw hw0
  obtain ⟨M, hM0, hM⟩ := exists_abs_bilinForm_le b
  have hneg' : ∀ w, b H w = 0 → b w w ≤ 0 := fun w hw => by
    by_cases hw0 : w = 0
    · simp [hw0]
    · exact (hneg w hw hw0).le
  set δ := normalizedDelta b x β H a
  set Rr := max 1 (2 / δ)
  set K := 2 / ε + 1 + ‖β‖ + |a / b H H| * ‖H‖
  set Rc := Rr * K
  set Rs := (M * Rc ^ 2 + 2) / 2
  have hRr : 1 ≤ Rr := le_max_left _ _
  have hK : 0 ≤ K := by positivity
  have hRc : 0 ≤ Rc := by positivity
  have hRs : 0 ≤ Rs := by positivity
  refine (hΓ (Rr + Rc + Rs)).subset fun v ⟨hvΓ, hv, hr, him, hre⟩ => ⟨hvΓ, ?_⟩
  have hr0 : 0 < v.1 := by linarith
  -- the rank
  have hrank := rank_sq_le_of_re_nonpos hb hH.ne' hβH hneg' hv hr0 him hre hδ
  have hrR : v.1 ≤ Rr := by
    have : v.1 ≤ v.1 ^ 2 := by nlinarith
    exact (this.trans hrank).trans (le_max_right _ _)
  -- the transverse part
  set u := perpPart b H a v - β
  have hu0 : b H u = 0 := by
    rw [map_sub, perpPart_orthogonal hH.ne' hr0.ne' him, hb H β, hβH, sub_zero]
  have hq := neg_le_of_re_nonpos hb hH.ne' hβH hv hr0 him hre
  have hu : ‖u‖ ^ 2 ≤ 2 / ε := by
    have hF' := hF u
    rw [hu0, norm_zero] at hF'
    have h2 : 2 / v.1 ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [le_div_iff₀ hε]
    nlinarith
  have hu' : ‖u‖ ≤ 2 / ε + 1 := by nlinarith [sq_nonneg (‖u‖ - 1)]
  -- the first Chern class: `c = r (u + β + (a/b(H, H)) H)`
  have hc : v.2.1 = v.1 • (u + β + (a / b H H) • H) := by
    simp only [u, perpPart, sub_add_cancel, sub_add_cancel, smul_smul, mul_inv_cancel₀ hr0.ne',
      one_smul]
  have hcR : ‖v.2.1‖ ≤ Rc := by
    rw [hc, norm_smul, Real.norm_of_nonneg hr0.le]
    have h1 : ‖u + β + (a / b H H) • H‖ ≤ K := by
      calc ‖u + β + (a / b H H) • H‖ ≤ ‖u‖ + ‖β‖ + ‖(a / b H H) • H‖ := norm_add₃_le
        _ ≤ (2 / ε + 1) + ‖β‖ + |a / b H H| * ‖H‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            linarith
    exact mul_le_mul hrR h1 (norm_nonneg _) (by linarith)
  -- the last coordinate: `2 r s = b(c, c) + 2`
  have hs : |v.2.2| ≤ Rs := by
    obtain ⟨r, c, t⟩ := v
    simp only at hr hcR ⊢
    rw [selfPairing_mk] at hv
    have hcc : |b c c| ≤ M * Rc ^ 2 :=
      (hM c).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcR 2) hM0)
    have h2 : 2 * (r * t) = b c c + 2 := by linarith
    have h3 : |t| ≤ |r * t| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < r)]
      nlinarith [abs_nonneg t]
    have h4 : |r * t| = |b c c + 2| / 2 := by
      rw [← h2, abs_mul (2 : ℝ), abs_two]
      ring
    have h5 : |b c c + 2| ≤ |b c c| + 2 := (abs_add_le _ _).trans (by rw [abs_two])
    rw [h4] at h3
    simp only [Rs]
    linarith
  -- the norm
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
  · rw [Real.norm_of_nonneg hr0.le]
    linarith
  · linarith
  · rw [Real.norm_eq_abs]
    linarith

end RealMukai

/-! ### The real model of an integral Mukai lattice -/

section RealModel

variable {N E : Type*} [AddCommGroup N] [NormedAddCommGroup E]

/-- The real model `(r, c, s) ↦ (r, f c, s)` of the integral Mukai lattice along `f : N →+ E`. -/
def realModel (f : N →+ E) : MukaiLattice ℤ N →+ MukaiLattice ℝ E where
  toFun v := ((v.1 : ℝ), f v.2.1, (v.2.2 : ℝ))
  map_zero' := by simp
  map_add' v w := by simp

@[simp]
theorem realModel_apply (f : N →+ E) (r : ℤ) (c : N) (t : ℤ) :
    realModel f (r, c, t) = ((r : ℝ), f c, (t : ℝ)) :=
  rfl

/-- The real model preserves the Mukai form when `f` carries `b` to `b_E`. -/
theorem pairing_realModel [NormedSpace ℝ E] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}
    {bE : LinearMap.BilinForm ℝ E} {f : N →+ E} (hf : ∀ x y, bE (f x) (f y) = b x y)
    (v w : MukaiLattice ℤ N) :
    pairing bE (realModel f v) (realModel f w) = pairing b v w := by
  obtain ⟨r, c, t⟩ := v
  obtain ⟨r', c', t'⟩ := w
  simp [hf]

theorem selfPairing_realModel [NormedSpace ℝ E] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}
    {bE : LinearMap.BilinForm ℝ E} {f : N →+ E} (hf : ∀ x y, bE (f x) (f y) = b x y)
    (v : MukaiLattice ℤ N) : selfPairing bE (realModel f v) = selfPairing b v :=
  pairing_realModel hf v v

/-- Finitely many integers in every interval `[-R, R]`. -/
theorem finite_int_abs_le (R : ℝ) : {n : ℤ | |(n : ℝ)| ≤ R}.Finite := by
  refine (Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset fun n (hn : |(n : ℝ)| ≤ R) => ?_
  have h := abs_le.mp hn
  constructor
  · have : ((-⌈R⌉ : ℤ) : ℝ) ≤ n := by
      push_cast
      linarith [Int.le_ceil R]
    exact_mod_cast this
  · have : (n : ℝ) ≤ ⌈R⌉ := h.2.trans (Int.le_ceil R)
    exact_mod_cast this

/-- If `f` has finitely many points in every ball, so does its real model. -/
theorem finite_realModel_norm_le {f : N →+ E} (hf : ∀ R : ℝ, {x | ‖f x‖ ≤ R}.Finite) (R : ℝ) :
    {v | ‖realModel f v‖ ≤ R}.Finite := by
  refine ((finite_int_abs_le R).prod ((hf R).prod (finite_int_abs_le R))).subset fun v hv => ?_
  have h := norm_prod_le_iff.mp hv
  have h' := norm_prod_le_iff.mp h.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [realModel, Real.norm_eq_abs] using h.1
  · simpa [realModel] using h'.1
  · simpa [realModel, Real.norm_eq_abs] using h'.2

/-- The image of the real model has finitely many points in every ball. -/
theorem finite_range_realModel_norm_le {f : N →+ E} (hf : ∀ R : ℝ, {x | ‖f x‖ ≤ R}.Finite)
    (R : ℝ) : {w | w ∈ Set.range (realModel f) ∧ ‖w‖ ≤ R}.Finite := by
  refine ((finite_realModel_norm_le hf R).image (realModel f)).subset ?_
  rintro w ⟨⟨v, rfl⟩, hw⟩
  exact ⟨v, hw, rfl⟩

end RealModel

end Mukai
