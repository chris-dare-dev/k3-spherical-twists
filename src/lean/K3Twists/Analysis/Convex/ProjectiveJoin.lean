/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Ultrafilter
import K3Twists.Analysis.Convex.IFS

/-!
# Cluster sets under a continuous parameter map, and the projective join

Let `K` be a compact space, `F` a Hausdorff topological additive group and `J : K → F`
continuous. A family `μ : α → F` *follows* `J` along a filter `l` if there are parameters
`w : α → K` with `μ a - J (w a) → 0`. Then the cluster points of `μ` are exactly the images under
`J` of the cluster points of `w` (`mapClusterPt_iff_of_tendsto_sub`). If moreover `J` is
injective, it is a closed embedding (`Continuous.isClosedEmbedding`), `μ` tends to `J x` iff `w`
tends to `x` (`tendsto_nhds_iff_of_tendsto_sub`), and `μ` converges iff `w` converges
(`exists_tendsto_iff_of_tendsto_sub`). The three statements hold as well for parameters that lie
eventually in a compact subset `s` of any space, with `J` continuous on `s`, and injective on `s`
for the last two (`IsCompact.mapClusterPt_iff_of_tendsto_sub` and its two companions).

This is the topology behind boundary points of normalized mass profiles that follow a continuous
parameter map. Profiles are functions on a type `Ω` of objects, so `F` is `Ω → ℝ` with the
product topology, and a boundary point of a family of normalized profiles is a cluster point
along a filter. That topology is not first countable when `Ω` is uncountable, so every statement
here is about cluster points of maps along filters (`MapClusterPt`) and limits along filters,
never about subsequences.

## The projective join

The linear case. Let `f : ι → F` be finitely many points of a real topological vector space and
`ℓ : F →ₗ[ℝ] ℝ` a linear functional, not assumed continuous, with `ℓ (f i) > 0` for every `i`.
The **projective join** sends weights `w : ι → ℝ` to
`projectiveJoin ℓ f w = (∑ i, w i * ℓ (f i))⁻¹ • ∑ i, w i • f i`, the multiple of
`∑ i, w i • f i` on the hyperplane `ℓ = 1` when the denominator does not vanish
(`apply_projectiveJoin`). It is constant on lines through the origin (`projectiveJoin_smul`), it
is the centre of mass of the normalized points `(ℓ (f i))⁻¹ • f i` with the weights
`w i * ℓ (f i)` (`projectiveJoin_eq_centerMass`), and it is continuous wherever its denominator
does not vanish, in particular on the standard simplex (`continuousOn_projectiveJoin`,
`continuousOn_projectiveJoin_simplex`, `continuous_projectiveJoin_weights`).

The join is injective on the standard simplex exactly when the `f i` are linearly independent
(`injOn_projectiveJoin_iff`). Only `ℓ (f i) > 0` is used, not that the `f i` are nonnegative:
for a relation `∑ i, a i • f i = 0` with `a ≠ 0`, applying `ℓ` shows that `a` takes both signs,
and its positive and negative parts, normalized, are two distinct points of the simplex with the
same join. Under linear independence the join is a closed embedding of the standard simplex into
a Hausdorff `F` (`isClosedEmbedding_projectiveJoin_weights`). The statements of the first
paragraph hold for the join: the one on cluster sets for any `f`
(`mapClusterPt_iff_of_tendsto_sub_projectiveJoin`), the two on convergence under linear
independence (`tendsto_nhds_projectiveJoin_iff_of_tendsto_sub`,
`exists_tendsto_iff_of_tendsto_sub_projectiveJoin`).

Profiles `μ a = t a • (∑ i, c a i • f i + ε a)`, with nonnegative weights `c a` of sum
`S a = ∑ i, c a i > 0`, scalars `t a ≠ 0` and errors with `(S a)⁻¹ • ε a → 0` and
`(S a)⁻¹ * ℓ (ε a) → 0`, follow the join of their normalized weights:
`(ℓ (μ a))⁻¹ • μ a - projectiveJoin ℓ f ((S a)⁻¹ • c a) → 0`
(`tendsto_inv_apply_smul_sub_projectiveJoin`). The usual case is `c a = (1, r₁, …, r_s)`, with
`S a = 1 + r₁ + ⋯ + r_s`. The second error condition follows from the first when `ℓ` is
continuous (`tendsto_inv_mul_apply_of_continuous`), in particular on `Ω → ℝ` when `ℓ` is a finite
combination `x ↦ ∑ k ∈ T, b k * x (E k)` of evaluations (`tendsto_inv_mul_apply_of_eq_sum`). That
`ℓ` is a finite combination of evaluations is what makes the error harmless; positive
coefficients `b k`, with `T` nonempty, give `ℓ (f i) > 0` for profiles `f i` positive at the
objects `E k`. So the cluster set of the normalized profiles is the image under the join of the
cluster set of the normalized weights (`mapClusterPt_inv_apply_smul_iff`), and under linear
independence the normalized profiles converge iff the normalized weights do
(`tendsto_inv_apply_smul_nhds_projectiveJoin_iff`, `exists_tendsto_inv_apply_smul_iff`).

## The nonlinear instance: the Cantor address map

`Analysis/Convex/IFS.lean` builds the centre ratio `IFS.centreRatio g : (ℕ → Bool) → ℝ` of an
infinite word in the two letters `b ∈ {2, 4}` (`false` for `2`, `true` for `4`): for `g > 0`, the
limit of the finite continued fractions `[b₀g; 2g, b₁g, 2g, …]` from any positive start. It is
continuous for `g > 0` (`IFS.continuous_centreRatio`) and, for `g ≥ 1/2`, a closed embedding of
the Cantor space `ℕ → Bool` into `ℝ` (`IFS.isClosedEmbedding_centreRatio`). So for words `ω a`
and reals `x a` with `x a - IFS.centreRatio g (ω a) → 0`, the cluster points of `x` are the
centre ratios of the cluster points of `ω` (`IFS.mapClusterPt_iff_of_tendsto_sub_centreRatio`),
and for `g ≥ 1/2`, `x` converges iff `ω` converges, that is iff each letter of `ω a` is
eventually constant (`IFS.exists_tendsto_iff_of_tendsto_sub_centreRatio`). As in that file,
nothing here identifies centre ratios with limits of mass profiles: the statements are about any
reals that follow the centre ratios of words.

## Main definitions

* `projectiveJoin ℓ f w`: the projective join of the points `f i` at the weights `w`.

## Main results

* `mapClusterPt_iff_of_tendsto_sub`: the cluster set of a family that follows a continuous map
  from a compact space is the image of the cluster set of its parameters.
* `tendsto_nhds_iff_of_tendsto_sub`, `exists_tendsto_iff_of_tendsto_sub`: for an injective
  parameter map the family converges iff its parameters do.
* `injOn_projectiveJoin_iff`, `injective_projectiveJoin_weights_iff`: the join is injective on the
  standard simplex iff the points are linearly independent.
* `projectiveJoin_eq_projectiveJoin_iff`: under linear independence two weights have the same
  join iff they are proportional.
* `isClosedEmbedding_projectiveJoin_weights`: under linear independence the join is a closed
  embedding of the standard simplex.
* `tendsto_inv_apply_smul_sub_projectiveJoin`: normalized profiles follow the join of their
  normalized weights.
* `mapClusterPt_inv_apply_smul_iff`, `exists_tendsto_inv_apply_smul_iff`: cluster sets and
  convergence of the normalized profiles.
* `IFS.mapClusterPt_iff_of_tendsto_sub_centreRatio`,
  `IFS.exists_tendsto_iff_of_tendsto_sub_centreRatio`: the Cantor instance.

## Conventions

Mathlib's standard simplex is the type `Convexity.StdSimplex ℝ ι`, with the topology induced by
its weights. Inside `ι → ℝ` it is the set `{w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}` of nonnegative
weights with sum `1`, the range of the weights: statements about weights as functions use that
set, and continuity, injectivity and the closed embedding are also stated on the type.
-/

open Filter Topology Set Function
open Convexity (StdSimplex)

variable {α : Type*} {l : Filter α}

/-! ### Cluster sets under a continuous parameter map -/

section ClusterSet

variable {K F : Type*} [TopologicalSpace K] [AddGroup F] [TopologicalSpace F] [ContinuousAdd F]
  {J : K → F} {w : α → K} {μ : α → F}

/-- Along a filter on which `w` tends to `x` inside a set `s` where `J` is continuous at `x`, a
family `μ` with `μ - J ∘ w → 0` tends to `J x`. -/
private lemma tendsto_of_tendsto_sub {s : Set K} {x : K} {l' : Filter α}
    (hJ : ContinuousWithinAt J s x) (hw : ∀ᶠ a in l', w a ∈ s) (hwx : Tendsto w l' (𝓝 x))
    (hμ : Tendsto (fun a ↦ μ a - J (w a)) l' (𝓝 0)) : Tendsto μ l' (𝓝 (J x)) := by
  simpa using hμ.add (hJ.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hwx, hw⟩))

/-- **Cluster sets under a continuous parameter map**, on a compact set. Let `J : K → F` be
continuous on a compact set `s`, let `w a ∈ s` eventually along `l`, and let
`μ a - J (w a) → 0`. Then the cluster points of `μ` are the images under `J` of the cluster points
of `w` in `s`. -/
theorem IsCompact.mapClusterPt_iff_of_tendsto_sub [T2Space F] {s : Set K} (hs : IsCompact s)
    (hJ : ContinuousOn J s) (hw : ∀ᶠ a in l, w a ∈ s)
    (hμ : Tendsto (fun a ↦ μ a - J (w a)) l (𝓝 0)) {ν : F} :
    MapClusterPt ν l μ ↔ ∃ x ∈ s, MapClusterPt x l w ∧ J x = ν := by
  constructor
  · intro h
    obtain ⟨U, hU, hUν⟩ := mapClusterPt_iff_ultrafilter.1 h
    obtain ⟨x, hx, hUx⟩ := hs.ultrafilter_le_nhds' (U.map w) (Ultrafilter.mem_map.2 (hU hw))
    rw [Ultrafilter.coe_map] at hUx
    exact ⟨x, hx, mapClusterPt_iff_ultrafilter.2 ⟨U, hU, hUx⟩,
      tendsto_nhds_unique (tendsto_of_tendsto_sub (hJ x hx) (hU hw) hUx (hμ.mono_left hU)) hUν⟩
  · rintro ⟨x, hx, h, rfl⟩
    obtain ⟨U, hU, hUx⟩ := mapClusterPt_iff_ultrafilter.1 h
    exact mapClusterPt_iff_ultrafilter.2
      ⟨U, hU, tendsto_of_tendsto_sub (hJ x hx) (hU hw) hUx (hμ.mono_left hU)⟩

/-- **Cluster sets under a continuous parameter map.** Let `K` be compact, `J : K → F` continuous
and `μ a - J (w a) → 0` along `l`. Then the cluster set of `μ` is the image under `J` of the
cluster set of `w`. -/
theorem mapClusterPt_iff_of_tendsto_sub [T2Space F] [CompactSpace K] (hJ : Continuous J)
    (hμ : Tendsto (fun a ↦ μ a - J (w a)) l (𝓝 0)) {ν : F} :
    MapClusterPt ν l μ ↔ ∃ x, MapClusterPt x l w ∧ J x = ν := by
  simpa using isCompact_univ.mapClusterPt_iff_of_tendsto_sub hJ.continuousOn
    (Eventually.of_forall fun _ ↦ mem_univ _) hμ

/-- With `J` continuous and injective on the compact set `s`, `w a ∈ s` eventually and
`μ a - J (w a) → 0`, the family `μ` tends to `J x` iff `w` tends to `x`, for every `x ∈ s`. -/
theorem IsCompact.tendsto_nhds_iff_of_tendsto_sub [T2Space F] {s : Set K} (hs : IsCompact s)
    (hJ : ContinuousOn J s) (hinj : InjOn J s) (hw : ∀ᶠ a in l, w a ∈ s)
    (hμ : Tendsto (fun a ↦ μ a - J (w a)) l (𝓝 0)) {x : K} (hx : x ∈ s) :
    Tendsto μ l (𝓝 (J x)) ↔ Tendsto w l (𝓝 x) := by
  refine ⟨fun h ↦ hs.tendsto_nhds_of_unique_mapClusterPt hw fun y hy hyw ↦ hinj hy hx ?_,
    fun h ↦ tendsto_of_tendsto_sub (hJ x hx) hw h hμ⟩
  have hJy : MapClusterPt (J y) l μ :=
    (hs.mapClusterPt_iff_of_tendsto_sub hJ hw hμ).2 ⟨y, hy, hyw, rfl⟩
  exact eq_of_nhds_neBot (ClusterPt.mono hJy h)

/-- With `J` continuous and injective on the compact set `s`, `w a ∈ s` eventually along a
nontrivial filter and `μ a - J (w a) → 0`, the family `μ` converges iff `w` converges to a point
of `s`. -/
theorem IsCompact.exists_tendsto_iff_of_tendsto_sub [T2Space F] [l.NeBot] {s : Set K}
    (hs : IsCompact s) (hJ : ContinuousOn J s) (hinj : InjOn J s) (hw : ∀ᶠ a in l, w a ∈ s)
    (hμ : Tendsto (fun a ↦ μ a - J (w a)) l (𝓝 0)) :
    (∃ ν, Tendsto μ l (𝓝 ν)) ↔ ∃ x ∈ s, Tendsto w l (𝓝 x) := by
  refine ⟨fun ⟨ν, hν⟩ ↦ ?_, fun ⟨x, hx, h⟩ ↦
    ⟨J x, (hs.tendsto_nhds_iff_of_tendsto_sub hJ hinj hw hμ hx).2 h⟩⟩
  obtain ⟨x, hx, hxw⟩ := hs.exists_mapClusterPt (le_principal_iff.2 hw)
  have hJx : MapClusterPt (J x) l μ :=
    (hs.mapClusterPt_iff_of_tendsto_sub hJ hw hμ).2 ⟨x, hx, hxw, rfl⟩
  obtain rfl : J x = ν := eq_of_nhds_neBot (ClusterPt.mono hJx hν)
  exact ⟨x, hx, (hs.tendsto_nhds_iff_of_tendsto_sub hJ hinj hw hμ hx).1 hν⟩

/-- **Injective parameter maps.** Let `K` be compact and `J : K → F` continuous and injective, so
a closed embedding (`Continuous.isClosedEmbedding`). If `μ a - J (w a) → 0`, then `μ` tends to
`J x` iff `w` tends to `x`. -/
theorem tendsto_nhds_iff_of_tendsto_sub [T2Space F] [CompactSpace K] (hJ : Continuous J)
    (hinj : Injective J) (hμ : Tendsto (fun a ↦ μ a - J (w a)) l (𝓝 0)) {x : K} :
    Tendsto μ l (𝓝 (J x)) ↔ Tendsto w l (𝓝 x) :=
  isCompact_univ.tendsto_nhds_iff_of_tendsto_sub hJ.continuousOn hinj.injOn
    (Eventually.of_forall fun _ ↦ mem_univ _) hμ (mem_univ x)

/-- **Injective parameter maps.** Let `K` be compact and `J : K → F` continuous and injective. If
`μ a - J (w a) → 0` along a nontrivial filter, then `μ` converges iff `w` converges. -/
theorem exists_tendsto_iff_of_tendsto_sub [T2Space F] [CompactSpace K] [l.NeBot]
    (hJ : Continuous J) (hinj : Injective J) (hμ : Tendsto (fun a ↦ μ a - J (w a)) l (𝓝 0)) :
    (∃ ν, Tendsto μ l (𝓝 ν)) ↔ ∃ x, Tendsto w l (𝓝 x) := by
  simpa using isCompact_univ.exists_tendsto_iff_of_tendsto_sub hJ.continuousOn hinj.injOn
    (Eventually.of_forall fun _ ↦ mem_univ _) hμ

end ClusterSet

/-! ### The projective join -/

section ProjectiveJoin

variable {ι F : Type*} [Fintype ι] [AddCommGroup F] [Module ℝ F]

/-- The **projective join** of finitely many points `f : ι → F` with respect to a linear
functional `ℓ`: the weights `w` go to the combination `∑ i, w i • f i` normalized by `ℓ`,
`(∑ i, w i * ℓ (f i))⁻¹ • ∑ i, w i • f i`. -/
noncomputable def projectiveJoin (ℓ : F →ₗ[ℝ] ℝ) (f : ι → F) (w : ι → ℝ) : F :=
  (∑ i, w i * ℓ (f i))⁻¹ • ∑ i, w i • f i

variable {ℓ : F →ₗ[ℝ] ℝ} {f : ι → F}

/-- The join is the combination `∑ i, w i • f i` normalized by `ℓ`. -/
theorem projectiveJoin_eq (ℓ : F →ₗ[ℝ] ℝ) (f : ι → F) (w : ι → ℝ) :
    projectiveJoin ℓ f w = (ℓ (∑ i, w i • f i))⁻¹ • ∑ i, w i • f i := by
  simp [projectiveJoin, map_sum, map_smul]

/-- `ℓ` takes the value `1` on the join wherever its denominator does not vanish. -/
theorem apply_projectiveJoin {w : ι → ℝ} (hw : ∑ i, w i * ℓ (f i) ≠ 0) :
    ℓ (projectiveJoin ℓ f w) = 1 := by
  simp only [projectiveJoin, map_smul, map_sum, smul_eq_mul]
  exact inv_mul_cancel₀ hw

/-- The join is constant on lines through the origin: `J(c • w) = J(w)` for `c ≠ 0`. -/
theorem projectiveJoin_smul (ℓ : F →ₗ[ℝ] ℝ) (f : ι → F) {c : ℝ} (hc : c ≠ 0) (w : ι → ℝ) :
    projectiveJoin ℓ f (c • w) = projectiveJoin ℓ f w := by
  have h₁ : ∑ i, (c • w) i * ℓ (f i) = c * ∑ i, w i * ℓ (f i) := by
    simp [Finset.mul_sum, mul_assoc]
  have h₂ : ∑ i, (c • w) i • f i = c • ∑ i, w i • f i := by
    simp [Finset.smul_sum, mul_smul]
  rw [projectiveJoin, projectiveJoin, h₁, h₂, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hc, mul_one]

/-- The join at the vertex `i` of the simplex is the normalized point `(ℓ (f i))⁻¹ • f i`. -/
theorem projectiveJoin_single [DecidableEq ι] (ℓ : F →ₗ[ℝ] ℝ) (f : ι → F) (i : ι) :
    projectiveJoin ℓ f (Pi.single i 1) = (ℓ (f i))⁻¹ • f i := by
  simp [projectiveJoin, Pi.single_apply]

/-- The join is the centre of mass of the normalized points `(ℓ (f i))⁻¹ • f i` with the weights
`w i * ℓ (f i)`. -/
theorem projectiveJoin_eq_centerMass (hf : ∀ i, ℓ (f i) ≠ 0) (w : ι → ℝ) :
    projectiveJoin ℓ f w =
      Finset.univ.centerMass (fun i ↦ w i * ℓ (f i)) fun i ↦ (ℓ (f i))⁻¹ • f i := by
  simp only [projectiveJoin, Finset.centerMass, smul_smul, mul_assoc, mul_inv_cancel₀ (hf _),
    mul_one]

/-- With `ℓ (f i) > 0` for every `i`, the denominator of the join is positive at nonnegative
weights with positive sum. -/
private lemma sum_mul_pos (hf : ∀ i, 0 < ℓ (f i)) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw' : 0 < ∑ i, w i) : 0 < ∑ i, w i * ℓ (f i) := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra! h
    exact hw'.not_ge (Finset.sum_nonpos fun i _ ↦ h i)
  exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (hw j) (hf j).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (hf i)⟩

/-- With `ℓ (f i) > 0` for every `i`, `ℓ` takes the value `1` on the join of nonnegative weights
with positive sum, in particular on the standard simplex. -/
theorem apply_projectiveJoin_of_nonneg (hf : ∀ i, 0 < ℓ (f i)) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw' : 0 < ∑ i, w i) : ℓ (projectiveJoin ℓ f w) = 1 :=
  apply_projectiveJoin (sum_mul_pos hf hw hw').ne'

/-- Normalized nonnegative weights with positive sum lie in the standard simplex. -/
private lemma inv_sum_smul_mem_simplex {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (hq' : 0 < ∑ i, q i) :
    (∑ i, q i)⁻¹ • q ∈ {w : ι → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} :=
  ⟨fun i ↦ mul_nonneg (inv_nonneg.2 hq'.le) (hq i), by
    simp [← Finset.mul_sum, inv_mul_cancel₀ hq'.ne']⟩

/-- In `ι → ℝ` the standard simplex `StdSimplex ℝ ι` is the set of nonnegative weights with sum
`1`. -/
private lemma range_weights :
    (range fun t : StdSimplex ℝ ι ↦ ⇑t.weights) = {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  rw [StdSimplex.range_toFun_comp_weights]
  ext w
  simp

private lemma isCompact_simplex : IsCompact {w : ι → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  rw [← range_weights]
  exact isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous

private lemma isClosed_simplex : IsClosed {w : ι → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  rw [← range_weights]
  exact (StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ ι).isClosed_range

/-- **The join identifies exactly the proportional weights.** For linearly independent `f`, two
weights with nonzero denominators have the same join iff they are proportional. -/
theorem projectiveJoin_eq_projectiveJoin_iff (hli : LinearIndependent ℝ f) {w w' : ι → ℝ}
    (hw : ∑ i, w i * ℓ (f i) ≠ 0) (hw' : ∑ i, w' i * ℓ (f i) ≠ 0) :
    projectiveJoin ℓ f w = projectiveJoin ℓ f w' ↔ ∃ c : ℝ, c ≠ 0 ∧ w = c • w' := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc, h⟩ ↦ h ▸ projectiveJoin_smul ℓ f hc w'⟩
  have hcoef := Fintype.linearIndependent_iff.1 hli
    (fun i ↦ (∑ j, w j * ℓ (f j))⁻¹ * w i - (∑ j, w' j * ℓ (f j))⁻¹ * w' i) (by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
      exact sub_eq_zero.2 h)
  refine ⟨(∑ j, w j * ℓ (f j)) * (∑ j, w' j * ℓ (f j))⁻¹, mul_ne_zero hw (inv_ne_zero hw'),
    funext fun i ↦ ?_⟩
  have := hcoef i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp at this ⊢
  linarith

/-- If the join is injective on the standard simplex then the points are linearly independent;
only `ℓ (f i) > 0` is used. A relation `∑ i, a i • f i = 0` with `a ≠ 0` gives, after applying
`ℓ`, that `a` takes both signs; its positive and negative parts, normalized, are two distinct
points of the simplex with the same join. -/
private lemma linearIndependent_of_injOn (hf : ∀ i, 0 < ℓ (f i))
    (h : InjOn (projectiveJoin ℓ f) {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}) :
    LinearIndependent ℝ f := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra! hne
  obtain ⟨j, hj⟩ := hne
  set p : ι → ℝ := fun i ↦ max (a i) 0 with hp
  set n : ι → ℝ := fun i ↦ max (-a i) 0 with hn
  have hp0 : ∀ i, 0 ≤ p i := fun i ↦ le_max_right _ _
  have hn0 : ∀ i, 0 ≤ n i := fun i ↦ le_max_right _ _
  have hpn : ∀ i, p i * n i = 0 := fun i ↦ by
    rcases le_total (a i) 0 with h | h <;> simp [hp, hn, h]
  have hsum : ∑ i, p i • f i = ∑ i, n i • f i := by
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    simpa only [← sub_smul, hp, hn, max_zero_sub_max_neg_zero_eq_self] using ha
  have hL : ∑ i, p i * ℓ (f i) = ∑ i, n i * ℓ (f i) := by
    simpa [map_sum, map_smul] using congrArg ℓ hsum
  -- applying `ℓ`, both parts are nonzero
  have hpos : 0 < ∑ i, p i * ℓ (f i) := by
    have hj' : 0 < p j + n j := by
      rcases lt_or_gt_of_ne hj with h | h <;> simp [hp, hn, h.le, h]
    have := Finset.sum_pos' (fun i _ ↦ mul_nonneg (add_nonneg (hp0 i) (hn0 i)) (hf i).le)
      ⟨j, Finset.mem_univ _, mul_pos hj' (hf j)⟩
    simp only [add_mul, Finset.sum_add_distrib, ← hL] at this
    linarith
  have hsum_pos : ∀ q : ι → ℝ, (∀ i, 0 ≤ q i) → 0 < ∑ i, q i * ℓ (f i) → 0 < ∑ i, q i := by
    intro q hq hq'
    refine (Finset.sum_nonneg fun i _ ↦ hq i).lt_of_ne fun h0 ↦ hq'.ne' ?_
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hq i).1 h0.symm
    simp [this]
  have hSp := hsum_pos p hp0 hpos
  have hSn := hsum_pos n hn0 (hL ▸ hpos)
  have heq := h (inv_sum_smul_mem_simplex hp0 hSp) (inv_sum_smul_mem_simplex hn0 hSn) (by
    rw [projectiveJoin_smul ℓ f (inv_ne_zero hSp.ne'),
      projectiveJoin_smul ℓ f (inv_ne_zero hSn.ne'), projectiveJoin, projectiveJoin, hL, hsum])
  have hzero : ∀ i, p i = 0 := fun i ↦ by
    have := congrFun heq i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h2 : (∑ i, p i)⁻¹ * p i * p i = 0 := by
      rw [this, mul_assoc, mul_comm (n i), hpn, mul_zero]
    have h3 : (∑ i, p i)⁻¹ ≠ 0 := inv_ne_zero hSp.ne'
    simpa [h3, mul_self_eq_zero] using h2
  simp [hzero] at hSp

/-- **Injectivity of the projective join.** With `ℓ (f i) > 0` for every `i`, the join is
injective on the standard simplex iff the points `f i` are linearly independent. The `f i` need
not be nonnegative in any sense. -/
theorem injOn_projectiveJoin_iff (hf : ∀ i, 0 < ℓ (f i)) :
    InjOn (projectiveJoin ℓ f) {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} ↔ LinearIndependent ℝ f := by
  refine ⟨linearIndependent_of_injOn hf, fun hli w hw w' hw' h ↦ ?_⟩
  obtain ⟨c, -, rfl⟩ := (projectiveJoin_eq_projectiveJoin_iff hli
    (sum_mul_pos hf hw.1 (by rw [hw.2]; exact one_pos)).ne'
    (sum_mul_pos hf hw'.1 (by rw [hw'.2]; exact one_pos)).ne').1 h
  have hc : c = 1 := by
    simpa [← Finset.mul_sum, hw'.2] using hw.2
  rw [hc, one_smul]

/-- With `ℓ (f i) > 0` for every `i`, the join is injective on the standard simplex
`StdSimplex ℝ ι` iff the points `f i` are linearly independent. -/
theorem injective_projectiveJoin_weights_iff (hf : ∀ i, 0 < ℓ (f i)) :
    Injective (fun t : StdSimplex ℝ ι ↦ projectiveJoin ℓ f t.weights) ↔
      LinearIndependent ℝ f := by
  rw [← injOn_projectiveJoin_iff hf, ← range_weights]
  exact ⟨fun h ↦ Injective.injOn_range (g := projectiveJoin ℓ f)
    (f := fun t : StdSimplex ℝ ι ↦ ⇑t.weights) h, fun h t t' htt' ↦
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).injective
      (h (mem_range_self t) (mem_range_self t') htt')⟩

/-- `(ℓ (c • x))⁻¹ • (c • x) = (ℓ x)⁻¹ • x` for `c ≠ 0`. -/
private lemma inv_apply_smul_smul (ℓ : F →ₗ[ℝ] ℝ) {c : ℝ} (hc : c ≠ 0) (x : F) :
    (ℓ (c • x))⁻¹ • (c • x) = (ℓ x)⁻¹ • x := by
  rw [map_smul, smul_eq_mul, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

section Topology

variable [TopologicalSpace F]

/-- For a continuous `ℓ`, the second error condition of
`tendsto_inv_apply_smul_sub_projectiveJoin` follows from the first. -/
theorem tendsto_inv_mul_apply_of_continuous (hℓ : Continuous ℓ) {S : α → ℝ} {ε : α → F}
    (hε : Tendsto (fun a ↦ (S a)⁻¹ • ε a) l (𝓝 0)) :
    Tendsto (fun a ↦ (S a)⁻¹ * ℓ (ε a)) l (𝓝 0) := by
  have h := (hℓ.tendsto 0).comp hε
  rw [map_zero] at h
  exact h.congr fun a ↦ by simp

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- The join is continuous wherever its denominator does not vanish, in particular on the standard
simplex when `ℓ (f i) > 0` for every `i`. -/
theorem continuousOn_projectiveJoin (ℓ : F →ₗ[ℝ] ℝ) (f : ι → F) :
    ContinuousOn (projectiveJoin ℓ f) {w | ∑ i, w i * ℓ (f i) ≠ 0} := by
  unfold projectiveJoin
  exact ((by fun_prop : Continuous fun w : ι → ℝ ↦ ∑ i, w i * ℓ (f i)).continuousOn.inv₀
    fun _ hw ↦ hw).smul (by fun_prop : Continuous fun w : ι → ℝ ↦ ∑ i, w i • f i).continuousOn

/-- With `ℓ (f i) > 0` for every `i`, the join is continuous on the standard simplex of
`ι → ℝ`. -/
theorem continuousOn_projectiveJoin_simplex (hf : ∀ i, 0 < ℓ (f i)) :
    ContinuousOn (projectiveJoin ℓ f) {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} :=
  (continuousOn_projectiveJoin ℓ f).mono fun w hw ↦
    (sum_mul_pos hf hw.1 (by rw [hw.2]; exact one_pos)).ne'

/-- With `ℓ (f i) > 0` for every `i`, the join is continuous on the standard simplex
`StdSimplex ℝ ι`. -/
theorem continuous_projectiveJoin_weights (hf : ∀ i, 0 < ℓ (f i)) :
    Continuous fun t : StdSimplex ℝ ι ↦ projectiveJoin ℓ f t.weights :=
  (continuousOn_projectiveJoin ℓ f).comp_continuous
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous fun t ↦
      (sum_mul_pos hf t.weights_nonneg (by simp)).ne'

/-- **The join is a closed embedding of the simplex.** With `ℓ (f i) > 0` for every `i` and
linearly independent `f i` in a Hausdorff space, the join is a closed embedding of the standard
simplex `StdSimplex ℝ ι` into `F`. -/
theorem isClosedEmbedding_projectiveJoin_weights [T2Space F] (hf : ∀ i, 0 < ℓ (f i))
    (hli : LinearIndependent ℝ f) :
    IsClosedEmbedding fun t : StdSimplex ℝ ι ↦ projectiveJoin ℓ f t.weights :=
  (continuous_projectiveJoin_weights hf).isClosedEmbedding
    ((injective_projectiveJoin_weights_iff hf).2 hli)

/-- **Cluster sets under the join.** With `ℓ (f i) > 0` for every `i`, let `w a` lie eventually
in the standard simplex and `μ a - projectiveJoin ℓ f (w a) → 0`. Then the cluster points of `μ`
are the joins of the cluster points of `w`. -/
theorem mapClusterPt_iff_of_tendsto_sub_projectiveJoin [T2Space F] (hf : ∀ i, 0 < ℓ (f i))
    {w : α → ι → ℝ} (hw : ∀ᶠ a in l, (∀ i, 0 ≤ w a i) ∧ ∑ i, w a i = 1) {μ : α → F}
    (hμ : Tendsto (fun a ↦ μ a - projectiveJoin ℓ f (w a)) l (𝓝 0)) {ν : F} :
    MapClusterPt ν l μ ↔ ∃ v, MapClusterPt v l w ∧ projectiveJoin ℓ f v = ν := by
  rw [isCompact_simplex.mapClusterPt_iff_of_tendsto_sub (continuousOn_projectiveJoin_simplex hf)
    hw hμ]
  exact ⟨fun ⟨v, _, hv⟩ ↦ ⟨v, hv⟩,
    fun ⟨v, hv⟩ ↦ ⟨v, isClosed_simplex.mem_of_mapClusterPt hv.1 hw, hv⟩⟩

/-- **Convergence under the join.** With `ℓ (f i) > 0` for every `i` and linearly independent
`f i` in a Hausdorff space, let `w a` lie eventually in the standard simplex and
`μ a - projectiveJoin ℓ f (w a) → 0`. Then `μ` tends to the join of a point `v` of the simplex
iff `w` tends to `v`. -/
theorem tendsto_nhds_projectiveJoin_iff_of_tendsto_sub [T2Space F] (hf : ∀ i, 0 < ℓ (f i))
    (hli : LinearIndependent ℝ f) {w : α → ι → ℝ}
    (hw : ∀ᶠ a in l, (∀ i, 0 ≤ w a i) ∧ ∑ i, w a i = 1) {μ : α → F}
    (hμ : Tendsto (fun a ↦ μ a - projectiveJoin ℓ f (w a)) l (𝓝 0)) {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hv' : ∑ i, v i = 1) :
    Tendsto μ l (𝓝 (projectiveJoin ℓ f v)) ↔ Tendsto w l (𝓝 v) :=
  isCompact_simplex.tendsto_nhds_iff_of_tendsto_sub (continuousOn_projectiveJoin_simplex hf)
    ((injOn_projectiveJoin_iff hf).2 hli) hw hμ ⟨hv, hv'⟩

/-- **Convergence under the join.** With `ℓ (f i) > 0` for every `i` and linearly independent
`f i` in a Hausdorff space, let `w a` lie eventually in the standard simplex and
`μ a - projectiveJoin ℓ f (w a) → 0` along a nontrivial filter. Then `μ` converges iff `w`
converges. -/
theorem exists_tendsto_iff_of_tendsto_sub_projectiveJoin [T2Space F] [l.NeBot]
    (hf : ∀ i, 0 < ℓ (f i)) (hli : LinearIndependent ℝ f) {w : α → ι → ℝ}
    (hw : ∀ᶠ a in l, (∀ i, 0 ≤ w a i) ∧ ∑ i, w a i = 1) {μ : α → F}
    (hμ : Tendsto (fun a ↦ μ a - projectiveJoin ℓ f (w a)) l (𝓝 0)) :
    (∃ ν, Tendsto μ l (𝓝 ν)) ↔ ∃ v, Tendsto w l (𝓝 v) := by
  rw [isCompact_simplex.exists_tendsto_iff_of_tendsto_sub
    (continuousOn_projectiveJoin_simplex hf) ((injOn_projectiveJoin_iff hf).2 hli) hw hμ]
  exact ⟨fun ⟨v, _, hv⟩ ↦ ⟨v, hv⟩, fun ⟨v, hv⟩ ↦ ⟨v, isClosed_simplex.mem_of_tendsto hv hw, hv⟩⟩

/-- Normalized weights `(S a)⁻¹ • c a`, with `c a` nonnegative of sum `S a > 0`, lie eventually
in the standard simplex. -/
private lemma eventually_inv_smul_mem_simplex {c : α → ι → ℝ} {S : α → ℝ}
    (hc : ∀ᶠ a in l, ∀ i, 0 ≤ c a i) (hS : ∀ᶠ a in l, ∑ i, c a i = S a)
    (hS₀ : ∀ᶠ a in l, 0 < S a) :
    ∀ᶠ a in l, (∀ i, 0 ≤ ((S a)⁻¹ • c a) i) ∧ ∑ i, ((S a)⁻¹ • c a) i = 1 := by
  filter_upwards [hc, hS, hS₀] with a hca hSa hS₀a
  rw [← hSa] at hS₀a ⊢
  exact inv_sum_smul_mem_simplex hca hS₀a

/-- **Approximation by the join.** With `ℓ (f i) > 0` for every `i`, let, eventually along `l`,
`μ a = t a • (∑ i, c a i • f i + ε a)` with scalars `t a ≠ 0` and nonnegative weights `c a` of
positive sum `S a = ∑ i, c a i`, and let the errors satisfy `(S a)⁻¹ • ε a → 0` and
`(S a)⁻¹ * ℓ (ε a) → 0`. Then the normalized profiles `(ℓ (μ a))⁻¹ • μ a` follow the join of the
normalized weights `(S a)⁻¹ • c a`. In the usual case `c a = (1, r₁, …, r_s)` and
`S a = 1 + r₁ + ⋯ + r_s`. -/
theorem tendsto_inv_apply_smul_sub_projectiveJoin (hf : ∀ i, 0 < ℓ (f i)) {c : α → ι → ℝ}
    {S t : α → ℝ} {ε μ : α → F} (hc : ∀ᶠ a in l, ∀ i, 0 ≤ c a i)
    (hS : ∀ᶠ a in l, ∑ i, c a i = S a) (hS₀ : ∀ᶠ a in l, 0 < S a) (ht : ∀ᶠ a in l, t a ≠ 0)
    (hμ : ∀ᶠ a in l, μ a = t a • (∑ i, c a i • f i + ε a))
    (hε : Tendsto (fun a ↦ (S a)⁻¹ • ε a) l (𝓝 0))
    (hℓε : Tendsto (fun a ↦ (S a)⁻¹ * ℓ (ε a)) l (𝓝 0)) :
    Tendsto (fun a ↦ (ℓ (μ a))⁻¹ • μ a - projectiveJoin ℓ f ((S a)⁻¹ • c a)) l (𝓝 0) := by
  have hw := eventually_inv_smul_mem_simplex hc hS hS₀
  -- the normalized profile in terms of the normalized weights
  have heq : ∀ᶠ a in l, (ℓ (μ a))⁻¹ • μ a =
      (∑ i, ((S a)⁻¹ • c a) i * ℓ (f i) + (S a)⁻¹ * ℓ (ε a))⁻¹ •
        (∑ i, ((S a)⁻¹ • c a) i • f i + (S a)⁻¹ • ε a) := by
    filter_upwards [hS₀, ht, hμ] with a hSa hta hμa
    have hx : (S a)⁻¹ • (∑ i, c a i • f i + ε a) =
        ∑ i, ((S a)⁻¹ • c a) i • f i + (S a)⁻¹ • ε a := by
      simp [smul_add, Finset.smul_sum, smul_smul]
    have hlx : ℓ (∑ i, ((S a)⁻¹ • c a) i • f i + (S a)⁻¹ • ε a) =
        ∑ i, ((S a)⁻¹ • c a) i * ℓ (f i) + (S a)⁻¹ * ℓ (ε a) := by
      simp [map_sum, map_smul]
    rw [hμa, inv_apply_smul_smul ℓ hta, ← inv_apply_smul_smul ℓ (inv_ne_zero hSa.ne'), hx, hlx]
  -- along every ultrafilter the normalized weights converge in the compact simplex
  rw [tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨v, hv, hUv⟩ := isCompact_simplex.ultrafilter_le_nhds'
    (U.map fun a ↦ (S a)⁻¹ • c a) (Ultrafilter.mem_map.2 (hU hw))
  rw [Ultrafilter.coe_map] at hUv
  have hD : 0 < ∑ i, v i * ℓ (f i) := sum_mul_pos hf hv.1 (by rw [hv.2]; exact one_pos)
  have hV := ((by fun_prop : Continuous fun v : ι → ℝ ↦ ∑ i, v i • f i).tendsto v).comp hUv
  have hL := ((by fun_prop : Continuous fun v : ι → ℝ ↦ ∑ i, v i * ℓ (f i)).tendsto v).comp hUv
  have h₁ := ((hL.add (hℓε.mono_left hU)).inv₀ (by simpa using hD.ne')).smul
    (hV.add (hε.mono_left hU))
  have h₂ := (hL.inv₀ hD.ne').smul hV
  rw [add_zero, add_zero] at h₁
  have h₃ := h₁.sub h₂
  rw [sub_self] at h₃
  refine h₃.congr' ?_
  filter_upwards [hU heq] with a ha
  rw [ha]
  rfl

/-- **Cluster sets of normalized profiles.** Under the hypotheses of
`tendsto_inv_apply_smul_sub_projectiveJoin`, with `F` Hausdorff, the cluster points of the
normalized profiles `(ℓ (μ a))⁻¹ • μ a` are the joins of the cluster points of the normalized
weights `(S a)⁻¹ • c a`, which lie in the standard simplex. -/
theorem mapClusterPt_inv_apply_smul_iff [T2Space F] (hf : ∀ i, 0 < ℓ (f i)) {c : α → ι → ℝ}
    {S t : α → ℝ} {ε μ : α → F} (hc : ∀ᶠ a in l, ∀ i, 0 ≤ c a i)
    (hS : ∀ᶠ a in l, ∑ i, c a i = S a) (hS₀ : ∀ᶠ a in l, 0 < S a) (ht : ∀ᶠ a in l, t a ≠ 0)
    (hμ : ∀ᶠ a in l, μ a = t a • (∑ i, c a i • f i + ε a))
    (hε : Tendsto (fun a ↦ (S a)⁻¹ • ε a) l (𝓝 0))
    (hℓε : Tendsto (fun a ↦ (S a)⁻¹ * ℓ (ε a)) l (𝓝 0)) {ν : F} :
    MapClusterPt ν l (fun a ↦ (ℓ (μ a))⁻¹ • μ a) ↔
      ∃ v, MapClusterPt v l (fun a ↦ (S a)⁻¹ • c a) ∧ projectiveJoin ℓ f v = ν :=
  mapClusterPt_iff_of_tendsto_sub_projectiveJoin hf (eventually_inv_smul_mem_simplex hc hS hS₀)
    (tendsto_inv_apply_smul_sub_projectiveJoin hf hc hS hS₀ ht hμ hε hℓε)

/-- **Convergence of normalized profiles.** Under the hypotheses of
`tendsto_inv_apply_smul_sub_projectiveJoin`, with `F` Hausdorff and the `f i` linearly
independent, the normalized profiles tend to the join of a point `v` of the standard simplex iff
the normalized weights tend to `v`. -/
theorem tendsto_inv_apply_smul_nhds_projectiveJoin_iff [T2Space F] (hf : ∀ i, 0 < ℓ (f i))
    (hli : LinearIndependent ℝ f) {c : α → ι → ℝ} {S t : α → ℝ} {ε μ : α → F}
    (hc : ∀ᶠ a in l, ∀ i, 0 ≤ c a i) (hS : ∀ᶠ a in l, ∑ i, c a i = S a)
    (hS₀ : ∀ᶠ a in l, 0 < S a) (ht : ∀ᶠ a in l, t a ≠ 0)
    (hμ : ∀ᶠ a in l, μ a = t a • (∑ i, c a i • f i + ε a))
    (hε : Tendsto (fun a ↦ (S a)⁻¹ • ε a) l (𝓝 0))
    (hℓε : Tendsto (fun a ↦ (S a)⁻¹ * ℓ (ε a)) l (𝓝 0)) {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hv' : ∑ i, v i = 1) :
    Tendsto (fun a ↦ (ℓ (μ a))⁻¹ • μ a) l (𝓝 (projectiveJoin ℓ f v)) ↔
      Tendsto (fun a ↦ (S a)⁻¹ • c a) l (𝓝 v) :=
  tendsto_nhds_projectiveJoin_iff_of_tendsto_sub hf hli
    (eventually_inv_smul_mem_simplex hc hS hS₀)
    (tendsto_inv_apply_smul_sub_projectiveJoin hf hc hS hS₀ ht hμ hε hℓε) hv hv'

/-- **Convergence of normalized profiles.** Under the hypotheses of
`tendsto_inv_apply_smul_sub_projectiveJoin`, with `F` Hausdorff, the `f i` linearly independent
and `l` nontrivial, the normalized profiles converge iff the normalized weights converge. -/
theorem exists_tendsto_inv_apply_smul_iff [T2Space F] [l.NeBot] (hf : ∀ i, 0 < ℓ (f i))
    (hli : LinearIndependent ℝ f) {c : α → ι → ℝ} {S t : α → ℝ} {ε μ : α → F}
    (hc : ∀ᶠ a in l, ∀ i, 0 ≤ c a i) (hS : ∀ᶠ a in l, ∑ i, c a i = S a)
    (hS₀ : ∀ᶠ a in l, 0 < S a) (ht : ∀ᶠ a in l, t a ≠ 0)
    (hμ : ∀ᶠ a in l, μ a = t a • (∑ i, c a i • f i + ε a))
    (hε : Tendsto (fun a ↦ (S a)⁻¹ • ε a) l (𝓝 0))
    (hℓε : Tendsto (fun a ↦ (S a)⁻¹ * ℓ (ε a)) l (𝓝 0)) :
    (∃ ν, Tendsto (fun a ↦ (ℓ (μ a))⁻¹ • μ a) l (𝓝 ν)) ↔
      ∃ v, Tendsto (fun a ↦ (S a)⁻¹ • c a) l (𝓝 v) :=
  exists_tendsto_iff_of_tendsto_sub_projectiveJoin hf hli
    (eventually_inv_smul_mem_simplex hc hS hS₀)
    (tendsto_inv_apply_smul_sub_projectiveJoin hf hc hS hS₀ ht hμ hε hℓε)

end Topology

end ProjectiveJoin

/-- **A finite combination of evaluations makes the error harmless.** On profiles `Ω → ℝ`, let
`ℓ x = ∑ k ∈ T, b k * x (E k)` for a finite set `T`. If `(S a)⁻¹ • ε a → 0` in the product
topology, that is pointwise, then `(S a)⁻¹ * ℓ (ε a) → 0`: the second error condition of
`tendsto_inv_apply_smul_sub_projectiveJoin` follows from the first. -/
theorem tendsto_inv_mul_apply_of_eq_sum {Ω κ : Type*} {T : Finset κ} {b : κ → ℝ} {E : κ → Ω}
    {ℓ : (Ω → ℝ) → ℝ} (hℓ : ∀ x, ℓ x = ∑ k ∈ T, b k * x (E k)) {S : α → ℝ} {ε : α → Ω → ℝ}
    (hε : Tendsto (fun a ↦ (S a)⁻¹ • ε a) l (𝓝 0)) :
    Tendsto (fun a ↦ (S a)⁻¹ * ℓ (ε a)) l (𝓝 0) := by
  have h := tendsto_finsetSum T fun k _ ↦
    (((continuous_apply (E k)).tendsto 0).comp hε).const_mul (b k)
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  refine h.congr fun a ↦ ?_
  simp only [hℓ, Finset.mul_sum, comp_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-! ### The nonlinear instance: the Cantor address map -/

namespace IFS

variable {g : ℝ} {ω : α → ℕ → Bool} {x : α → ℝ}

/-- The centre ratio is continuous on the Cantor space `ℕ → Bool` for `g > 0`. -/
theorem continuous_centreRatio (hg : 0 < g) : Continuous (centreRatio g) :=
  Real.continuous_exp.comp
    (continuous_codingMap (lipschitzWith_twoBlockLetter hg) (twoBlockConst_lt_one hg))

/-- **Cluster points of centre ratios.** For `g > 0`, words `ω a` and reals `x a` with
`x a - centreRatio g (ω a) → 0`, the cluster points of `x` are the centre ratios of the cluster
points of `ω` in the Cantor space `ℕ → Bool`. -/
theorem mapClusterPt_iff_of_tendsto_sub_centreRatio (hg : 0 < g)
    (hx : Tendsto (fun a ↦ x a - centreRatio g (ω a)) l (𝓝 0)) {y : ℝ} :
    MapClusterPt y l x ↔ ∃ η, MapClusterPt η l ω ∧ centreRatio g η = y :=
  mapClusterPt_iff_of_tendsto_sub (continuous_centreRatio hg) hx

/-- For `g ≥ 1/2` and `x a - centreRatio g (ω a) → 0`, `x` tends to the centre ratio of a word
`η` iff `ω` tends to `η`. -/
theorem tendsto_nhds_centreRatio_iff_of_tendsto_sub (hg : 1 / 2 ≤ g)
    (hx : Tendsto (fun a ↦ x a - centreRatio g (ω a)) l (𝓝 0)) {η : ℕ → Bool} :
    Tendsto x l (𝓝 (centreRatio g η)) ↔ Tendsto ω l (𝓝 η) :=
  tendsto_nhds_iff_of_tendsto_sub (isClosedEmbedding_centreRatio hg).continuous
    (isClosedEmbedding_centreRatio hg).injective hx

/-- **Convergence and the Cantor address.** For `g ≥ 1/2` and `x a - centreRatio g (ω a) → 0`
along a nontrivial filter, `x` converges iff the words `ω` converge, that is iff each letter of
`ω a` is eventually constant. -/
theorem exists_tendsto_iff_of_tendsto_sub_centreRatio [l.NeBot] (hg : 1 / 2 ≤ g)
    (hx : Tendsto (fun a ↦ x a - centreRatio g (ω a)) l (𝓝 0)) :
    (∃ y, Tendsto x l (𝓝 y)) ↔ ∃ η, Tendsto ω l (𝓝 η) :=
  exists_tendsto_iff_of_tendsto_sub (isClosedEmbedding_centreRatio hg).continuous
    (isClosedEmbedding_centreRatio hg).injective hx

end IFS
