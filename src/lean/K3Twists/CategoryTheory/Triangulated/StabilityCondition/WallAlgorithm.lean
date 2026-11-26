/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.SplitTower
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WallCrossing
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WallStep

/-!
# The tower algorithm at one wall

The tower algorithm of the rank-one draft crosses a wall `w` between chambers `t₁` and `t₂` with
two local inputs (`CategoryTheory.Triangulated.WallCrossing`): the incoming factors group into wall
groups, and each wall group has an outgoing HN filtration at `t₂`. Its outgoing clause has three
parts: the outgoing flags exist in ordered phase windows (Bayer–Bridgeland, arXiv:1310.8266,
Lemma 2.7), the wall group carrying the point keeps it once (the two-extension lemma), and

3. *a wall group that does not carry the point has outgoing factors that are nonzero, do not carry
   the point, and are spherical.*

This file proves part 3 from the slice fields of the split tower theorem
(`CategoryTheory.Triangulated.SliceFields`) and the Mukai budget, with its nonzero-factor
conjunct: a non-carrier wall group of an object with `e = 2` is rigid, so its HN factors at any
slicing are rigid, hence spherical and not carriers (`outgoing_noncarrier`), and its outgoing HN
filtration can be chosen with nonzero factors and phases among those of any given one
(`HNFiltration.exists_nonzero_factors`), so the phase windows are kept. So the third part of the
outgoing clause is a theorem (`SliceFields.exists_outgoing_noncarrier`), and a wall crossing
needs only the grouping, the ordered flags and the two-extension lemma as inputs
(`WallCrossing.ofSliceFields`).

## On the rank-free form

The split tower theorem (`SplitTowerHypotheses.tower`) splits carrying the point once into at most
once, a theorem at every slicing (`SliceFields.atMostOnce`), and existence of a carrier
(`Slicing.HasCarrier`). On that form each input of the algorithm is an existence statement
(`WallCrossing.ofHasCarrier`): the grouping says that a carrier at `t₁` gives a carrier at the
wall, the outgoing flags exist in ordered phase windows with no condition on their factors, and
the carrier clause says that a nonzero semistable carrier at the wall has a carrier at `t₂`.

The carrier clause is the transport of a carrier across a named wall step from the wall slicing
to `t₂` (`CategoryTheory.Triangulated.WallStep`), so its anisotropy discharges the clause
through `WallStep.lost_isotropic` (`WallStep.hasCarrier_of_semistable`,
`WallCrossing.ofWallStep`). The flags and the octahedral insertion are then not needed for
transport: the grouping and the named wall give a transport step whose Gram matrices are those of
the stable spheres of the wall (`CarrierStep.ofGrouping`). What the flags give is the naming of
the factors after the wall: inserting them gives an HN filtration at `t₂` that carries the point
once, each factor an outgoing factor of one wall group, and its carrier factor an outgoing factor
of the carrier group (`SliceFields.exists_named_refinement`).

## Main results

* `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_factors`: every HN filtration can be
  replaced by one with nonzero factors and phases among its own.
* `CategoryTheory.Triangulated.SliceFields.exists_outgoing_noncarrier`: the third part of the
  outgoing clause, with nonzero factors.
* `CategoryTheory.Triangulated.WallCrossing.ofSliceFields`: a wall crossing from the grouping, the
  ordered flags and the carrier clause.
* `CategoryTheory.Triangulated.WallCrossing.ofHasCarrier`, `WallCrossing.ofWallStep`: a wall
  crossing from existence statements, and with the carrier clause from a named wall.
* `CategoryTheory.Triangulated.SliceFields.exists_named_refinement`: the factors after a wall.
* `CategoryTheory.Triangulated.CarrierStep.ofGrouping`: the transport step of a grouping and a
  named wall, with the Gram matrices of the wall.

## What stays an input

The grouping of incoming factors into wall groups (`WallCrossing.wall_of_incoming`, or its
existence part in `WallCrossing.ofHasCarrier`), the existence and order of the outgoing flags
(Bayer–Bridgeland, Lemma 2.7, in the formal wall model the HN filtration of the model for the
charge of the side, `Quiver.Preprojective.FormalWallHypotheses`), and the carrier clause (the
two-extension lemma, in the formal wall model
`Quiver.Preprojective.DoubledRep.twoExtensions_of_selfExtDim_eq_two`, or the anisotropy of a named
wall). Rigid wall objects are determined by their incoming flag in the quiver model
(`Quiver.Kronecker.DoubledRep.nonempty_iso_of_hnFiltration`, from the open-orbit input).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe w u u'

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **HN filtrations with nonzero factors.** Every HN filtration of `E` can be replaced by one whose
factors are nonzero and whose phases are among its own: drop the zero factors one at a time,
from the top of the filtration down. -/
theorem HNFiltration.exists_nonzero_factors {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) :
    ∃ G : HNFiltration C P E, (∀ i, ¬IsZero (G.factor i)) ∧ ∀ i, ∃ j, G.φ i = F.φ j := by
  suffices h : ∀ (m : ℕ) (E : C) (F : HNFiltration C P E), F.n = m →
      ∃ G : HNFiltration C P E, (∀ i, ¬IsZero (G.factor i)) ∧ ∀ i, ∃ j, G.φ i = F.φ j from
    h _ E F rfl
  intro m
  induction m with
  | zero =>
    intro E F hF
    exact ⟨F, fun i ↦ absurd i.isLt (by omega), fun i ↦ ⟨i, rfl⟩⟩
  | succ k ih =>
    intro E F hF
    have hpos : 0 < F.n := by omega
    obtain ⟨G', hG'0, hG'φ⟩ := ih _ (F.prefix C (F.n - 1) (by omega)) (by simp; omega)
    let T := F.triangle ⟨F.n - 1, by omega⟩
    have hT : T ∈ distTriang C := F.triangle_dist _
    by_cases hz : IsZero (F.factor ⟨F.n - 1, by omega⟩)
    · have : IsIso T.mor₁ := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hz
      refine ⟨G'.ofIso C ((F.lastTriangleObj₁Iso hpos).symm ≪≫ asIso T.mor₁ ≪≫
        F.lastTriangleObj₂Iso hpos), fun i ↦ hG'0 i, fun i ↦ ?_⟩
      obtain ⟨j, hj⟩ := hG'φ i
      exact ⟨⟨j, by have := j.isLt; simp at this; omega⟩, hj⟩
    · have hlt : ∀ i : Fin G'.n, F.φ ⟨F.n - 1, by omega⟩ < G'.φ i := fun i ↦ by
        obtain ⟨j, hj⟩ := hG'φ i
        rw [hj, HNFiltration.prefix_φ']
        exact F.hφ (Fin.mk_lt_mk.mpr (by have := j.isLt; simp at this; omega))
      have hψ : P (F.φ ⟨F.n - 1, by omega⟩) T.obj₃ := F.semistable _
      refine ⟨G'.appendFactor C T hT (F.lastTriangleObj₁Iso hpos) (F.lastTriangleObj₂Iso hpos)
        (F.φ ⟨F.n - 1, by omega⟩) hψ hlt, fun i ↦ ?_, fun i ↦ ?_⟩
      · have hi₀ : i.val < G'.n + 1 := i.isLt
        rcases Nat.lt_or_ge i.val G'.n with hi | hi
        · rw [HNFiltration.appendFactor_factor_of_lt G' T hT (F.lastTriangleObj₁Iso hpos)
            (F.lastTriangleObj₂Iso hpos) _ hψ hlt i hi]
          exact hG'0 _
        · rw [HNFiltration.appendFactor_factor_of_eq G' T hT (F.lastTriangleObj₁Iso hpos)
            (F.lastTriangleObj₂Iso hpos) _ hψ hlt i (by omega)]
          exact hz
      · have hi₀ : i.val < G'.n + 1 := i.isLt
        rcases Nat.lt_or_ge i.val G'.n with hi | hi
        · rw [HNFiltration.appendFactor_φ_of_lt G' T hT (F.lastTriangleObj₁Iso hpos)
            (F.lastTriangleObj₂Iso hpos) _ hψ hlt i hi]
          obtain ⟨j, hj⟩ := hG'φ ⟨i, hi⟩
          exact ⟨⟨j, by have := j.isLt; simp at this; omega⟩, hj⟩
        · rw [HNFiltration.appendFactor_φ_of_eq G' T hT (F.lastTriangleObj₁Iso hpos)
            (F.lastTriangleObj₂Iso hpos) _ hψ hlt i (by omega)]
          exact ⟨⟨F.n - 1, by omega⟩, rfl⟩

variable {b : MukaiBudget C} {carrier spherical : Slicing C → ObjectProperty C}

/-- **The third part of the outgoing clause, with its nonzero-factor conjunct.** Let `W` be an HN
filtration at a wall `w` of an object with `e = 2` that carries the point once, and `k` a wall
group that does not carry it. For every slicing `t₂` the wall group has an HN filtration at `t₂`
with nonzero factors that are spherical and not carriers, and phases among those of any given
one. -/
theorem SliceFields.exists_outgoing_noncarrier (hS : SliceFields b carrier spherical)
    {w t₂ : Slicing C} {E : C} (hE : b.e E = 2) (W : HNFiltration C w.P E)
    (hW : W.CarriesOnce (carrier w) (spherical w)) (k : Fin W.n) (hk : ¬carrier w (W.factor k))
    (G : HNFiltration C t₂.P (W.factor k)) :
    ∃ G' : HNFiltration C t₂.P (W.factor k), (∀ i, ¬IsZero (G'.factor i)) ∧
      (∀ i, ¬carrier t₂ (G'.factor i)) ∧ (∀ i, spherical t₂ (G'.factor i)) ∧
        ∀ i, ∃ j, G'.φ i = G.φ j := by
  obtain ⟨G', h0, hφ⟩ := G.exists_nonzero_factors
  obtain ⟨hc, hs⟩ := outgoing_noncarrier hS hE W hW k hk G'
  exact ⟨G', h0, hc, hs, hφ⟩

/-- **A wall crossing from its remaining inputs.** Given the slice fields, a wall crossing for the
objects with `e = 2` needs only the grouping of incoming factors into wall groups, and for every
wall filtration carrying the point once some outgoing flags in ordered phase windows of which the
group carrying the point keeps it once: the third part of the outgoing clause is a theorem
(`SliceFields.exists_outgoing_noncarrier`). -/
theorem WallCrossing.ofSliceFields (hS : SliceFields b carrier spherical) {t₁ w t₂ : Slicing C}
    (hwall : ∀ E, b.e E = 2 → t₁.CarriesOnce (carrier t₁) (spherical t₁) E →
      w.CarriesOnce (carrier w) (spherical w) E)
    (hflag : ∀ E, b.e E = 2 → ∀ W : HNFiltration C w.P E,
      W.CarriesOnce (carrier w) (spherical w) →
        ∃ G : ∀ k : Fin W.n, HNFiltration C t₂.P (W.factor k),
          (∀ k l : Fin W.n, k < l → ∀ i j, (G l).φ j < (G k).φ i) ∧
          ∀ k, carrier w (W.factor k) → (G k).CarriesOnce (carrier t₂) (spherical t₂)) :
    WallCrossing t₁ w t₂ carrier spherical (fun E ↦ b.e E = 2) where
  wall_of_incoming := hwall
  outgoing E hE W hW := by
    classical
    obtain ⟨G, hord, hcar⟩ := hflag E hE W hW
    have key : ∀ k : Fin W.n, ∃ G' : HNFiltration C t₂.P (W.factor k),
        (∀ i, ∃ j, G'.φ i = (G k).φ j) ∧
        (carrier w (W.factor k) → G'.CarriesOnce (carrier t₂) (spherical t₂)) ∧
        (¬carrier w (W.factor k) → (∀ i, ¬IsZero (G'.factor i)) ∧
          (∀ i, ¬carrier t₂ (G'.factor i)) ∧ ∀ i, spherical t₂ (G'.factor i)) := fun k ↦ by
      by_cases hk : carrier w (W.factor k)
      · exact ⟨G k, fun i ↦ ⟨i, rfl⟩, fun _ ↦ hcar k hk, fun h ↦ absurd hk h⟩
      · obtain ⟨G', h0, hc, hs, hφ⟩ := hS.exists_outgoing_noncarrier hE W hW k hk (G k)
        exact ⟨G', hφ, fun h ↦ absurd h hk, fun _ ↦ ⟨h0, hc, hs⟩⟩
    choose G' hG'φ hG'car hG'non using key
    refine ⟨G', fun k l hkl i j ↦ ?_, hG'car, fun k _ hk ↦ hG'non k hk⟩
    obtain ⟨i', hi'⟩ := hG'φ k i
    obtain ⟨j', hj'⟩ := hG'φ l j
    rw [hi', hj']
    exact hord k l hkl i' j'

/-! ### The algorithm on the rank-free form -/

/-- A carrier factor of an object with `e = 2` has `e = 2`: it is not spherical, hence not
rigid, and every HN factor has `e = 0` or `e = 2`. -/
theorem SliceFields.e_eq_two_of_carrier (hS : SliceFields b carrier spherical) {s : Slicing C}
    {E : C} (hE : b.e E = 2) (F : HNFiltration C s.P E) {k : Fin F.n}
    (hk : carrier s (F.factor k)) : b.e (F.factor k) = 2 := by
  have hne : ∀ i, b.e (F.factor i) ≠ 1 := fun i ↦ hS.ne_one s _ _ (F.semistable i)
  rcases b.e_factor_eq_zero_or_two s.hom_vanishing hE F hne k with h | h
  · exact absurd (hS.rigid_spherical s _ _ (F.semistable k) h) (hS.carrier_not_spherical s _ hk)
  · exact h

/-- **A wall crossing from existence statements.** Given the slice fields, a wall crossing for
the objects with `e = 2` needs three inputs, each an existence statement:

* the grouping, in the form *a carrier at `t₁` gives a carrier at the wall*;
* outgoing HN filtrations of the wall groups in ordered phase windows (Bayer–Bridgeland,
  arXiv:1310.8266, Lemma 2.7), with no condition on their factors;
* the carrier clause, in the form *a nonzero semistable carrier at the wall with `e = 2` has a
  carrier at `t₂`*.

Everything else is a theorem: at most once at every slicing (`SliceFields.atMostOnce`), the
outgoing clause for the groups without the point (`SliceFields.exists_outgoing_noncarrier`), and
carrying the point once for every outgoing filtration of the carrier group with nonzero factors
(`Slicing.CarriesOnce.forall`). -/
theorem WallCrossing.ofHasCarrier [∀ s, (carrier s).IsClosedUnderIsomorphisms]
    [∀ s, (spherical s).IsClosedUnderIsomorphisms] (hS : SliceFields b carrier spherical)
    {t₁ w t₂ : Slicing C}
    (hwall : ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E → w.HasCarrier (carrier w) E)
    (hflag : ∀ E, b.e E = 2 → ∀ W : HNFiltration C w.P E, (∀ i, ¬IsZero (W.factor i)) →
      ∃ G : ∀ k : Fin W.n, HNFiltration C t₂.P (W.factor k),
        ∀ k l : Fin W.n, k < l → ∀ i j, (G l).φ j < (G k).φ i)
    (hkeep : ∀ φ M, w.P φ M → ¬IsZero M → b.e M = 2 → carrier w M →
      t₂.HasCarrier (carrier t₂) M) :
    WallCrossing t₁ w t₂ carrier spherical (fun E ↦ b.e E = 2) := by
  refine WallCrossing.ofSliceFields hS (fun E hE h ↦ ?_) (fun E hE W hW ↦ ?_)
  · exact (hS.carriesOnce_iff_hasCarrier w hE).mpr
      (hwall E hE ((hS.carriesOnce_iff_hasCarrier t₁ hE).mp h))
  · obtain ⟨G, hord⟩ := hflag E hE W hW.nonzero
    choose G' hG'0 hG'φ using fun k ↦ (G k).exists_nonzero_factors
    refine ⟨G', fun k l hkl i j ↦ ?_, fun k hk ↦ ?_⟩
    · obtain ⟨i', hi'⟩ := hG'φ k i
      obtain ⟨j', hj'⟩ := hG'φ l j
      rw [hi', hj']
      exact hord k l hkl i' j'
    · have he := hS.e_eq_two_of_carrier hE W hk
      exact ((hS.carriesOnce_iff_hasCarrier t₂ he).mpr
        (hkeep _ _ (W.semistable k) (hW.nonzero k) he hk)).forall (G' k) (hG'0 k)

/-- **Naming the factors after a wall.** Let `W` be an HN filtration at a wall `w` of an object
with `e = 2` that carries the point once, and let its groups have outgoing HN filtrations at `t₂`
with nonzero factors, in ordered phase windows, the carrier group having a carrier at `t₂`.
Inserting them (`HNFiltration.exists_refinement`) gives an HN filtration of `E` at `t₂` that
carries the point once, each of whose factors is an outgoing factor of one wall group, and whose
carrier factor is an outgoing factor of the carrier group of `W`: the other groups are rigid, so
their outgoing factors are spherical and not carriers (`outgoing_noncarrier`). -/
theorem SliceFields.exists_named_refinement [IsTriangulated C]
    [∀ s, (carrier s).IsClosedUnderIsomorphisms] [∀ s, (spherical s).IsClosedUnderIsomorphisms]
    (hS : SliceFields b carrier spherical) {w t₂ : Slicing C} {E : C} (hE : b.e E = 2)
    (W : HNFiltration C w.P E) (hW : W.CarriesOnce (carrier w) (spherical w))
    (G : ∀ k : Fin W.n, HNFiltration C t₂.P (W.factor k))
    (hsep : ∀ k l : Fin W.n, k < l → ∀ i j, (G l).φ j < (G k).φ i)
    (hG0 : ∀ k i, ¬IsZero ((G k).factor i))
    (hkeep : ∀ k, carrier w (W.factor k) → t₂.HasCarrier (carrier t₂) (W.factor k)) :
    ∃ H : HNFiltration C t₂.P E, H.CarriesOnce (carrier t₂) (spherical t₂) ∧
      (∀ i, ∃ k j, H.φ i = (G k).φ j ∧ Nonempty (H.factor i ≅ (G k).factor j)) ∧
      ∀ i, carrier t₂ (H.factor i) →
        ∃ k j, carrier w (W.factor k) ∧ Nonempty (H.factor i ≅ (G k).factor j) := by
  classical
  obtain ⟨H, hprov, hcount⟩ := W.exists_refinement G hsep
  have hpiece : ∀ k, (∀ i, carrier t₂ ((G k).factor i) ∨ spherical t₂ ((G k).factor i)) ∧
      (G k).count (carrier t₂) = if carrier w (W.factor k) then 1 else 0 := by
    intro k
    by_cases hk : carrier w (W.factor k)
    · have he := hS.e_eq_two_of_carrier hE W hk
      have h₂ := ((hS.carriesOnce_iff_hasCarrier t₂ he).mpr (hkeep k hk)).forall (G k) (hG0 k)
      exact ⟨h₂.pt_or_rg, by simp [h₂.count_eq_one, hk]⟩
    · obtain ⟨hc, hs⟩ := outgoing_noncarrier hS hE W hW k hk (G k)
      exact ⟨fun i ↦ Or.inr (hs i), by simp [PostnikovTower.count, hc, hk]⟩
  refine ⟨H, ⟨fun i hz ↦ ?_, ?_, fun i ↦ ?_⟩, hprov, fun i hi ↦ ?_⟩
  · obtain ⟨k, j, -, ⟨e⟩⟩ := hprov i
    exact hG0 k j (hz.of_iso e.symm)
  · rw [hcount (carrier t₂), Finset.sum_congr rfl (fun k _ ↦ (hpiece k).2)]
    exact hW.count_eq_one
  · obtain ⟨k, j, -, ⟨e⟩⟩ := hprov i
    exact ((hpiece k).1 j).imp ((carrier t₂).prop_of_iso e.symm)
      ((spherical t₂).prop_of_iso e.symm)
  · obtain ⟨k, j, -, ⟨e⟩⟩ := hprov i
    refine ⟨k, j, ?_, ⟨e⟩⟩
    by_contra hk
    exact (outgoing_noncarrier hS hE W hW k hk (G k)).1 j ((carrier t₂).prop_of_iso e hi)

section NamedWall

variable {Λ : Type u'} [AddCommGroup Λ] {q : LinearMap.BilinForm ℤ Λ} {v : K₀ C →+ Λ}

/-- **The carrier clause from a named wall.** If the named wall step `S` from the wall slicing `w`
to `t₂` is anisotropic (no phase has an isotropic sum of the classes of its stable spheres), a
nonzero semistable carrier at `w` with `e = 2` has a carrier at `t₂`: this is the third input of
`WallCrossing.ofHasCarrier`, from `WallStep.lost_isotropic`. -/
theorem WallStep.hasCarrier_of_semistable {w t₂ : Slicing C} (S : WallStep b q v carrier w t₂)
    (han : S.Anisotropic) {φ : ℝ} {M : C} (hM : w.P φ M) (hM0 : ¬IsZero M) (he : b.e M = 2)
    (hc : carrier w M) : t₂.HasCarrier (carrier t₂) M :=
  S.keep han he (w.carriesOnce_of_semistable (Rg := ⊤) hM hM0 hc).hasCarrier

/-- **A wall crossing from the grouping, the ordered flags and a named wall.** The carrier clause
of `WallCrossing.ofHasCarrier` is discharged by an anisotropic named wall step from the wall
slicing to `t₂` (`WallStep.hasCarrier_of_semistable`). -/
theorem WallCrossing.ofWallStep [∀ s, (carrier s).IsClosedUnderIsomorphisms]
    [∀ s, (spherical s).IsClosedUnderIsomorphisms] (hS : SliceFields b carrier spherical)
    {t₁ w t₂ : Slicing C}
    (hwall : ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E → w.HasCarrier (carrier w) E)
    (hflag : ∀ E, b.e E = 2 → ∀ W : HNFiltration C w.P E, (∀ i, ¬IsZero (W.factor i)) →
      ∃ G : ∀ k : Fin W.n, HNFiltration C t₂.P (W.factor k),
        ∀ k l : Fin W.n, k < l → ∀ i j, (G l).φ j < (G k).φ i)
    (S : WallStep b q v carrier w t₂) (han : S.Anisotropic) :
    WallCrossing t₁ w t₂ carrier spherical (fun E ↦ b.e E = 2) :=
  WallCrossing.ofHasCarrier hS hwall hflag fun _ _ hM hM0 he hc ↦
    S.hasCarrier_of_semistable han hM hM0 he hc

/-- **The transport step of a grouping and a named wall.** If carriers pass from `t₁` to the wall
slicing `w` and `S` is a named wall step from `w` to `t₂`, the step from `t₁` to `t₂` whose Gram
matrices are those of the stable spheres of `S`; its field is `WallStep.lost_isotropic` after the
grouping. No outgoing flag and no octahedral insertion is used: on the rank-free form the flags
name the factors after the wall (`SliceFields.exists_named_refinement`) and are not needed for
transport. -/
def CarrierStep.ofGrouping {t₁ w t₂ : Slicing C}
    (hwall : ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E → w.HasCarrier (carrier w) E)
    (S : WallStep b q v carrier w t₂) : CarrierStep b carrier t₁ t₂ where
  ι := S.SphereType
  gram := S.gram
  lost_isotropic E hE h₁ h₂ := S.lost_isotropic E hE (hwall E hE h₁) h₂

@[simp]
theorem CarrierStep.ofGrouping_gram {t₁ w t₂ : Slicing C}
    (hwall : ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E → w.HasCarrier (carrier w) E)
    (S : WallStep b q v carrier w t₂) : (CarrierStep.ofGrouping hwall S).gram = S.gram :=
  rfl

/-- The step of a grouping and a named wall is anisotropic when the wall is. -/
theorem CarrierStep.anisotropic_ofGrouping {t₁ w t₂ : Slicing C}
    (hwall : ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E → w.HasCarrier (carrier w) E)
    {S : WallStep b q v carrier w t₂} (han : S.Anisotropic) :
    (CarrierStep.ofGrouping hwall S).Anisotropic :=
  han

end NamedWall

end CategoryTheory.Triangulated
