/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.SplitTower
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WallCrossing

/-!
# The outgoing clause of the tower algorithm

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

## Main results

* `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_factors`: every HN filtration can be
  replaced by one with nonzero factors and phases among its own.
* `CategoryTheory.Triangulated.SliceFields.exists_outgoing_noncarrier`: the third part of the
  outgoing clause, with nonzero factors.
* `CategoryTheory.Triangulated.WallCrossing.ofSliceFields`: a wall crossing from the grouping, the
  ordered flags and the carrier clause.

## What stays an input

The grouping of incoming factors into wall groups (`WallCrossing.wall_of_incoming`), the existence
and order of the outgoing flags (Bayer–Bridgeland, Lemma 2.7, in the formal wall model the HN
filtration of the model for the charge of the side, `Quiver.Preprojective.FormalWallHypotheses`),
and the carrier clause (the two-extension lemma, in the formal wall model
`Quiver.Preprojective.DoubledRep.twoExtensions_of_selfExtDim_eq_two`). Rigid wall objects are
determined by their incoming flag in the quiver model
(`Quiver.Kronecker.DoubledRep.nonempty_iso_of_hnFiltration`, from the open-orbit input).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe w u

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

end CategoryTheory.Triangulated
