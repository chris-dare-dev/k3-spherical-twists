/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Slicing.HarderNarasimhan
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Insertion

/-!
# Carrying an HN tower across walls

The bookkeeping of the tower algorithm in the draft *Harder–Narasimhan towers of spherical twist
words on a Picard-rank-one K3 surface* ("The tower algorithm", "Recovering the arrows and closing
the induction"), for an abstract triangulated category and abstract properties of HN factors.

Fix, for every slicing `s`, two isomorphism-closed properties of objects: `Pt s` (in the draft:
the stable constituents are one isotropic object, once, and spheres) and `Rg s` (all stable
constituents spherical). An HN filtration *carries the point once* (`HNFiltration.CarriesOnce`)
when its factors are nonzero, exactly one has `Pt s`, and each has `Pt s` or `Rg s`. By
uniqueness of HN filtrations this is a property of the object (`Slicing.CarriesOnce`,
`Slicing.CarriesOnce.forall`).

A wall crossing (`WallCrossing`) between an incoming chamber `t₁` and an outgoing chamber `t₂`
through a wall `w` is given by two local inputs: the grouping of the incoming factors into wall
groups, and, for each wall group, an outgoing filtration whose phases stay in a window around its
wall phase, the windows of different groups being ordered. Inserting the outgoing flags by
homotopy pullback (`HNFiltration.exists_refinement`) gives the outgoing HN filtration, and the
property is carried across (`WallCrossing.carriesOnce`). An exact autoequivalence `Φ` matching the
properties carries the property from `s` to `Φ s` (`TriEquiv.carriesOnce_map`). A finite path of
crossings, `Leg`, is in `StabilityCondition/Tower.lean`, with the split of `CarriesOnce` into its
at-most-once half, which the Mukai budget gives at every slicing, and its existence half.

## Main definitions

* `HNFiltration.CarriesOnce`, `Slicing.CarriesOnce`: exactly one factor carries the point.
* `WallCrossing`: the local inputs at one wall.

## Main results

* `Slicing.CarriesOnce.forall`: the property holds for every HN filtration with nonzero factors.
* `WallCrossing.carriesOnce`: crossing one wall.
* `TriEquiv.carriesOnce_map`: applying a letter.

## Tags

Harder–Narasimhan filtration, wall crossing, slicing, autoequivalence
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace CategoryTheory.Triangulated

open WeakStabilityCondition.StabilityCondition.GroupAction

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Carrying the point once -/

/-- An HN filtration *carries the point once* for properties `Pt` and `Rg` of its factors: its
factors are nonzero, exactly one of them has `Pt`, and each has `Pt` or `Rg`. -/
structure HNFiltration.CarriesOnce {P : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (Pt Rg : ObjectProperty C) : Prop where
  /-- Every factor is nonzero. -/
  nonzero : ∀ i, ¬IsZero (F.factor i)
  /-- Exactly one factor has `Pt`. -/
  count_eq_one : F.count Pt = 1
  /-- Every factor has `Pt` or `Rg`. -/
  pt_or_rg : ∀ i, Pt (F.factor i) ∨ Rg (F.factor i)

/-- An object *carries the point once* for a slicing `s` if one of its HN filtrations does; by
`Slicing.CarriesOnce.forall` every HN filtration with nonzero factors then does. -/
def Slicing.CarriesOnce (s : Slicing C) (Pt Rg : ObjectProperty C) (E : C) : Prop :=
  ∃ F : HNFiltration C s.P E, F.CarriesOnce Pt Rg

/-- A semistable nonzero object with `Pt` carries the point once: its HN filtration has one
factor. -/
theorem Slicing.carriesOnce_of_semistable (s : Slicing C) {Pt Rg : ObjectProperty C} {E : C}
    {φ : ℝ} (hE : s.P φ E) (hE0 : ¬IsZero E) (hPt : Pt E) : s.CarriesOnce Pt Rg E := by
  classical
  refine ⟨HNFiltration.single C E φ hE, ⟨fun _ => hE0, ?_, fun _ => Or.inl hPt⟩⟩
  change (∑ _i : Fin 1, if Pt E then 1 else 0) = 1
  simp [hPt]

/-- **Uniqueness.** If an object carries the point once for `s`, so does every HN filtration of
it for `s` whose factors are nonzero. -/
theorem Slicing.CarriesOnce.forall {s : Slicing C} {Pt Rg : ObjectProperty C}
    [Pt.IsClosedUnderIsomorphisms] [Rg.IsClosedUnderIsomorphisms] {E : C}
    (h : s.CarriesOnce Pt Rg E) (G : HNFiltration C s.P E) (hG : ∀ j, ¬IsZero (G.factor j)) :
    G.CarriesOnce Pt Rg := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨hn, hi⟩ := F.exists_iso_of_nonzero s G hF.nonzero hG
  refine ⟨hG, ?_, fun j => ?_⟩
  · rw [← PostnikovTower.count_eq_of_iso F.toPostnikovTower G.toPostnikovTower hn
      (fun i => (hi i).2) Pt]
    exact hF.count_eq_one
  · obtain ⟨e⟩ := (hi (Fin.cast hn.symm j)).2
    have hj : Fin.cast hn (Fin.cast hn.symm j) = j := Fin.ext rfl
    rw [hj] at e
    exact (hF.pt_or_rg _).imp (Pt.prop_of_iso e) (Rg.prop_of_iso e)

/-- Carrying the point once is invariant under isomorphism of objects. -/
theorem Slicing.CarriesOnce.of_iso {s : Slicing C} {Pt Rg : ObjectProperty C} {E E' : C}
    (h : s.CarriesOnce Pt Rg E) (e : E ≅ E') : s.CarriesOnce Pt Rg E' := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.ofIso C e, ⟨hF.nonzero, hF.count_eq_one, hF.pt_or_rg⟩⟩

/-! ### One wall -/

/-- **The local inputs at one wall.** An incoming chamber `t₁`, the wall `w` and an outgoing
chamber `t₂`, for the objects of a class `𝒪` (in the draft, objects with the self-extensions of
a point, `e(E) = 2`). -/
structure WallCrossing (t₁ w t₂ : Slicing C) (Pt Rg : Slicing C → ObjectProperty C)
    (𝒪 : ObjectProperty C) : Prop where
  /-- Grouping: consecutive incoming factors of one limiting phase merge into a wall group, and
  the property passes to the wall groups (in the draft: "There is always an isotropic
  constituent", by Mukai's inequality, Bayer–Bridgeland arXiv:1310.8266, Lemma 2.5, and the
  rigid-factor lemma, ibid., Lemmas 2.6, 3.3 and Proposition 3.4). -/
  wall_of_incoming : ∀ E, 𝒪 E → t₁.CarriesOnce (Pt t₁) (Rg t₁) E →
    w.CarriesOnce (Pt w) (Rg w) E
  /-- Outgoing flags: each wall group has an outgoing HN filtration, in a phase window around
  its wall phase, the windows of later groups below those of earlier ones (Bayer–Bridgeland,
  arXiv:1310.8266, Lemma 2.7 and Remark 2.8); the group carrying the point keeps it once (the
  draft's two-extension lemma) and a spherical group stays spherical (the draft's rigid-wall
  proposition). -/
  outgoing : ∀ E, 𝒪 E → ∀ W : HNFiltration C w.P E, W.CarriesOnce (Pt w) (Rg w) →
    ∃ G : ∀ k : Fin W.n, HNFiltration C t₂.P (W.factor k),
      (∀ k l : Fin W.n, k < l → ∀ i j, (G l).φ j < (G k).φ i) ∧
      (∀ k, Pt w (W.factor k) → (G k).CarriesOnce (Pt t₂) (Rg t₂)) ∧
      (∀ k, Rg w (W.factor k) → ¬Pt w (W.factor k) →
        (∀ i, ¬IsZero ((G k).factor i)) ∧ (∀ i, ¬Pt t₂ ((G k).factor i)) ∧
          ∀ i, Rg t₂ ((G k).factor i))

namespace WallCrossing

variable {t₁ w t₂ : Slicing C} {Pt Rg : Slicing C → ObjectProperty C} {𝒪 : ObjectProperty C}

/-- **Crossing one wall.** If an object of `𝒪` carries the point once for the incoming chamber,
it carries it once for the outgoing chamber: insert the outgoing flags of its wall groups by
homotopy pullback. -/
theorem carriesOnce [IsTriangulated C] [∀ s, (Pt s).IsClosedUnderIsomorphisms]
    [∀ s, (Rg s).IsClosedUnderIsomorphisms] (hw : WallCrossing t₁ w t₂ Pt Rg 𝒪) {E : C}
    (hE : 𝒪 E) (h : t₁.CarriesOnce (Pt t₁) (Rg t₁) E) : t₂.CarriesOnce (Pt t₂) (Rg t₂) E := by
  classical
  obtain ⟨W, hW⟩ := hw.wall_of_incoming E hE h
  obtain ⟨G, hsep, hpt, hrg⟩ := hw.outgoing E hE W hW
  obtain ⟨H, hprov, hcount⟩ := W.exists_refinement G hsep
  -- Each piece is nonzero and has `Pt` or `Rg`, and carries `Pt` exactly when its group does.
  have hpiece : ∀ k, (∀ i, ¬IsZero ((G k).factor i)) ∧
      (∀ i, Pt t₂ ((G k).factor i) ∨ Rg t₂ ((G k).factor i)) ∧
      (G k).count (Pt t₂) = if Pt w (W.factor k) then 1 else 0 := by
    intro k
    by_cases hk : Pt w (W.factor k)
    · obtain ⟨h0, h1, h2⟩ := hpt k hk
      exact ⟨h0, h2, by simp [h1, hk]⟩
    · have hr : Rg w (W.factor k) := (hW.pt_or_rg k).resolve_left hk
      obtain ⟨h0, h1, h2⟩ := hrg k hr hk
      refine ⟨h0, fun i => Or.inr (h2 i), ?_⟩
      simp [PostnikovTower.count, h1, hk]
  refine ⟨H, ⟨fun i => ?_, ?_, fun i => ?_⟩⟩
  · obtain ⟨k, j, -, ⟨e⟩⟩ := hprov i
    exact fun hz => (hpiece k).1 j (hz.of_iso e.symm)
  · rw [hcount (Pt t₂), Finset.sum_congr rfl (fun k _ => (hpiece k).2.2)]
    exact hW.count_eq_one
  · obtain ⟨k, j, -, ⟨e⟩⟩ := hprov i
    exact ((hpiece k).2.1 j).imp ((Pt t₂).prop_of_iso e.symm) ((Rg t₂).prop_of_iso e.symm)

/-- **Stopping on a wall.** An object of `𝒪` that carries the point once for the incoming
chamber carries it once for the wall: the algorithm returns the entire extension of each wall
phase. -/
theorem carriesOnce_wall (hw : WallCrossing t₁ w t₂ Pt Rg 𝒪) {E : C} (hE : 𝒪 E)
    (h : t₁.CarriesOnce (Pt t₁) (Rg t₁) E) : w.CarriesOnce (Pt w) (Rg w) E :=
  hw.wall_of_incoming E hE h

end WallCrossing

/-! ### One letter -/

namespace WeakStabilityCondition.StabilityCondition.GroupAction.TriEquiv

/-- **Applying a letter.** An exact autoequivalence `Φ` that matches the properties of `s` with
those of `Φ s` carries the property from `E` at `s` to `Φ E` at `Φ s`. -/
theorem carriesOnce_map (Φ : TriEquiv C) {s : Slicing C} {Pt Rg : Slicing C →
    ObjectProperty C} (hPt : ∀ X, Pt (Φ.act s) (Φ.e.functor.obj X) ↔ Pt s X)
    (hRg : ∀ X, Rg s X → Rg (Φ.act s) (Φ.e.functor.obj X)) {E : C}
    (h : s.CarriesOnce (Pt s) (Rg s) E) :
    (Φ.act s).CarriesOnce (Pt (Φ.act s)) (Rg (Φ.act s)) (Φ.e.functor.obj E) := by
  classical
  obtain ⟨F, hF⟩ := h
  refine ⟨Φ.mapHN F, ⟨fun i => ?_, ?_, fun i => ?_⟩⟩
  · rw [TriEquiv.mapHN_factor, TriEquiv.isZero_functor_obj_iff]
    exact hF.nonzero i
  · rw [← hF.count_eq_one]
    unfold PostnikovTower.count
    exact Finset.sum_congr rfl (fun i _ => if_congr (hPt _) rfl rfl)
  · rw [TriEquiv.mapHN_factor]
    exact (hF.pt_or_rg i).imp (hPt _).mpr (hRg _)

end WeakStabilityCondition.StabilityCondition.GroupAction.TriEquiv

end CategoryTheory.Triangulated
