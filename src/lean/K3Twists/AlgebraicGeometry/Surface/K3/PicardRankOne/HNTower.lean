/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WallCrossing

/-!
# The Harder–Narasimhan tower of a twisted point

The tower theorem of the draft *Harder–Narasimhan towers of spherical twist words on a
Picard-rank-one K3 surface* ("The tower algorithm"). Let `X` be a K3 surface with `Pic X = ℤH`,
`P = 𝒪_x` a skyscraper sheaf, `V_j = T_{Y_j}^{±1}` spherical twists, `W_j = V_j ⋯ V_1` and
`E_j = W_j P`. For a stability condition `σ`, the stable constituents of the HN factors of
`W_ℓ P` include exactly one isotropic object, with multiplicity one, and every other constituent
is spherical.

The proof is an induction on the length of the word. At the generic anchor `η` in the geometric
chamber the tower of `P` is `0 → P`. Given the tower of `E_j` at `η`, transport it along a path of
walls to `V_{j+1}⁻¹ η`: at each wall group the incoming factors by their wall phase, refine each
wall group by its outgoing flag, and insert the flags by homotopy pullback. Then apply `V_{j+1}`:
an exact equivalence carries `P_{V⁻¹η}(φ)` to `P_η(φ)`, so the image is the tower of `E_{j+1}` at
`η`, by uniqueness of HN filtrations. A last path of walls reaches `σ`.

## What is proved and what is assumed

Mathlib has neither `D^b(X)` nor stability conditions on it, so `C` is an abstract triangulated
category standing for `D^b(X)`, a stability condition enters through its slicing, and the
geometric inputs are the fields of `TowerHypotheses`, each citing its source:

* the point is stable at the anchor (Bayer–Bridgeland, arXiv:1310.8266, Theorem 2.2 and
  Lemma 6.7; the draft's "Visibility on the cover");
* a letter matches the constituents of `P_s(φ)` with those of `P_{V s}(φ)`, preserving isotropy and
  sphericity (Bridgeland, arXiv:math/0212237, §8: the action of autoequivalences on
  stability conditions; an autoequivalence preserves the Mukai pairing);
* for each letter, a finite path of walls from `η` to `V⁻¹ η` ("How to find the next wall"), and at
  each wall the grouping into wall groups and the outgoing flag of each group (the draft's
  two-extension lemma and rigid-wall proposition, with Bayer–Bridgeland, arXiv:1310.8266,
  Lemmas 2.5–2.7 and Remark 2.8), packaged as `WallCrossing`.

From these, Lean proves the induction (`TowerHypotheses.tower`): the insertion of the outgoing
flags by homotopy pullback (`HNFiltration.exists_refinement`, from the octahedral axiom alone),
the ordering of the inserted phases, the transport of HN filtrations through each letter
(`TriEquiv.mapHN`), and the identification with the HN tower by uniqueness
(`HNFiltration.exists_iso_of_nonzero`), which also makes the conclusion hold for every HN
filtration of `W P` with nonzero factors (`TowerHypotheses.tower_forall`).

The properties `carrier s M` ("the stable constituents of `M` in the phase slice of `s` are one
isotropic object, once, and spheres") and `spherical s M` ("all constituents spherical") are
fields: Jordan–Hölder constituents in a phase slice and Mukai vectors are not formalized. In an
open chamber the draft's stronger statement (the factor carrying the point is stable, the others
isotypic) is the same induction with the stronger properties.

## Main definitions

* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses`: the inputs.
* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses.word`: the prefixes `E_j = W_j P`.

## Main results

* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses.carriesOnce_anchor`: the tower of every
  prefix at the anchor.
* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses.tower`: the tower theorem.
* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses.tower_forall`: the same for every HN
  filtration with nonzero factors.

## Tags

Harder–Narasimhan filtration, spherical twist, K3 surface, stability condition, wall crossing
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

/-- **The inputs of the tower theorem.** `C` stands for `D^b(X)`, a slicing for the slicing of a
stability condition in `Stab†(X)`, `point` for `P = 𝒪_x` and `letter j` for the `(j+1)`-st letter
`V_{j+1} = T_{Y_{j+1}}^{±1}`. -/
structure TowerHypotheses (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The skyscraper sheaf `P = 𝒪_x`. -/
  point : C
  /-- The letters: `letter j` is `V_{j+1} = T_{Y_{j+1}}^{ε_{j+1}}`, an exact autoequivalence. -/
  letter : ℕ → TriEquiv C
  /-- The length `ℓ` of the word. -/
  length : ℕ
  /-- The slicing of the generic anchor `η` in the geometric chamber. -/
  anchor : Slicing C
  /-- The slicing of the target stability condition `σ`. -/
  target : Slicing C
  /-- `carrier s M`: the stable constituents of `M` in its phase slice for `s` are one isotropic
  object, with multiplicity one, and spherical objects. -/
  carrier : Slicing C → ObjectProperty C
  /-- `spherical s M`: every stable constituent of `M` in its phase slice for `s` is spherical. -/
  spherical : Slicing C → ObjectProperty C
  carrier_iso : ∀ s, (carrier s).IsClosedUnderIsomorphisms
  spherical_iso : ∀ s, (spherical s).IsClosedUnderIsomorphisms
  /-- The objects with the self-extensions of a point, `e(E) = dim Ext¹(E, E) = 2`; the wall
  inputs are stated for them. -/
  pointLike : ObjectProperty C
  /-- `e(𝒪_x) = 2`. -/
  pointLike_point : pointLike point
  /-- An exact autoequivalence preserves `Ext¹(E, E)`. -/
  pointLike_letter : ∀ j E, pointLike E → pointLike ((letter j).e.functor.obj E)
  /-- `𝒪_x ≠ 0`. -/
  point_nonzero : ¬IsZero point
  /-- `𝒪_x` is stable at the geometric anchor (Bayer–Bridgeland, arXiv:1310.8266, Theorem 2.2
  and Lemma 6.7; the draft's "Visibility on the cover"). -/
  point_semistable : ∃ φ, anchor.P φ point
  /-- A stable `𝒪_x` is its own single constituent, isotropic. -/
  carrier_point : carrier anchor point
  /-- A letter carries `P_s(φ)` to `P_{V s}(φ)` and its stable objects to stable objects,
  preserving the Mukai pairing, hence isotropy (Bridgeland, arXiv:math/0212237, §8). -/
  carrier_letter : ∀ j s X,
    carrier ((letter j).act s) ((letter j).e.functor.obj X) ↔ carrier s X
  /-- Likewise for sphericity (Seidel–Thomas, arXiv:math/0001043: autoequivalences preserve
  spherical objects). -/
  spherical_letter : ∀ j s X,
    spherical s X → spherical ((letter j).act s) ((letter j).e.functor.obj X)
  /-- For each letter, a finite path of walls from `η` to `V⁻¹ η` with the local inputs at each
  wall (the draft, "How to find the next wall" and "The filtration on the other side of a
  wall"). -/
  leg : ℕ → Leg carrier spherical pointLike
  leg_start : ∀ j, (leg j).chamber 0 = anchor
  leg_end : ∀ j, (leg j).chamber (leg j).n = (letter j).symm.act anchor
  /-- The last path of walls, from `η` towards `σ`. -/
  final : Leg carrier spherical pointLike
  final_start : final.chamber 0 = anchor
  /-- Arriving at `σ`: if `σ` lies in a chamber this is its chamber; if `σ` lies on walls, the
  incoming factors of each real phase are merged into one wall group ("Evaluate at the
  target"). -/
  final_target : ∀ E, pointLike E →
    (final.chamber final.n).CarriesOnce (carrier (final.chamber final.n))
      (spherical (final.chamber final.n)) E →
    target.CarriesOnce (carrier target) (spherical target) E

namespace TowerHypotheses

attribute [instance] carrier_iso spherical_iso

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (T : TowerHypotheses C)

/-- The prefixes `E_j = W_j P`: `E₀ = P` and `E_{j+1} = V_{j+1} E_j`. -/
def word : ℕ → C
  | 0 => T.point
  | j + 1 => (T.letter j).e.functor.obj (word j)

/-- Every prefix has the self-extensions of a point. -/
theorem pointLike_word : ∀ j, T.pointLike (T.word j)
  | 0 => T.pointLike_point
  | j + 1 => T.pointLike_letter j _ (pointLike_word j)

/-- **The tower at the anchor.** For every prefix `E_j`, exactly one HN factor at `η` carries the
point and every other factor is spherical: transport the tower of `E_j` along the walls to
`V⁻¹ η`, then apply `V`. -/
theorem carriesOnce_anchor [IsTriangulated C] :
    ∀ j, T.anchor.CarriesOnce (T.carrier T.anchor) (T.spherical T.anchor) (T.word j)
  | 0 => by
      obtain ⟨φ, hφ⟩ := T.point_semistable
      exact T.anchor.carriesOnce_of_semistable hφ T.point_nonzero T.carrier_point
  | j + 1 => by
      have h₀ := carriesOnce_anchor j
      rw [← T.leg_start j] at h₀
      have h₁ := (T.leg j).carriesOnce (T.pointLike_word j) h₀
      rw [T.leg_end j] at h₁
      have h₂ := (T.letter j).carriesOnce_map (T.carrier_letter j _) (T.spherical_letter j _) h₁
      rwa [TriEquiv.act_symm_act] at h₂

/-- **The tower theorem.** At the target `σ`, exactly one HN factor of `W P` carries the point,
once, and every other factor is spherical. -/
theorem tower [IsTriangulated C] :
    T.target.CarriesOnce (T.carrier T.target) (T.spherical T.target) (T.word T.length) := by
  have h₀ := T.carriesOnce_anchor T.length
  rw [← T.final_start] at h₀
  exact T.final_target _ (T.pointLike_word _) (T.final.carriesOnce (T.pointLike_word _) h₀)

/-- **The tower theorem for every HN filtration.** Every HN filtration of `W P` at `σ` with
nonzero factors has exactly one factor carrying the point, and its other factors are
spherical. -/
theorem tower_forall [IsTriangulated C] (F : HNFiltration C T.target.P (T.word T.length))
    (hF : ∀ i, ¬IsZero (F.factor i)) :
    F.CarriesOnce (T.carrier T.target) (T.spherical T.target) :=
  T.tower.forall F hF

end TowerHypotheses

end AlgebraicGeometry.K3.PicardRankOne
