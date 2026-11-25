/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Tower

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
geometric inputs are the fields of `CategoryTheory.Triangulated.TowerHypotheses`, each citing its
source. None of them mentions the surface or its Picard rank, so the structure and the theorem
live in `CategoryTheory/Triangulated/StabilityCondition/Tower.lean`; this file keeps the old names
as deprecated aliases. The inputs are:

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

## Main declarations

The declarations moved to `CategoryTheory.Triangulated`; the names below are deprecated aliases.

* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses`: the inputs.
* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses.word`: the prefixes `E_j = W_j P`.
* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses.carriesOnce_anchor`: the tower of every
  prefix at the anchor.
* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses.tower`: the tower theorem.
* `AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses.tower_forall`: the same for every HN
  filtration with nonzero factors.

The Mukai budget gives the at-most-once half of the conclusion at every slicing, with no wall
input (`CategoryTheory.Triangulated.TowerHypotheses.atMostOnce_word`), so the tower theorem is the
budget plus the existence of a carrier at the target
(`CategoryTheory.Triangulated.TowerHypotheses.carriesOnce_target_iff`).

## Tags

Harder–Narasimhan filtration, spherical twist, K3 surface, stability condition, wall crossing
-/

namespace AlgebraicGeometry.K3.PicardRankOne

@[deprecated (since := "2026-11-25")]
alias TowerHypotheses := CategoryTheory.Triangulated.TowerHypotheses

@[deprecated (since := "2026-11-25")]
alias TowerHypotheses.word := CategoryTheory.Triangulated.TowerHypotheses.word

@[deprecated (since := "2026-11-25")]
alias TowerHypotheses.pointLike_word := CategoryTheory.Triangulated.TowerHypotheses.pointLike_word

@[deprecated (since := "2026-11-25")]
alias TowerHypotheses.carriesOnce_anchor :=
  CategoryTheory.Triangulated.TowerHypotheses.carriesOnce_anchor

@[deprecated (since := "2026-11-25")]
alias TowerHypotheses.tower := CategoryTheory.Triangulated.TowerHypotheses.tower

@[deprecated (since := "2026-11-25")]
alias TowerHypotheses.tower_forall := CategoryTheory.Triangulated.TowerHypotheses.tower_forall

end AlgebraicGeometry.K3.PicardRankOne
