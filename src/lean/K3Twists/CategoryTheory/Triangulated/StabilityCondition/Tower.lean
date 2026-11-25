/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Budget
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WallCrossing

/-!
# The tower property: the Mukai budget plus existence of a carrier

An HN filtration *carries the point once* (`HNFiltration.CarriesOnce`) when its factors are
nonzero, exactly one has the property `Pt` and each has `Pt` or `Rg`. This file splits that
property in two (`HNFiltration.carriesOnce_iff`):

* **at most once** (`HNFiltration.AtMostOnce`): at most one factor has `Pt`, and every factor has
  `Pt` or `Rg`;
* **existence** (`Slicing.HasCarrier`): some HN filtration with nonzero factors has a factor with
  `Pt`.

For `Pt := (e = 2)` and `Rg := (e = 0)`, with `e` a Mukai budget, the first half is a theorem at
every slicing, for every HN filtration of an object with `e(E) = 2`, with no wall, path, word or
Picard rank (`MukaiBudget.atMostOnce_e`); it needs only that no factor has `e = 1`. Existence is
the vanishing of the budget defect: an HN filtration with nonzero factors has a factor with `e = 2`
exactly when `∑ e(M_i) = e(E)` (`MukaiBudget.carriesOnce_e_iff`). Existence is independent of the
budget: near the wall that contracts a `(-2)`-curve `C`, on the side where `𝒪_C` has the larger
phase, a point `𝒪_x` with `x ∈ C` has the two rigid HN factors `𝒪_C` and `𝒪_C(-1)[1]`
(`PairingTwoWallHypotheses.hn_P_of_phase_gt`; in triangulated form in
`K3TwistsTest/PairingTwoWallTowerModel.lean`). So the tower theorem is the budget plus the
transport of a carrier along the path, wall by wall; the transport is the wall input
(`WallCrossing`), not a consequence of the budget.

The second part of the file holds the inputs of the tower theorem, a finite path of walls (`Leg`)
and `TowerHypotheses`, moved here from `WallCrossing.lean` and from the Picard-rank-one directory:
none of their fields mentions a K3 surface or a Picard rank. The budget re-derives the
at-most-once half of the tower theorem at every slicing (`TowerHypotheses.atMostOnce_word`), shows
that the tower theorem forces zero defect at the target (`TowerHypotheses.sum_e_eq_two`), and that
given the pointwise links between the carrier predicates and `e`, the conclusion of the tower
theorem is equivalent to its existence half (`TowerHypotheses.carriesOnce_target_iff`).

## Main definitions

* `HNFiltration.AtMostOnce`, `Slicing.HasCarrier`: the two halves of `CarriesOnce`.
* `Leg`: a finite path of wall crossings.
* `TowerHypotheses`: the inputs of the tower theorem.

## Main results

* `HNFiltration.carriesOnce_iff`: `CarriesOnce ↔ nonzero factors ∧ AtMostOnce ∧ ∃ carrier`.
* `MukaiBudget.atMostOnce`, `MukaiBudget.atMostOnce_e`: at most once, from the budget.
* `MukaiBudget.exists_e_eq_two_iff`, `MukaiBudget.carriesOnce_e_iff`: existence is zero defect.
* `Leg.carriesOnce`: following a path of walls.
* `TowerHypotheses.tower`, `TowerHypotheses.tower_forall`: the tower theorem.
* `TowerHypotheses.atMostOnce_word`, `TowerHypotheses.sum_e_eq_two`,
  `TowerHypotheses.carriesOnce_target_iff`: the tower theorem through the budget.

## Tags

Harder–Narasimhan filtration, Mukai's lemma, wall crossing, spherical twist, tower
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace CategoryTheory.Triangulated

open WeakStabilityCondition.StabilityCondition.GroupAction

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Counting factors -/

namespace PostnikovTower

variable {E : C} (T : PostnikovTower C E)

open Classical in
/-- The count of a property is the number of factors that have it. -/
theorem count_eq_card (R : ObjectProperty C) :
    T.count R = (Finset.univ.filter fun i => R (T.factor i)).card := by
  rw [Finset.card_filter]
  rfl

open Classical in
theorem count_mono {Q R : ObjectProperty C} (h : ∀ i, Q (T.factor i) → R (T.factor i)) :
    T.count Q ≤ T.count R := by
  unfold PostnikovTower.count
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hq : Q (T.factor i)
  · simp [hq, h i hq]
  · simp [hq]

open Classical in
theorem one_le_count {Q : ObjectProperty C} {i : Fin T.n} (h : Q (T.factor i)) :
    1 ≤ T.count Q := by
  unfold PostnikovTower.count
  have := Finset.single_le_sum (f := fun j => if Q (T.factor j) then 1 else 0)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  simpa [h] using this

open Classical in
theorem exists_of_count_ne_zero {Q : ObjectProperty C} (h : T.count Q ≠ 0) :
    ∃ i, Q (T.factor i) := by
  by_contra hne
  push Not at hne
  exact h (Finset.sum_eq_zero (fun i _ => by simp [hne i]))

end PostnikovTower

/-! ### At most once, and existence -/

/-- An HN filtration has the properties `Pt` and `Rg` **at most once**: at most one factor has
`Pt`, and every factor has `Pt` or `Rg`. This is `HNFiltration.CarriesOnce` without the existence
of a factor with `Pt` and without asking the factors to be nonzero. -/
structure HNFiltration.AtMostOnce {P : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (Pt Rg : ObjectProperty C) : Prop where
  /-- At most one factor has `Pt`. -/
  count_le_one : F.count Pt ≤ 1
  /-- Every factor has `Pt` or `Rg`. -/
  pt_or_rg : ∀ i, Pt (F.factor i) ∨ Rg (F.factor i)

/-- **Carrying the point once is at most once plus existence**, for factors that are nonzero. -/
theorem HNFiltration.carriesOnce_iff {P : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (Pt Rg : ObjectProperty C) :
    F.CarriesOnce Pt Rg ↔
      (∀ i, ¬IsZero (F.factor i)) ∧ F.AtMostOnce Pt Rg ∧ ∃ i, Pt (F.factor i) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, ⟨h1.le, h2⟩, F.exists_of_count_ne_zero (by rw [h1]; exact one_ne_zero)⟩
  · rintro ⟨h0, ⟨h1, h2⟩, i, hi⟩
    exact ⟨h0, le_antisymm h1 (F.one_le_count hi), h2⟩

/-- **Existence of a carrier**: some HN filtration of `E` for `s` with nonzero factors has a factor
with `Pt`. -/
def Slicing.HasCarrier (s : Slicing C) (Pt : ObjectProperty C) (E : C) : Prop :=
  ∃ F : HNFiltration C s.P E, (∀ i, ¬IsZero (F.factor i)) ∧ ∃ i, Pt (F.factor i)

/-- At most once for every HN filtration, plus existence, gives carrying the point once. -/
theorem Slicing.carriesOnce_of_hasCarrier {s : Slicing C} {Pt Rg : ObjectProperty C} {E : C}
    (hA : ∀ F : HNFiltration C s.P E, F.AtMostOnce Pt Rg) (hC : s.HasCarrier Pt E) :
    s.CarriesOnce Pt Rg E := by
  obtain ⟨F, h0, i, hi⟩ := hC
  exact ⟨F, (F.carriesOnce_iff Pt Rg).mpr ⟨h0, hA F, i, hi⟩⟩

theorem Slicing.CarriesOnce.hasCarrier {s : Slicing C} {Pt Rg : ObjectProperty C} {E : C}
    (h : s.CarriesOnce Pt Rg E) : s.HasCarrier Pt E := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, hF.nonzero, ((F.carriesOnce_iff Pt Rg).mp hF).2.2⟩

/-! ### At most once from the budget -/

namespace MukaiBudget

variable (b : MukaiBudget C)

/-- **At most once from the Mukai budget.** Let `e(E) = 2` and let no HN factor have `e = 1`.
If a factor with `Pt` is not rigid, a rigid factor has `Rg`, and a factor with `e = 2` has `Pt`
or `Rg`, then the filtration has `Pt` and `Rg` at most once.

For the stability properties of the tower theorem (`Pt`: the constituents are one isotropic object
once and spheres; `Rg`: all constituents spherical) the three links are pointwise statements about
semistable objects: Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.6 for the second. Applied at a wall
slicing, this is the at-most-once half of `WallCrossing.wall_of_incoming`. -/
theorem atMostOnce {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    {E : C} (hE : b.e E = 2) (F : HNFiltration C P E) {Pt Rg : ObjectProperty C}
    (hne : ∀ i, b.e (F.factor i) ≠ 1)
    (hPt : ∀ i, Pt (F.factor i) → b.e (F.factor i) ≠ 0)
    (hRg : ∀ i, b.e (F.factor i) = 0 → Rg (F.factor i))
    (hsemi : ∀ i, b.e (F.factor i) = 2 → Pt (F.factor i) ∨ Rg (F.factor i)) :
    F.AtMostOnce Pt Rg where
  count_le_one := by
    calc F.count Pt ≤ F.count (fun X => b.e X ≠ 0) := F.count_mono fun i h => hPt i h
      _ = (Finset.univ.filter fun i => b.e (F.factor i) ≠ 0).card := by
        classical
        rw [F.count_eq_card]
        congr
      _ ≤ b.e E / 2 := b.card_nonrigid_le hvan F hne
      _ = 1 := by rw [hE]
  pt_or_rg i := by
    rcases b.e_factor_eq_zero_or_two hvan hE F hne i with h | h
    · exact Or.inr (hRg i h)
    · exact hsemi i h

/-- **At most one factor with `e = 2`, the others rigid**, for every HN filtration of an object
with `e(E) = 2`, at every slicing (Hom vanishing is the only slicing axiom used). It needs only
that no factor has `e = 1`; no path, word, evenness or Picard rank. -/
theorem atMostOnce_e {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    {E : C} (hE : b.e E = 2) (F : HNFiltration C P E) (hne : ∀ i, b.e (F.factor i) ≠ 1) :
    F.AtMostOnce (fun X => b.e X = 2) (fun X => b.e X = 0) :=
  b.atMostOnce hvan hE F hne (fun i (h : b.e (F.factor i) = 2) => by lia) (fun _ h => h)
    (fun _ h => Or.inl h)

/-- `atMostOnce_e` when `e` takes only even values. -/
theorem atMostOnce_e_of_even {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    (heven : ∀ X, Even (b.e X)) {E : C} (hE : b.e E = 2) (F : HNFiltration C P E) :
    F.AtMostOnce (fun X => b.e X = 2) (fun X => b.e X = 0) :=
  b.atMostOnce_e hvan hE F fun i h => by
    obtain ⟨r, hr⟩ := heven (F.factor i)
    lia

/-- **Existence is zero defect.** For `e(E) = 2` and no factor with `e = 1`, some factor has
`e = 2` exactly when `∑ e(M_i) = e(E)`. -/
theorem exists_e_eq_two_iff {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    {E : C} (hE : b.e E = 2) (F : HNFiltration C P E) (hne : ∀ i, b.e (F.factor i) ≠ 1) :
    (∃ i, b.e (F.factor i) = 2) ↔ ∑ i, b.e (F.factor i) = b.e E := by
  have hsum := b.hn_sum_le hvan F
  constructor
  · rintro ⟨i, hi⟩
    have := Finset.single_le_sum (f := fun j => b.e (F.factor j))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    lia
  · intro h
    by_contra hne'
    push Not at hne'
    have h0 : ∀ i, b.e (F.factor i) = 0 := fun i =>
      (b.e_factor_eq_zero_or_two hvan hE F hne i).resolve_right (hne' i)
    simp [h0] at h
    lia

/-- **The tower property for `e`, as zero defect.** If `e(E) = 2` and no semistable object of `s`
has `e = 1`, then `E` carries `e = 2` once at `s`, with every other factor rigid, exactly when some
HN filtration with nonzero factors has `∑ e(M_i) = e(E)`. By `sum_e_eq_of_nonzero` the sum does not
depend on that filtration. -/
theorem carriesOnce_e_iff (s : Slicing C) {E : C} (hE : b.e E = 2)
    (hne : ∀ φ X, s.P φ X → b.e X ≠ 1) :
    s.CarriesOnce (fun X => b.e X = 2) (fun X => b.e X = 0) E ↔
      ∃ F : HNFiltration C s.P E, (∀ i, ¬IsZero (F.factor i)) ∧
        ∑ i, b.e (F.factor i) = b.e E := by
  have hne' : ∀ F : HNFiltration C s.P E, ∀ i, b.e (F.factor i) ≠ 1 :=
    fun F i => hne _ _ (F.semistable i)
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F, hF.nonzero, (b.exists_e_eq_two_iff s.hom_vanishing hE F (hne' F)).mp
      ((F.carriesOnce_iff _ _).mp hF).2.2⟩
  · rintro ⟨F, h0, hd⟩
    obtain ⟨i, hi⟩ := (b.exists_e_eq_two_iff s.hom_vanishing hE F (hne' F)).mpr hd
    exact Slicing.carriesOnce_of_hasCarrier
      (fun G => b.atMostOnce_e s.hom_vanishing hE G (hne' G)) ⟨F, h0, i, hi⟩

end MukaiBudget

/-! ### A path of walls -/

/-- **A finite path of wall crossings**: chambers `chamber 0, …, chamber n` and walls
`wall 0, …, wall (n - 1)`, the `k`-th wall separating `chamber k` from `chamber (k + 1)`. Between
walls the HN filtration does not change, so only the walls are recorded (in the draft, the
straight legs of a polygon meet finitely many rational alignment lines, "How to find the next
wall"). -/
structure Leg (Pt Rg : Slicing C → ObjectProperty C) (𝒪 : ObjectProperty C) where
  /-- The number of walls. -/
  n : ℕ
  /-- The chambers. -/
  chamber : ℕ → Slicing C
  /-- The walls. -/
  wall : ℕ → Slicing C
  /-- The local inputs at each wall. -/
  crossing : ∀ k < n, WallCrossing (chamber k) (wall k) (chamber (k + 1)) Pt Rg 𝒪

/-- **Following a path of walls.** An object of `𝒪` that carries the point once at the start of
a leg carries it once at its end. -/
theorem Leg.carriesOnce [IsTriangulated C] {Pt Rg : Slicing C → ObjectProperty C}
    [∀ s, (Pt s).IsClosedUnderIsomorphisms] [∀ s, (Rg s).IsClosedUnderIsomorphisms]
    {𝒪 : ObjectProperty C} (L : Leg Pt Rg 𝒪) {E : C} (hE : 𝒪 E)
    (h : (L.chamber 0).CarriesOnce (Pt (L.chamber 0)) (Rg (L.chamber 0)) E) :
    (L.chamber L.n).CarriesOnce (Pt (L.chamber L.n)) (Rg (L.chamber L.n)) E := by
  suffices key : ∀ k ≤ L.n,
      (L.chamber k).CarriesOnce (Pt (L.chamber k)) (Rg (L.chamber k)) E from key L.n le_rfl
  intro k
  induction k with
  | zero => exact fun _ => h
  | succ k ih => exact fun hk => (L.crossing k (by lia)).carriesOnce hE (ih (by lia))

/-! ### The inputs of the tower theorem -/

/-- **The inputs of the tower theorem** of the draft *Harder–Narasimhan towers of spherical twist
words on a Picard-rank-one K3 surface* ("The tower algorithm"). `C` stands for `D^b(X)`, a slicing
for the slicing of a stability condition in `Stab†(X)`, `point` for `P = 𝒪_x` and `letter j` for
the `(j+1)`-st letter `V_{j+1} = T_{Y_{j+1}}^{±1}`. No field mentions the surface or its Picard
rank; the rank enters through the wall inputs (`WallCrossing`) the draft supplies for it. -/
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

/-! ### The tower theorem through the budget -/

variable (b : MukaiBudget C)

/-- Every prefix has budget `2`, when the point-like objects do. -/
theorem e_word (hpt : ∀ E, T.pointLike E → b.e E = 2) (j : ℕ) : b.e (T.word j) = 2 :=
  hpt _ (T.pointLike_word j)

/-- **The at-most-once half of the tower theorem, at every slicing.** For every slicing `s`, every
prefix `W_j P` and every HN filtration of it for `s` with no factor of budget `1`, at most one
factor has `e = 2` and the others are rigid. No wall input, path or letter is used. -/
theorem atMostOnce_word (hpt : ∀ E, T.pointLike E → b.e E = 2) (s : Slicing C) (j : ℕ)
    (F : HNFiltration C s.P (T.word j)) (hne : ∀ i, b.e (F.factor i) ≠ 1) :
    F.AtMostOnce (fun X => b.e X = 2) (fun X => b.e X = 0) :=
  b.atMostOnce_e s.hom_vanishing (T.e_word b hpt j) F hne

/-- **The tower theorem has zero defect at the target.** If carriers at `σ` are not rigid, then
every HN filtration of `W P` at `σ` with nonzero factors and no factor of budget `1` has
`∑ e(M_i) = e(W P) = 2`. -/
theorem sum_e_eq_two [IsTriangulated C] (hpt : ∀ E, T.pointLike E → b.e E = 2)
    (hcar : ∀ X, T.carrier T.target X → b.e X ≠ 0)
    (F : HNFiltration C T.target.P (T.word T.length)) (hF : ∀ i, ¬IsZero (F.factor i))
    (hne : ∀ i, b.e (F.factor i) ≠ 1) :
    ∑ i, b.e (F.factor i) = 2 := by
  obtain ⟨-, -, i, hi⟩ := (F.carriesOnce_iff _ _).mp (T.tower_forall F hF)
  have h2 := (b.e_factor_eq_zero_or_two T.target.hom_vanishing (T.e_word b hpt _) F hne
    i).resolve_left (hcar _ hi)
  rw [← T.e_word b hpt T.length]
  exact (b.exists_e_eq_two_iff T.target.hom_vanishing (T.e_word b hpt _) F hne).mp ⟨i, h2⟩

/-- **The tower theorem is its existence half, given the budget.** Suppose that at `σ` no
semistable object has budget `1`, a semistable carrier is not rigid, a rigid semistable object is
spherical (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.6), and a semistable object of budget `2` is
a carrier or spherical. Then the conclusion of the tower theorem holds exactly when some HN
filtration of `W P` at `σ` with nonzero factors has a carrier factor: the at-most-once half is the
Mukai budget lemma. -/
theorem carriesOnce_target_iff (hpt : ∀ E, T.pointLike E → b.e E = 2)
    (hne : ∀ φ X, T.target.P φ X → b.e X ≠ 1)
    (hcar : ∀ φ X, T.target.P φ X → T.carrier T.target X → b.e X ≠ 0)
    (hsph : ∀ φ X, T.target.P φ X → b.e X = 0 → T.spherical T.target X)
    (hsemi : ∀ φ X, T.target.P φ X → b.e X = 2 →
      T.carrier T.target X ∨ T.spherical T.target X) :
    T.target.CarriesOnce (T.carrier T.target) (T.spherical T.target) (T.word T.length) ↔
      T.target.HasCarrier (T.carrier T.target) (T.word T.length) :=
  ⟨Slicing.CarriesOnce.hasCarrier, Slicing.carriesOnce_of_hasCarrier fun F =>
    b.atMostOnce T.target.hom_vanishing (T.e_word b hpt _) F
      (fun i => hne _ _ (F.semistable i)) (fun i => hcar _ _ (F.semistable i))
      (fun i => hsph _ _ (F.semistable i)) (fun i => hsemi _ _ (F.semistable i))⟩

end TowerHypotheses

end CategoryTheory.Triangulated
