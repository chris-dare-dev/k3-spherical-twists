/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Tower
import K3Twists.LinearAlgebra.Lattice.Mukai.SphericalConfiguration

/-!
# The split tower theorem: the Mukai budget plus transport of a carrier, step by step

The tower theorem (`TowerHypotheses.tower`) says that at the target slicing exactly one HN factor of
a twisted point `W 𝒪_x` carries the point, once, and every other factor is spherical. This file
states it in a split form (`SplitTowerHypotheses.tower`):

* **at most once** holds at every slicing for every object with `e(E) = 2`, from the Mukai budget
  and four pointwise links between the carrier predicates and `e` (`SliceFields.atMostOnce`);
* **existence** of a carrier (`Slicing.HasCarrier`) is carried along a path of slicings one step
  at a time (`CarrierStep`, `CarrierPath`), and through each letter of the word.

## What is assumed and what is gone

**Transport of a carrier is assumed, per step.** A `CarrierStep` from `t₁` to `t₂` carries, for
each phase `φ`, an index type `ι φ` and an integer matrix `gram φ`, and one field: if an object with
`e(E) = 2` has a carrier at `t₁` and none at `t₂`, some `gram φ` has an isotropic sum with natural
coefficients (`Matrix.IsotropicSphereSum`). In this structure `ι` and `gram` are free data, tied to
no wall, object or class map: a step with an anisotropic `gram` exists exactly when carriers of
objects with `e(E) = 2` pass from `t₁` to `t₂` (`CarrierStep.exists_anisotropic_iff`). So the
anisotropy fields of `SplitTowerHypotheses` are carrier transport restated. What drops out of the
proof is the *octahedral* proof of transport: `IsTriangulated`, wall slicings, outgoing flags and
their ordering, the sphericity of letters and uniqueness of HN filtrations are not used by
`SplitTowerHypotheses.tower`. The field has lattice content only once the Gram matrix of a step is
defined from the classes of the stable spherical objects of each phase of a named wall and the
field is proved from constituent-level inputs; this file does not do that.

**The slice fields are used, not needed.** `SliceFields` holds for `carrier := (e = 2)` and
`spherical := (e = 0)` and every budget with no semistable object of budget `1`
(`SliceFields.ofBudget`); its content lies in the predicates it is applied to. The tower theorem
uses it at the target, to turn existence into carrying the point once.

**The old structure gives the new one, at a cost** (`SplitTowerHypotheses.ofTowerHypotheses`):
besides `TowerHypotheses` it needs a Mukai budget, `SliceFields`, that objects with `e = 2` are
point-like, `e(𝒪_x) = 2` and invariance of `e` under the letters. Each wall crossing becomes a step
whose Gram matrices are all empty, so the anisotropy fields carry no lattice content there, and the
old `final_target` is absorbed into the last step of the final path, not removed. The new structure
as a whole is not weaker than the old one: it needs the slice fields and the budget.

**What the outgoing clause keeps.** `outgoing_noncarrier` proves the sphericity part of the third
clause of `WallCrossing.outgoing` from the budget and the slice fields; it does not give the
nonzero-factor conjunct of that clause, nor the existence and ordering of the outgoing flags. Rigid
wall uniqueness is not needed only because existence of a carrier is assumed step by step.

The public form of the tower theorem in higher Picard rank (the rank-one form, this rank-free form,
or both) is not decided here: `TowerHypotheses` and its theorem are kept unchanged.

## Main definitions

* `SliceFields`: Bayer–Bridgeland's rigid-implies-spherical, the carrier dichotomy for semirigid
  semistable objects, no budget `1`.
* `CarrierStep`, `CarrierPath`: transport of a carrier, with the anisotropy of each step.
* `SplitTowerHypotheses`: the inputs of the split tower theorem.

## Main results

* `SliceFields.atMostOnce`: at most once, at every slicing.
* `CarrierStep.keep`, `CarrierPath.keep`: an anisotropic step or path keeps a carrier.
* `CarrierStep.exists_anisotropic_iff`: an anisotropic step exists iff carriers are transported.
* `SplitTowerHypotheses.tower`, `SplitTowerHypotheses.tower_forall`: the split tower theorem.
* `outgoing_noncarrier`, `wall_atMostOnce`: what remains of the outgoing and wall clauses.
* `SplitTowerHypotheses.ofTowerHypotheses`, `SplitTowerHypotheses.tower_ofTowerHypotheses`: the old
  inputs give the new ones, and the two theorems agree.

## References

* A. Bayer, T. Bridgeland, *Derived automorphism groups of K3 surfaces of Picard rank 1*,
  arXiv:1310.8266, Lemmas 2.5 and 2.6.

## Tags

Harder–Narasimhan filtration, Mukai's lemma, wall crossing, spherical twist, tower, isotropic
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace CategoryTheory.Triangulated

open WeakStabilityCondition.StabilityCondition.GroupAction

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### The slice fields -/

/-- **The slice fields**: pointwise links, for the semistable objects of every slicing, between the
predicates `carrier s` ("one isotropic stable constituent, once, and spheres") and `spherical s`
("all stable constituents spherical") and the budget `e`. The split tower theorem uses them; they
hold for `carrier := (e = 2)` and `spherical := (e = 0)` (`SliceFields.ofBudget`), so their content
lies in the predicates. -/
structure SliceFields (b : MukaiBudget C) (carrier spherical : Slicing C → ObjectProperty C) :
    Prop where
  /-- No semistable object has budget `1`. On a 2-Calabi–Yau category `e` is even
  (`TwoCYHypotheses.even`). -/
  ne_one : ∀ (s : Slicing C) (φ : ℝ) (M : C), s.P φ M → b.e M ≠ 1
  /-- **Rigid implies spherical**: a rigid semistable object has only spherical stable
  constituents (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.6). -/
  rigid_spherical : ∀ (s : Slicing C) (φ : ℝ) (M : C), s.P φ M → b.e M = 0 → spherical s M
  /-- A carrier is not spherical: its isotropic constituent is not a sphere. -/
  carrier_not_spherical : ∀ (s : Slicing C) (M : C), carrier s M → ¬spherical s M
  /-- A semistable object with `e = 2` is a carrier or has only spherical constituents. -/
  semirigid : ∀ (s : Slicing C) (φ : ℝ) (M : C), s.P φ M → b.e M = 2 →
    carrier s M ∨ spherical s M

/-- **The slice fields hold for the budget predicates** `carrier := (e = 2)`,
`spherical := (e = 0)`, as soon as no semistable object has budget `1`. -/
theorem SliceFields.ofBudget (b : MukaiBudget C)
    (hne : ∀ (s : Slicing C) (φ : ℝ) (M : C), s.P φ M → b.e M ≠ 1) :
    SliceFields b (fun _ X => b.e X = 2) (fun _ X => b.e X = 0) where
  ne_one := hne
  rigid_spherical _ _ _ _ h := h
  carrier_not_spherical _ _ h h' := by simp_all
  semirigid _ _ _ _ h := Or.inl h

/-- **At most once, at every slicing.** For `e(E) = 2`, every HN filtration of `E` at every slicing
has at most one carrier factor, and every other factor is spherical. No wall, path, word or Picard
rank is used. -/
theorem SliceFields.atMostOnce {b : MukaiBudget C}
    {carrier spherical : Slicing C → ObjectProperty C} (hS : SliceFields b carrier spherical)
    (s : Slicing C) {E : C} (hE : b.e E = 2) (F : HNFiltration C s.P E) :
    F.AtMostOnce (carrier s) (spherical s) :=
  b.atMostOnce s.hom_vanishing hE F (fun i => hS.ne_one s _ _ (F.semistable i))
    (fun i hc h0 => hS.carrier_not_spherical s _ hc (hS.rigid_spherical s _ _ (F.semistable i) h0))
    (fun i => hS.rigid_spherical s _ _ (F.semistable i))
    (fun i => hS.semirigid s _ _ (F.semistable i))

/-- With the slice fields, carrying the point once at `s` is existence of a carrier at `s`. -/
theorem SliceFields.carriesOnce_iff_hasCarrier {b : MukaiBudget C}
    {carrier spherical : Slicing C → ObjectProperty C} (hS : SliceFields b carrier spherical)
    (s : Slicing C) {E : C} (hE : b.e E = 2) :
    s.CarriesOnce (carrier s) (spherical s) E ↔ s.HasCarrier (carrier s) E :=
  ⟨Slicing.CarriesOnce.hasCarrier,
    Slicing.carriesOnce_of_hasCarrier fun F => hS.atMostOnce s hE F⟩

/-! ### One step and a path -/

/-- **One step of transport.** Between slicings `t₁` and `t₂`, for each phase `φ` an index type
`ι φ` and an integer matrix `gram φ`, standing for the Gram matrix of the classes of the stable
spherical objects of phase `φ` at the wall crossed, and the transport field: if `E` with `e(E) = 2`
has a carrier at `t₁` and none at `t₂`, then some `gram φ` has an isotropic sum with natural
coefficients.

The data are per phase, not per wall: anisotropy is not closed under orthogonal sums
(`Matrix.isotropic_block`). In this structure they are free: any isotropic matrix gives a step
between any two slicings, and an anisotropic step exists exactly when carriers are transported
(`CarrierStep.exists_anisotropic_iff`). -/
structure CarrierStep (b : MukaiBudget C) (carrier : Slicing C → ObjectProperty C)
    (t₁ t₂ : Slicing C) where
  /-- The index type of phase `φ`: the stable spherical objects of that phase at the wall. -/
  ι : ℝ → Type u
  /-- The matrix of phase `φ`: the Gram matrix of their classes. -/
  gram : ∀ φ, Matrix (ι φ) (ι φ) ℤ
  /-- **A lost carrier forces an isotropic sphere sum** in one phase. -/
  lost_isotropic : ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E →
    ¬t₂.HasCarrier (carrier t₂) E → ∃ φ, (gram φ).IsotropicSphereSum

namespace CarrierStep

variable {b : MukaiBudget C} {carrier : Slicing C → ObjectProperty C} {t₁ t₂ : Slicing C}

/-- The anisotropy of a step: no phase has an isotropic sphere sum. -/
def Anisotropic (S : CarrierStep b carrier t₁ t₂) : Prop :=
  ∀ φ, ¬(S.gram φ).IsotropicSphereSum

/-- **An anisotropic step keeps a carrier.** -/
theorem keep (S : CarrierStep b carrier t₁ t₂) (han : S.Anisotropic) {E : C} (hE : b.e E = 2)
    (h : t₁.HasCarrier (carrier t₁) E) : t₂.HasCarrier (carrier t₂) E := by
  by_contra hn
  obtain ⟨φ, hφ⟩ := S.lost_isotropic E hE h hn
  exact han φ hφ

/-- **The step of a transport statement**: if carriers of objects with `e(E) = 2` pass from `t₁`
to `t₂`, the step with empty index types. Its Gram matrices are empty, so its anisotropy carries
no lattice content. -/
def ofTransport (h : ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E → t₂.HasCarrier (carrier t₂) E) :
    CarrierStep b carrier t₁ t₂ where
  ι := fun _ => PEmpty
  gram := fun _ => 0
  lost_isotropic E hE h₁ h₂ := absurd (h E hE h₁) h₂

theorem anisotropic_ofTransport
    (h : ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E → t₂.HasCarrier (carrier t₂) E) :
    (ofTransport h).Anisotropic := fun φ =>
  haveI : IsEmpty ((ofTransport h).ι φ) := inferInstanceAs (IsEmpty PEmpty)
  Matrix.not_isotropicSphereSum_of_isEmpty _

/-- **An anisotropic step is transport restated.** An anisotropic step from `t₁` to `t₂` exists
exactly when every object with `e(E) = 2` that has a carrier at `t₁` has one at `t₂`. So with free
Gram matrices the anisotropy of a step is an assumption of transport. -/
theorem exists_anisotropic_iff :
    (∃ S : CarrierStep b carrier t₁ t₂, S.Anisotropic) ↔
      ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E → t₂.HasCarrier (carrier t₂) E :=
  ⟨fun ⟨S, hS⟩ _ hE h => S.keep hS hE h, fun h => ⟨ofTransport h, anisotropic_ofTransport h⟩⟩

/-- Transport a step along equalities of slicings. -/
def congr {t₁' t₂' : Slicing C} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂')
    (S : CarrierStep b carrier t₁ t₂) : CarrierStep b carrier t₁' t₂' where
  ι := S.ι
  gram := S.gram
  lost_isotropic := by subst h₁ h₂; exact S.lost_isotropic

@[simp]
theorem congr_gram {t₁' t₂' : Slicing C} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂')
    (S : CarrierStep b carrier t₁ t₂) : (S.congr h₁ h₂).gram = S.gram :=
  rfl

theorem anisotropic_congr {t₁' t₂' : Slicing C} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂')
    {S : CarrierStep b carrier t₁ t₂} (hS : S.Anisotropic) : (S.congr h₁ h₂).Anisotropic :=
  hS

end CarrierStep

/-- **A path for transport**: slicings `chamber 0, …, chamber n` and a step between consecutive
ones. No wall slicings and no outgoing flags. -/
structure CarrierPath (b : MukaiBudget C) (carrier : Slicing C → ObjectProperty C) where
  /-- The number of steps. -/
  n : ℕ
  /-- The slicings along the path. -/
  chamber : ℕ → Slicing C
  /-- The step from `chamber k` to `chamber (k + 1)`. -/
  step : ∀ k < n, CarrierStep b carrier (chamber k) (chamber (k + 1))

namespace CarrierPath

variable {b : MukaiBudget C} {carrier : Slicing C → ObjectProperty C}

/-- The anisotropy of a path: every step is anisotropic. -/
def Anisotropic (L : CarrierPath b carrier) : Prop :=
  ∀ k (hk : k < L.n), (L.step k hk).Anisotropic

/-- **An anisotropic path keeps a carrier** from its start to its end. -/
theorem keep (L : CarrierPath b carrier) (han : L.Anisotropic) {E : C} (hE : b.e E = 2)
    (h : (L.chamber 0).HasCarrier (carrier (L.chamber 0)) E) :
    (L.chamber L.n).HasCarrier (carrier (L.chamber L.n)) E := by
  suffices key : ∀ k ≤ L.n, (L.chamber k).HasCarrier (carrier (L.chamber k)) E from
    key L.n le_rfl
  intro k
  induction k with
  | zero => exact fun _ => h
  | succ k ih => exact fun hk => (L.step k (by lia)).keep (han k (by lia)) hE (ih (by lia))

/-- Append one step at the end of a path. -/
def snoc (L : CarrierPath b carrier) {t : Slicing C} (S : CarrierStep b carrier (L.chamber L.n) t) :
    CarrierPath b carrier where
  n := L.n + 1
  chamber k := if k ≤ L.n then L.chamber k else t
  step k hk :=
    if h : k < L.n then
      (L.step k h).congr (by simp [h.le]) (by simp [show k + 1 ≤ L.n by lia])
    else
      S.congr (by simp [show k = L.n by lia]) (by simp [show ¬(k + 1 ≤ L.n) by lia])

@[simp]
theorem snoc_n (L : CarrierPath b carrier) {t : Slicing C}
    (S : CarrierStep b carrier (L.chamber L.n) t) : (L.snoc S).n = L.n + 1 :=
  rfl

theorem snoc_chamber_zero (L : CarrierPath b carrier) {t : Slicing C}
    (S : CarrierStep b carrier (L.chamber L.n) t) : (L.snoc S).chamber 0 = L.chamber 0 := by
  simp [snoc]

theorem snoc_chamber_last (L : CarrierPath b carrier) {t : Slicing C}
    (S : CarrierStep b carrier (L.chamber L.n) t) : (L.snoc S).chamber (L.snoc S).n = t := by
  simp [snoc]

private theorem anisotropic_dite {t₁ t₂ : Slicing C} {c : Prop} [Decidable c]
    {a : c → CarrierStep b carrier t₁ t₂} {a' : ¬c → CarrierStep b carrier t₁ t₂}
    (ha : ∀ h, (a h).Anisotropic) (ha' : ∀ h, (a' h).Anisotropic) : (dite c a a').Anisotropic := by
  by_cases h : c
  · rw [dite_eq_left h]; exact ha h
  · rw [dite_eq_right h]; exact ha' h

theorem snoc_anisotropic (L : CarrierPath b carrier) {t : Slicing C}
    (S : CarrierStep b carrier (L.chamber L.n) t) (hL : L.Anisotropic) (hS : S.Anisotropic) :
    (L.snoc S).Anisotropic := fun k _ =>
  anisotropic_dite (fun h => CarrierStep.anisotropic_congr _ _ (hL k h))
    (fun _ => CarrierStep.anisotropic_congr _ _ hS)

end CarrierPath

/-! ### One letter -/

/-- **A letter carries a carrier to a carrier.** If an exact autoequivalence `Φ` sends carriers at
`s` to carriers at `Φ s`, it sends a carrier of `E` at `s` to one of `Φ E` at `Φ s`. Only this
direction of the letter field of the tower theorem is used. -/
theorem TriEquiv.hasCarrier_map (Φ : TriEquiv C) {s : Slicing C}
    {Pt : Slicing C → ObjectProperty C} (hPt : ∀ X, Pt s X → Pt (Φ.act s) (Φ.e.functor.obj X))
    {E : C} (h : s.HasCarrier (Pt s) E) :
    (Φ.act s).HasCarrier (Pt (Φ.act s)) (Φ.e.functor.obj E) := by
  obtain ⟨F, h0, i, hi⟩ := h
  refine ⟨Φ.mapHN F, fun j => ?_, i, ?_⟩
  · rw [TriEquiv.mapHN_factor, TriEquiv.isZero_functor_obj_iff]
    exact h0 j
  · exact hPt _ hi

/-! ### The split tower theorem -/

/-- **The inputs of the split tower theorem.** The objects and letters are those of
`TowerHypotheses`; the wall inputs are replaced by a Mukai budget, the slice fields, and paths of
transport steps whose anisotropy is a field. Transport of a carrier is assumed step by step
through these fields; see the module docstring. -/
structure SplitTowerHypotheses (C : Type u) [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The Mukai budget `e = dim Ext¹`: Mukai's lemma and invariance under isomorphism. -/
  budget : MukaiBudget C
  /-- `carrier s M`: the stable constituents of `M` in its phase slice for `s` are one isotropic
  object, with multiplicity one, and spherical objects. -/
  carrier : Slicing C → ObjectProperty C
  /-- `spherical s M`: every stable constituent of `M` in its phase slice for `s` is spherical. -/
  spherical : Slicing C → ObjectProperty C
  /-- The slice fields. -/
  slice : SliceFields budget carrier spherical
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
  /-- `e(𝒪_x) = dim Ext¹(𝒪_x, 𝒪_x) = 2`. -/
  e_point : budget.e point = 2
  /-- An exact autoequivalence preserves `Ext¹(E, E)`. -/
  e_letter : ∀ j E, budget.e ((letter j).e.functor.obj E) = budget.e E
  /-- `𝒪_x ≠ 0`. -/
  point_nonzero : ¬IsZero point
  /-- `𝒪_x` is stable at the geometric anchor (Bayer–Bridgeland, arXiv:1310.8266, Theorem 2.2
  and Lemma 6.7). -/
  point_semistable : ∃ φ, anchor.P φ point
  /-- A stable `𝒪_x` is its own single constituent, isotropic. -/
  carrier_point : carrier anchor point
  /-- A letter sends a carrier at `s` to a carrier at `V s` (Bridgeland, arXiv:math/0212237, §8:
  an autoequivalence matches the constituents of `P_s(φ)` with those of `P_{V s}(φ)` and preserves
  the Mukai pairing). Only this direction is used. -/
  carrier_letter : ∀ j s X, carrier s X → carrier ((letter j).act s) ((letter j).e.functor.obj X)
  /-- For each letter, a path of transport steps from `η` to `V⁻¹ η`. -/
  leg : ℕ → CarrierPath budget carrier
  leg_start : ∀ j, (leg j).chamber 0 = anchor
  leg_end : ∀ j, (leg j).chamber (leg j).n = (letter j).symm.act anchor
  /-- The final path, from `η` to the target `σ` itself (which may lie on walls). The old
  `final_target` is its last step. -/
  final : CarrierPath budget carrier
  final_start : final.chamber 0 = anchor
  final_end : final.chamber final.n = target
  /-- **The anisotropy field along each leg.** -/
  anisotropic_leg : ∀ j, (leg j).Anisotropic
  /-- **The anisotropy field along the final path.** -/
  anisotropic_final : final.Anisotropic

namespace SplitTowerHypotheses

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (T : SplitTowerHypotheses C)

/-- The prefixes `E_j = W_j P`: `E₀ = P` and `E_{j+1} = V_{j+1} E_j`. -/
def word : ℕ → C
  | 0 => T.point
  | j + 1 => (T.letter j).e.functor.obj (word j)

/-- Every prefix has `e = 2`. -/
theorem e_word : ∀ j, T.budget.e (T.word j) = 2
  | 0 => T.e_point
  | j + 1 => (T.e_letter j _).trans (e_word j)

/-- **Existence at the anchor for every prefix**: carry the carrier of `E_j` along the leg to
`V⁻¹ η`, then apply `V`. -/
theorem hasCarrier_anchor : ∀ j, T.anchor.HasCarrier (T.carrier T.anchor) (T.word j)
  | 0 => by
      obtain ⟨φ, hφ⟩ := T.point_semistable
      exact (T.anchor.carriesOnce_of_semistable (Rg := T.spherical T.anchor) hφ T.point_nonzero
        T.carrier_point).hasCarrier
  | j + 1 => by
      have h₀ := hasCarrier_anchor j
      rw [← T.leg_start j] at h₀
      have h₁ := (T.leg j).keep (T.anisotropic_leg j) (T.e_word j) h₀
      rw [T.leg_end j] at h₁
      have h₂ := TriEquiv.hasCarrier_map (T.letter j) (Pt := T.carrier) (T.carrier_letter j _) h₁
      rwa [TriEquiv.act_symm_act] at h₂

/-- **The split tower theorem.** At the target `σ`, exactly one HN factor of `W P` carries the
point, once, and every other factor is spherical. The same conclusion as `TowerHypotheses.tower`,
with no `IsTriangulated`, wall slicings, outgoing flags, sphericity of letters or uniqueness of HN
filtrations; transport is assumed step by step through the anisotropy fields. -/
theorem tower :
    T.target.CarriesOnce (T.carrier T.target) (T.spherical T.target) (T.word T.length) := by
  have h₀ := T.hasCarrier_anchor T.length
  rw [← T.final_start] at h₀
  have h₁ := T.final.keep T.anisotropic_final (T.e_word _) h₀
  rw [T.final_end] at h₁
  exact (T.slice.carriesOnce_iff_hasCarrier T.target (T.e_word _)).mpr h₁

/-- **The split tower theorem for every HN filtration.** Every HN filtration of `W P` at `σ` with
nonzero factors has exactly one carrier factor and its other factors are spherical. This uses
uniqueness of HN filtrations, hence that the predicates are closed under isomorphism. -/
theorem tower_forall [∀ s, (T.carrier s).IsClosedUnderIsomorphisms]
    [∀ s, (T.spherical s).IsClosedUnderIsomorphisms]
    (F : HNFiltration C T.target.P (T.word T.length)) (hF : ∀ i, ¬IsZero (F.factor i)) :
    F.CarriesOnce (T.carrier T.target) (T.spherical T.target) :=
  T.tower.forall F hF

end SplitTowerHypotheses

/-! ### What remains of the wall clauses -/

/-- **The sphericity part of the outgoing clause.** At a slicing `w` where `E` with `e(E) = 2`
carries the point once, every HN factor at any `t₂` of a non-carrier factor of `E` at `w` is rigid,
hence spherical (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.6) and not a carrier. No rigid-wall
uniqueness is used. This is not the third clause of `WallCrossing.outgoing`: it does not say that
those factors are nonzero, nor that outgoing flags exist in ordered phase windows. -/
theorem outgoing_noncarrier {b : MukaiBudget C} {carrier spherical : Slicing C → ObjectProperty C}
    (hS : SliceFields b carrier spherical) {w t₂ : Slicing C} {E : C} (hE : b.e E = 2)
    (W : HNFiltration C w.P E) (hW : W.CarriesOnce (carrier w) (spherical w))
    (k : Fin W.n) (hk : ¬carrier w (W.factor k)) (G : HNFiltration C t₂.P (W.factor k)) :
    (∀ i, ¬carrier t₂ (G.factor i)) ∧ ∀ i, spherical t₂ (G.factor i) := by
  obtain ⟨-, -, k₀, hk₀⟩ := (W.carriesOnce_iff _ _).mp hW
  have hne : ∀ i, b.e (W.factor i) ≠ 1 := fun i => hS.ne_one w _ _ (W.semistable i)
  have hnr : b.e (W.factor k₀) ≠ 0 := fun h0 =>
    hS.carrier_not_spherical w _ hk₀ (hS.rigid_spherical w _ _ (W.semistable k₀) h0)
  have hrig : b.e (W.factor k) = 0 := by
    rcases b.e_factor_eq_zero_or_two w.hom_vanishing hE W hne k with h | h
    · exact h
    · have := b.eq_of_e_factor_ne_zero w.hom_vanishing hE W hne (i := k) (by lia) hnr
      exact absurd (this ▸ hk₀) hk
  have hG : ∀ i, b.e (G.factor i) = 0 := b.rigid_factors t₂.hom_vanishing hrig G
  refine ⟨fun i hc => ?_, fun i => hS.rigid_spherical t₂ _ _ (G.semistable i) (hG i)⟩
  exact hS.carrier_not_spherical t₂ _ hc (hS.rigid_spherical t₂ _ _ (G.semistable i) (hG i))

/-- **The at-most-once half of the wall clause.** At any slicing `w`, every HN filtration of `E`
with `e(E) = 2` has at most one carrier factor and its other factors spherical, with no incoming
hypothesis; existence is the part of `WallCrossing.wall_of_incoming` that is not derived. -/
theorem wall_atMostOnce {b : MukaiBudget C} {carrier spherical : Slicing C → ObjectProperty C}
    (hS : SliceFields b carrier spherical) (w : Slicing C) {E : C} (hE : b.e E = 2)
    (W : HNFiltration C w.P E) : W.AtMostOnce (carrier w) (spherical w) :=
  hS.atMostOnce w hE W

/-! ### The old inputs give the new ones -/

section OfTowerHypotheses

variable [IsTriangulated C] {b : MukaiBudget C} {carrier spherical : Slicing C → ObjectProperty C}
  [∀ s, (carrier s).IsClosedUnderIsomorphisms] [∀ s, (spherical s).IsClosedUnderIsomorphisms]

/-- **A wall crossing gives a transport step** with empty Gram matrices, for objects with
`e(E) = 2` that are point-like. -/
def CarrierStep.ofWallCrossing (hS : SliceFields b carrier spherical) {𝒪 : ObjectProperty C}
    (h𝒪 : ∀ E, b.e E = 2 → 𝒪 E) {t₁ w t₂ : Slicing C}
    (hw : WallCrossing t₁ w t₂ carrier spherical 𝒪) : CarrierStep b carrier t₁ t₂ :=
  CarrierStep.ofTransport fun E hE h =>
    (hw.carriesOnce (h𝒪 E hE) ((hS.carriesOnce_iff_hasCarrier t₁ hE).mpr h)).hasCarrier

theorem CarrierStep.anisotropic_ofWallCrossing (hS : SliceFields b carrier spherical)
    {𝒪 : ObjectProperty C} (h𝒪 : ∀ E, b.e E = 2 → 𝒪 E) {t₁ w t₂ : Slicing C}
    (hw : WallCrossing t₁ w t₂ carrier spherical 𝒪) :
    (CarrierStep.ofWallCrossing hS h𝒪 hw).Anisotropic :=
  CarrierStep.anisotropic_ofTransport _

/-- **A leg gives a transport path** with the same chambers, every step with empty Gram
matrices. -/
def CarrierPath.ofLeg (hS : SliceFields b carrier spherical) {𝒪 : ObjectProperty C}
    (h𝒪 : ∀ E, b.e E = 2 → 𝒪 E) (L : Leg carrier spherical 𝒪) : CarrierPath b carrier where
  n := L.n
  chamber := L.chamber
  step k hk := CarrierStep.ofWallCrossing hS h𝒪 (L.crossing k hk)

theorem CarrierPath.anisotropic_ofLeg (hS : SliceFields b carrier spherical)
    {𝒪 : ObjectProperty C} (h𝒪 : ∀ E, b.e E = 2 → 𝒪 E) (L : Leg carrier spherical 𝒪) :
    (CarrierPath.ofLeg hS h𝒪 L).Anisotropic := fun k hk =>
  CarrierStep.anisotropic_ofWallCrossing hS h𝒪 (L.crossing k hk)

end OfTowerHypotheses

namespace SplitTowerHypotheses

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- **The old inputs, with the budget fields, give the split inputs.** Beyond `TowerHypotheses`
this needs a Mukai budget, the slice fields, that objects with `e = 2` are point-like, `e(𝒪_x) = 2`
and invariance of `e` under the letters. Every wall crossing becomes a step with empty Gram
matrices, and `final_target` becomes the last step of the final path. -/
def ofTowerHypotheses (T : TowerHypotheses C) (b : MukaiBudget C)
    (hS : SliceFields b T.carrier T.spherical) (h𝒪 : ∀ E, b.e E = 2 → T.pointLike E)
    (e_point : b.e T.point = 2) (e_letter : ∀ j E, b.e ((T.letter j).e.functor.obj E) = b.e E) :
    SplitTowerHypotheses C where
  budget := b
  carrier := T.carrier
  spherical := T.spherical
  slice := hS
  point := T.point
  letter := T.letter
  length := T.length
  anchor := T.anchor
  target := T.target
  e_point := e_point
  e_letter := e_letter
  point_nonzero := T.point_nonzero
  point_semistable := T.point_semistable
  carrier_point := T.carrier_point
  carrier_letter j s X h := (T.carrier_letter j s X).mpr h
  leg j := CarrierPath.ofLeg hS h𝒪 (T.leg j)
  leg_start := T.leg_start
  leg_end := T.leg_end
  final := (CarrierPath.ofLeg hS h𝒪 T.final).snoc <| CarrierStep.ofTransport fun E hE h =>
    (T.final_target E (h𝒪 E hE) ((hS.carriesOnce_iff_hasCarrier _ hE).mpr h)).hasCarrier
  final_start := by rw [CarrierPath.snoc_chamber_zero]; exact T.final_start
  final_end := CarrierPath.snoc_chamber_last _ _
  anisotropic_leg j := CarrierPath.anisotropic_ofLeg hS h𝒪 (T.leg j)
  anisotropic_final := CarrierPath.snoc_anisotropic _ _
    (CarrierPath.anisotropic_ofLeg hS h𝒪 T.final) (CarrierStep.anisotropic_ofTransport _)

theorem word_ofTowerHypotheses (T : TowerHypotheses C) (b : MukaiBudget C)
    (hS : SliceFields b T.carrier T.spherical) (h𝒪 : ∀ E, b.e E = 2 → T.pointLike E)
    (e_point : b.e T.point = 2) (e_letter : ∀ j E, b.e ((T.letter j).e.functor.obj E) = b.e E) :
    ∀ j, (ofTowerHypotheses T b hS h𝒪 e_point e_letter).word j = T.word j
  | 0 => rfl
  | j + 1 => by
    change (T.letter j).e.functor.obj _ = (T.letter j).e.functor.obj _
    rw [word_ofTowerHypotheses T b hS h𝒪 e_point e_letter j]

/-- **The two theorems agree on the old data**: the split tower theorem of
`ofTowerHypotheses T …` is the conclusion of `TowerHypotheses.tower T`. -/
theorem tower_ofTowerHypotheses (T : TowerHypotheses C) (b : MukaiBudget C)
    (hS : SliceFields b T.carrier T.spherical) (h𝒪 : ∀ E, b.e E = 2 → T.pointLike E)
    (e_point : b.e T.point = 2) (e_letter : ∀ j E, b.e ((T.letter j).e.functor.obj E) = b.e E) :
    T.target.CarriesOnce (T.carrier T.target) (T.spherical T.target) (T.word T.length) := by
  have h := (ofTowerHypotheses T b hS h𝒪 e_point e_letter).tower
  rwa [word_ofTowerHypotheses] at h

end SplitTowerHypotheses

end CategoryTheory.Triangulated
