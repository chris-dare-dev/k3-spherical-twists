/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Foundation.PreStabilityCondition
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.SplitTower

/-!
# A lost carrier forces an isotropic sphere sum at one phase of the wall

A transport step of the split tower theorem (`CarrierStep`) carries, for each phase, a matrix that
stands for the Gram matrix of the stable spheres of that phase at the wall crossed; there it is
free data. This file defines it from a named wall and proves the step's field.

**The wall step.** A `WallStep` from `t₁` to `t₂` names a wall: a pre-stability condition `w`
with class map `v : K₀(C) → Λ` (a slicing and a central charge compatible with it), and a
bilinear form `q` on `Λ`, the Mukai pairing in Mukai's sign. For each phase `φ`:

* `WallStep.SphereType φ` is the type of isomorphism classes of objects that are stable of phase
  `φ` at `w` and rigid (`e = 0`); on a 2-Calabi–Yau category a stable rigid object is spherical,
  since it is simple in `P_w(φ)` (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.6);
* `WallStep.gram φ` is their Gram matrix, `gram φ i j = q(v(Sᵢ), v(Sⱼ))`.

These are **definitions**, not fields. The stable objects of a phase are not assumed to be finitely
many: isotropic sphere sums are finitely supported.

**The theorem** (`WallStep.lost_isotropic`). If `e(E) = 2`, `E` has a carrier at `t₁` and none at
`t₂`, then some phase `φ` of the wall has a nonzero `a : SphereType φ →₀ ℕ` with `aᵀ·gram φ·a = 0`.
More precisely (`WallStep.exists_isotropic_of_lost`), the isotropic constituent of the carrier at
`t₁` is semistable at the wall with only spherical stable constituents there, and its class, which
is isotropic, is their sum. So `WallStep.toCarrierStep` is a `CarrierStep` whose Gram matrices are
those of the stable spheres of the wall. The statement is per phase, not per wall, since anisotropy
is not closed under orthogonal sums (`Matrix.isotropic_block`); its coefficients are natural
numbers, since distinct stable objects `S`, `T` of one phase have `⟨v(S), v(T)⟩ = ext¹(S, T) ≥ 0`
and the two notions differ for two spheres exactly at pairing `-2`. No assumption is made on how
many spheres share a phase.

## The inputs

The categorical inputs are fields of `WallStep`, each with its source:

* **stability at the wall**: a predicate `Stable φ` of stable objects of phase `φ`, the simple
  objects of the abelian category `P_w(φ)` (Bridgeland, arXiv:math/0212237, Lemma 5.2);
* **Jordan–Hölder classes at the wall**: each semistable object of phase `φ` has stable
  constituents of phase `φ` whose classes add up to its class (`P_w(φ)` has finite length for a
  locally finite stability condition, Bridgeland, arXiv:math/0212237, Lemma 4.5, and its short
  exact sequences are distinguished triangles);
* **semicontinuity of constituents**: a carrier at `t₁` of an object with `e = 2` has an isotropic
  stable constituent `X`, nonzero, of square-zero class, which is semistable at the wall (the set
  where an object is semistable is closed: Bridgeland, arXiv:math/0212237, §8, after
  Proposition 8.1; Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.7 and Remark 2.8);
* **the two-extension lemma**: if `X` has a non-rigid stable constituent at the wall, the carrier
  survives on the outgoing side (the draft *Harder–Narasimhan towers of spherical twist words on a
  Picard-rank-one K3 surface*, its two-extension lemma, with openness of stability,
  Bayer–Bridgeland, arXiv:1310.8266, Proposition 2.10).

The proof then is lattice arithmetic: if every constituent of `X` at the wall is spherical, the
class of `X` is an isotropic nonzero sum of sphere classes with natural coefficients
(`BilinearForm.isotropicSphereSum_gram_of_list`), nonzero because a nonzero semistable object has
nonzero charge (`PreStabilityCondition.WithClassMap.classOf_ne_zero`).

## Real objects

These fields have no instance built from real objects: the library has no 2-Calabi–Yau
triangulated category of a K3 surface, hence no stability condition on one, its stable objects or
their Jordan–Hölder constituents. The Gram matrices of named walls are computed from the classes of
the library's lattices: in Picard rank one, the wall of `𝒪_X` and `𝒪_X(-H)[1]`
(`AlgebraicGeometry/Surface/K3/PicardRankOne/AnisotropicWall.lean`), and the pairing-two wall of
`𝒪_C` and `𝒪_C(-1)[1]` on an elliptic K3 surface with a section, where the carrier of a point is
lost (`K3TwistsTest/WallStepModel.lean`).

## Main definitions

* `WallStep`: a named wall between two slicings, with the constituent-level inputs.
* `WallStep.SphereType`, `WallStep.sphereClass`, `WallStep.gram`: the stable spheres of a phase,
  their classes and their Gram matrix.
* `WallStep.toCarrierStep`, `WallPath`, `WallPath.toCarrierPath`: the transport step and path.
* `WallTowerHypotheses`: the inputs of the split tower theorem over paths of named walls, with
  anisotropy a hypothesis of the theorem rather than a field.

## Main results

* `PreStabilityCondition.WithClassMap.classOf_ne_zero`, `classOf_ne_neg`: a nonzero semistable
  object has nonzero class, and two of one phase do not have opposite classes.
* `WallStep.exists_nonrigid_constituent`: at an anisotropic phase, the carrier's isotropic
  constituent has a non-rigid constituent.
* `WallStep.exists_isotropic_of_lost`, `WallStep.lost_isotropic`: **a lost carrier forces an
  isotropic sphere sum at one phase**.
* `WallStep.keep`, `WallPath.keep`: an anisotropic wall keeps a carrier.
* `WallTowerHypotheses.tower`: the split tower theorem over paths of anisotropic named walls.

## Tags

wall crossing, stability condition, spherical object, Gram matrix, isotropic, Jordan–Hölder
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u u'

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {Λ : Type u'} [AddCommGroup Λ]

/-! ### Classes of semistable objects -/

namespace PreStabilityCondition.WithClassMap

variable {v : K₀ C →+ Λ}

/-- **A nonzero semistable object has nonzero class**: its charge lies on an open ray. -/
theorem classOf_ne_zero (σ : WithClassMap C v) {φ : ℝ} {E : C} (hP : σ.slicing.P φ E)
    (hE : ¬IsZero E) : classOf C v E ≠ 0 := by
  intro h
  obtain ⟨m, hm, heq⟩ := σ.compat φ E hP hE
  rw [charge_def, h, map_zero] at heq
  exact mul_ne_zero (by exact_mod_cast hm.ne') (Complex.exp_ne_zero _) heq.symm

/-- **Two nonzero semistable objects of one phase do not have opposite classes**: their charges
lie on the same open ray. -/
theorem classOf_ne_neg (σ : WithClassMap C v) {φ : ℝ} {S T : C} (hS : σ.slicing.P φ S)
    (hS0 : ¬IsZero S) (hT : σ.slicing.P φ T) (hT0 : ¬IsZero T) :
    classOf C v T ≠ -classOf C v S := by
  intro h
  obtain ⟨m, hm, hmS⟩ := σ.compat φ S hS hS0
  obtain ⟨m', hm', hmT⟩ := σ.compat φ T hT hT0
  rw [charge_def, h, map_neg, ← charge_def, hmS] at hmT
  have key : ((m : ℂ) + m') * Complex.exp ((Real.pi * φ : ℝ) * Complex.I) = 0 := by
    linear_combination -hmT
  rcases mul_eq_zero.mp key with h0 | h0
  · have : m + m' = 0 := by exact_mod_cast h0
    linarith
  · exact Complex.exp_ne_zero _ h0

end PreStabilityCondition.WithClassMap

/-! ### The wall step -/

/-- **A named wall between two slicings, with its constituent-level inputs.** `wall` is a
pre-stability condition with class map `v`; `Stable φ` its stable objects of phase `φ`;
`constituents φ X` the Jordan–Hölder constituents of a semistable `X` of phase `φ`;
`CarrierConstituent E ψ X` says that `X` is the isotropic stable constituent, at `t₁`, of the HN
factor of `E` that carries the point, and lies in `P_w(ψ)`. See the module docstring for the
sources. -/
structure WallStep (b : MukaiBudget C) (q : LinearMap.BilinForm ℤ Λ) (v : K₀ C →+ Λ)
    (carrier : Slicing C → ObjectProperty C) (t₁ t₂ : Slicing C) where
  /-- The wall: a slicing with a central charge `Z : Λ → ℂ` compatible with it (Bridgeland,
  arXiv:math/0212237, Definition 5.1). -/
  wall : PreStabilityCondition.WithClassMap C v
  /-- `Stable φ S`: `S` is stable of phase `φ` at the wall, a simple object of the abelian category
  `P_w(φ)` (Bridgeland, arXiv:math/0212237, Lemma 5.2). -/
  Stable : ℝ → ObjectProperty C
  /-- A stable object of phase `φ` is semistable of phase `φ`. -/
  semistable_of_stable : ∀ φ S, Stable φ S → wall.slicing.P φ S
  /-- A stable object is nonzero. -/
  nonzero_of_stable : ∀ φ S, Stable φ S → ¬IsZero S
  /-- The Jordan–Hölder constituents of a semistable object of phase `φ`, with multiplicity. -/
  constituents : ℝ → C → List C
  /-- **Jordan–Hölder at the wall**: the constituents are stable of the same phase (`P_w(φ)` has
  finite length: Bridgeland, arXiv:math/0212237, Lemma 4.5). -/
  stable_of_mem_constituents : ∀ φ X, wall.slicing.P φ X → ∀ T ∈ constituents φ X, Stable φ T
  /-- **Jordan–Hölder classes**: the classes of the constituents add up to the class of the
  object (a short exact sequence in `P_w(φ)` is a distinguished triangle). -/
  sum_classOf_constituents : ∀ φ X, wall.slicing.P φ X →
    ((constituents φ X).map (classOf C v)).sum = classOf C v X
  /-- `CarrierConstituent E ψ X`: `X` is the isotropic stable constituent, at `t₁`, of the HN
  factor of `E` carrying the point, and is semistable of phase `ψ` at the wall. -/
  CarrierConstituent : C → ℝ → C → Prop
  /-- **Semicontinuity of constituents**: a carrier at `t₁` of an object with `e = 2` has an
  isotropic stable constituent, and it is semistable at the wall (Bridgeland, arXiv:math/0212237,
  §8, after Proposition 8.1; Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.7 and Remark 2.8). -/
  exists_carrierConstituent : ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E →
    ∃ ψ X, CarrierConstituent E ψ X
  semistable_of_carrierConstituent : ∀ E ψ X, CarrierConstituent E ψ X → wall.slicing.P ψ X
  nonzero_of_carrierConstituent : ∀ E ψ X, CarrierConstituent E ψ X → ¬IsZero X
  /-- The carrier's constituent is isotropic: for a stable object `e = 2 + v²` (Riemann–Roch,
  Mukai; Huybrechts, *Fourier–Mukai transforms in algebraic geometry*, Ch. 10), and `e = 2`. -/
  isotropic_of_carrierConstituent : ∀ E ψ X, CarrierConstituent E ψ X →
    q (classOf C v X) (classOf C v X) = 0
  /-- **The two-extension lemma**: if the carrier's constituent has a non-rigid stable
  constituent at the wall, the carrier survives at `t₂` (the draft's two-extension lemma, with
  openness of stability, Bayer–Bridgeland, arXiv:1310.8266, Proposition 2.10). -/
  hasCarrier_of_nonrigid_constituent : ∀ E ψ X, b.e E = 2 → CarrierConstituent E ψ X →
    (∃ T ∈ constituents ψ X, b.e T ≠ 0) → t₂.HasCarrier (carrier t₂) E

namespace WallStep

variable {b : MukaiBudget C} {q : LinearMap.BilinForm ℤ Λ} {v : K₀ C →+ Λ}
  {carrier : Slicing C → ObjectProperty C} {t₁ t₂ : Slicing C}
  (W : WallStep b q v carrier t₁ t₂)

/-- `S` is a stable sphere of phase `φ` at the wall: stable of phase `φ` and rigid. -/
def IsSphere (φ : ℝ) (S : C) : Prop :=
  W.Stable φ S ∧ b.e S = 0

/-- Isomorphism of stable spheres of phase `φ`. -/
def sphereSetoid (φ : ℝ) : Setoid {S : C // W.IsSphere φ S} where
  r S T := Nonempty (S.1 ≅ T.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- **The sphere types of phase `φ`**: the isomorphism classes of stable spheres of phase `φ` at the
wall. -/
def SphereType (φ : ℝ) : Type u :=
  Quotient (W.sphereSetoid φ)

/-- The sphere type of a stable sphere. -/
def SphereType.mk {φ : ℝ} (S : C) (hS : W.IsSphere φ S) : W.SphereType φ :=
  Quotient.mk (W.sphereSetoid φ) ⟨S, hS⟩

/-- The class `v(S)` of a sphere type. -/
def sphereClass (φ : ℝ) : W.SphereType φ → Λ :=
  Quotient.lift (fun S => classOf C v S.1) fun _ _ ⟨e⟩ => classOf_iso C v e

@[simp]
theorem sphereClass_mk {φ : ℝ} (S : C) (hS : W.IsSphere φ S) :
    W.sphereClass φ (SphereType.mk W S hS) = classOf C v S :=
  rfl

/-- Every sphere type is the type of a stable sphere. -/
theorem SphereType.exists_eq_mk {φ : ℝ} (i : W.SphereType φ) :
    ∃ S hS, i = SphereType.mk W S hS :=
  Quotient.inductionOn i fun S => ⟨S.1, S.2, rfl⟩

/-- Two stable spheres have the same type exactly when they are isomorphic. -/
theorem SphereType.mk_eq_mk_iff {φ : ℝ} {S T : C} (hS : W.IsSphere φ S) (hT : W.IsSphere φ T) :
    SphereType.mk W S hS = SphereType.mk W T hT ↔ Nonempty (S ≅ T) :=
  Quotient.eq (r := W.sphereSetoid φ)

/-- **The Gram matrix of phase `φ`**: `gram φ i j = q(v(Sᵢ), v(Sⱼ))` over the stable spheres of
phase `φ` at the wall. A definition, from the wall and the class map. -/
def gram (φ : ℝ) : Matrix (W.SphereType φ) (W.SphereType φ) ℤ :=
  BilinearForm.gram q (W.sphereClass φ)

theorem gram_apply (φ : ℝ) (i j : W.SphereType φ) :
    W.gram φ i j = q (W.sphereClass φ i) (W.sphereClass φ j) :=
  rfl

/-- **At an anisotropic phase the carrier's constituent has a non-rigid constituent.** If the
stable spheres of phase `ψ` have no isotropic sum, then the isotropic constituent `X` of a carrier,
semistable of phase `ψ` at the wall, has a stable constituent there with `e ≠ 0`: otherwise its
isotropic nonzero class is a sum of sphere classes with natural coefficients. -/
theorem exists_nonrigid_constituent {E X : C} {ψ : ℝ} (hX : W.CarrierConstituent E ψ X)
    (hψ : ¬(W.gram ψ).IsotropicSphereSum) : ∃ T ∈ W.constituents ψ X, b.e T ≠ 0 := by
  by_contra hrig
  push Not at hrig
  apply hψ
  have hP := W.semistable_of_carrierConstituent E ψ X hX
  have hsph : ∀ T ∈ W.constituents ψ X, W.IsSphere ψ T := fun T hT =>
    ⟨W.stable_of_mem_constituents ψ X hP T hT, hrig T hT⟩
  let L : List (W.SphereType ψ) :=
    (W.constituents ψ X).pmap (fun T hT => SphereType.mk W T hT) hsph
  have hmap : L.map (W.sphereClass ψ) = (W.constituents ψ X).map (classOf C v) := by
    simp only [L, List.map_pmap, sphereClass_mk, List.pmap_eq_map]
  have hsum : (L.map (W.sphereClass ψ)).sum = classOf C v X := by
    rw [hmap, W.sum_classOf_constituents ψ X hP]
  have hne : classOf C v X ≠ 0 :=
    W.wall.classOf_ne_zero hP (W.nonzero_of_carrierConstituent E ψ X hX)
  refine BilinearForm.isotropicSphereSum_gram_of_list q (W.sphereClass ψ) L ?_ ?_
  · rintro hL
    apply hne
    rw [← hsum, hL, List.map_nil, List.sum_nil]
  · rw [hsum]
    exact W.isotropic_of_carrierConstituent E ψ X hX

/-- **A lost carrier, located.** If `e(E) = 2`, `E` has a carrier at `t₁` and none at `t₂`, then
the isotropic constituent `X` of its carrier at `t₁` is semistable of some phase `ψ` at the wall,
every stable constituent of `X` there is a sphere, and the stable spheres of phase `ψ` have an
isotropic sum (the class of `X`). -/
theorem exists_isotropic_of_lost {E : C} (hE : b.e E = 2) (h₁ : t₁.HasCarrier (carrier t₁) E)
    (h₂ : ¬t₂.HasCarrier (carrier t₂) E) :
    ∃ ψ X, W.CarrierConstituent E ψ X ∧ (∀ T ∈ W.constituents ψ X, W.IsSphere ψ T) ∧
      (W.gram ψ).IsotropicSphereSum := by
  obtain ⟨ψ, X, hX⟩ := W.exists_carrierConstituent E hE h₁
  have hP := W.semistable_of_carrierConstituent E ψ X hX
  refine ⟨ψ, X, hX, fun T hT => ⟨W.stable_of_mem_constituents ψ X hP T hT, ?_⟩, ?_⟩
  · by_contra hT0
    exact h₂ (W.hasCarrier_of_nonrigid_constituent E ψ X hE hX ⟨T, hT, hT0⟩)
  · by_contra hψ
    exact h₂ (W.hasCarrier_of_nonrigid_constituent E ψ X hE hX
      (W.exists_nonrigid_constituent hX hψ))

/-- **A lost carrier forces an isotropic sphere sum at one phase of the wall.** If `e(E) = 2`, `E`
has a carrier at `t₁` and none at `t₂`, then for some phase `φ` a nonzero `a : SphereType φ →₀ ℕ`
has `aᵀ·gram φ·a = 0`. This is the field of `CarrierStep`, for the Gram matrix of the stable spheres
of a named wall. -/
theorem lost_isotropic (E : C) (hE : b.e E = 2) (h₁ : t₁.HasCarrier (carrier t₁) E)
    (h₂ : ¬t₂.HasCarrier (carrier t₂) E) : ∃ φ, (W.gram φ).IsotropicSphereSum := by
  obtain ⟨ψ, -, -, -, h⟩ := W.exists_isotropic_of_lost hE h₁ h₂
  exact ⟨ψ, h⟩

/-- **The transport step of a wall**: its index types are the sphere types of the wall and its
matrices their Gram matrices; its field is `WallStep.lost_isotropic`. -/
def toCarrierStep : CarrierStep b carrier t₁ t₂ where
  ι := W.SphereType
  gram := W.gram
  lost_isotropic := W.lost_isotropic

@[simp]
theorem toCarrierStep_gram : W.toCarrierStep.gram = W.gram :=
  rfl

/-- The anisotropy of a wall: no phase has an isotropic sphere sum. -/
def Anisotropic : Prop :=
  ∀ φ, ¬(W.gram φ).IsotropicSphereSum

theorem anisotropic_toCarrierStep (h : W.Anisotropic) : W.toCarrierStep.Anisotropic :=
  h

/-- **Computing a Gram matrix from named spheres.** If the sphere types of phase `φ` are indexed
by `ι` through an equivalence under which their classes are `c`, the Gram matrix of phase `φ` has
an isotropic sphere sum exactly when the Gram matrix of `c` has one. -/
theorem isotropicSphereSum_gram_iff_of_equiv {φ : ℝ} {ι : Type*} (e : W.SphereType φ ≃ ι)
    (c : ι → Λ) (hc : ∀ i, W.sphereClass φ (e.symm i) = c i) :
    (W.gram φ).IsotropicSphereSum ↔ (BilinearForm.gram q c).IsotropicSphereSum := by
  rw [← Matrix.isotropicSphereSum_submatrix_equiv (W.gram φ) e.symm]
  have : (W.gram φ).submatrix e.symm e.symm = BilinearForm.gram q c := by
    ext i j
    simp [gram_apply, hc]
  rw [this]

/-- **An anisotropic wall keeps a carrier.** -/
theorem keep (han : W.Anisotropic) {E : C} (hE : b.e E = 2) (h : t₁.HasCarrier (carrier t₁) E) :
    t₂.HasCarrier (carrier t₂) E :=
  W.toCarrierStep.keep han hE h

end WallStep

/-! ### A path of walls -/

/-- **A path of named walls**: slicings `chamber 0, …, chamber n` and a wall step between
consecutive ones. -/
structure WallPath (b : MukaiBudget C) (q : LinearMap.BilinForm ℤ Λ) (v : K₀ C →+ Λ)
    (carrier : Slicing C → ObjectProperty C) where
  /-- The number of walls. -/
  n : ℕ
  /-- The slicings along the path. -/
  chamber : ℕ → Slicing C
  /-- The wall step from `chamber k` to `chamber (k + 1)`. -/
  step : ∀ k < n, WallStep b q v carrier (chamber k) (chamber (k + 1))

namespace WallPath

variable {b : MukaiBudget C} {q : LinearMap.BilinForm ℤ Λ} {v : K₀ C →+ Λ}
  {carrier : Slicing C → ObjectProperty C} (L : WallPath b q v carrier)

/-- The transport path of a path of walls: every step's Gram matrices are those of the stable
spheres of its wall. -/
def toCarrierPath : CarrierPath b carrier where
  n := L.n
  chamber := L.chamber
  step k hk := (L.step k hk).toCarrierStep

/-- The anisotropy of a path of walls. -/
def Anisotropic : Prop :=
  ∀ k (hk : k < L.n), (L.step k hk).Anisotropic

theorem anisotropic_toCarrierPath (h : L.Anisotropic) : L.toCarrierPath.Anisotropic :=
  h

/-- **An anisotropic path of walls keeps a carrier.** -/
theorem keep (han : L.Anisotropic) {E : C} (hE : b.e E = 2)
    (h : (L.chamber 0).HasCarrier (carrier (L.chamber 0)) E) :
    (L.chamber L.n).HasCarrier (carrier (L.chamber L.n)) E :=
  L.toCarrierPath.keep (L.anisotropic_toCarrierPath han) hE h

end WallPath

/-! ### The tower over paths of named walls -/

/-- **The inputs of the split tower theorem over paths of named walls.** The fields are those of
`SplitTowerHypotheses`, except that every path is a path of named walls (`WallPath`), whose Gram
matrices are those of the stable spheres of each wall, and that anisotropy is not a field: it is a
property of the walls, a hypothesis of `WallTowerHypotheses.tower`, proved in Picard rank one
(`AlgebraicGeometry.K3.PicardRankOne.WallTowerHypotheses.tower_of_rankOne`). -/
structure WallTowerHypotheses (C : Type u) [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {Λ : Type u'} [AddCommGroup Λ] (q : LinearMap.BilinForm ℤ Λ) (v : K₀ C →+ Λ) where
  /-- The Mukai budget `e = dim Ext¹`. -/
  budget : MukaiBudget C
  /-- `carrier s M`: one isotropic stable constituent, once, and spheres. -/
  carrier : Slicing C → ObjectProperty C
  /-- `spherical s M`: every stable constituent spherical. -/
  spherical : Slicing C → ObjectProperty C
  /-- The slice fields. -/
  slice : SliceFields budget carrier spherical
  /-- The skyscraper sheaf `P = 𝒪_x`. -/
  point : C
  /-- The letters, exact autoequivalences. -/
  letter : ℕ → WeakStabilityCondition.StabilityCondition.GroupAction.TriEquiv C
  /-- The length of the word. -/
  length : ℕ
  /-- The slicing of the generic anchor `η` in the geometric chamber. -/
  anchor : Slicing C
  /-- The slicing of the target stability condition `σ`. -/
  target : Slicing C
  /-- `e(𝒪_x) = 2`. -/
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
  /-- A letter sends a carrier at `s` to a carrier at `V s` (Bridgeland, arXiv:math/0212237,
  §8). -/
  carrier_letter : ∀ j s X, carrier s X → carrier ((letter j).act s) ((letter j).e.functor.obj X)
  /-- For each letter, a path of named walls from `η` to `V⁻¹ η`. -/
  leg : ℕ → WallPath budget q v carrier
  leg_start : ∀ j, (leg j).chamber 0 = anchor
  leg_end : ∀ j, (leg j).chamber (leg j).n = (letter j).symm.act anchor
  /-- The final path of named walls, from `η` to the target `σ`. -/
  final : WallPath budget q v carrier
  final_start : final.chamber 0 = anchor
  final_end : final.chamber final.n = target

namespace WallTowerHypotheses

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {Λ : Type u'} [AddCommGroup Λ] {q : LinearMap.BilinForm ℤ Λ} {v : K₀ C →+ Λ}
  (T : WallTowerHypotheses C q v)

/-- The prefixes `E_j = W_j P`. -/
def word : ℕ → C
  | 0 => T.point
  | j + 1 => (T.letter j).e.functor.obj (word j)

/-- **The split inputs of anisotropic walls**: the transport paths of the walls, whose Gram
matrices are those of the stable spheres of each wall. -/
def toSplitTowerHypotheses (han_leg : ∀ j, (T.leg j).Anisotropic)
    (han_final : T.final.Anisotropic) : SplitTowerHypotheses C where
  budget := T.budget
  carrier := T.carrier
  spherical := T.spherical
  slice := T.slice
  point := T.point
  letter := T.letter
  length := T.length
  anchor := T.anchor
  target := T.target
  e_point := T.e_point
  e_letter := T.e_letter
  point_nonzero := T.point_nonzero
  point_semistable := T.point_semistable
  carrier_point := T.carrier_point
  carrier_letter := T.carrier_letter
  leg j := (T.leg j).toCarrierPath
  leg_start := T.leg_start
  leg_end := T.leg_end
  final := T.final.toCarrierPath
  final_start := T.final_start
  final_end := T.final_end
  anisotropic_leg j := (T.leg j).anisotropic_toCarrierPath (han_leg j)
  anisotropic_final := T.final.anisotropic_toCarrierPath han_final

theorem word_toSplitTowerHypotheses (han_leg : ∀ j, (T.leg j).Anisotropic)
    (han_final : T.final.Anisotropic) :
    ∀ j, (T.toSplitTowerHypotheses han_leg han_final).word j = T.word j
  | 0 => rfl
  | j + 1 => by
    change (T.letter j).e.functor.obj _ = (T.letter j).e.functor.obj _
    rw [word_toSplitTowerHypotheses han_leg han_final j]

/-- **The tower theorem over anisotropic walls.** If every wall along the paths is anisotropic (no
phase has an isotropic sum of the classes of its stable spheres), then at the target exactly one HN
factor of `W P` carries the point, once, and every other factor is spherical. -/
theorem tower (han_leg : ∀ j, (T.leg j).Anisotropic) (han_final : T.final.Anisotropic) :
    T.target.CarriesOnce (T.carrier T.target) (T.spherical T.target) (T.word T.length) := by
  have h := (T.toSplitTowerHypotheses han_leg han_final).tower
  rwa [word_toSplitTowerHypotheses] at h

end WallTowerHypotheses

end CategoryTheory.Triangulated
