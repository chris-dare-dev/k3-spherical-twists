/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.SerreFunctor.TwoCalabiYau
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.SplitTower

/-!
# The split tower hypotheses can hold together, with `e(point) = 2`

A consistency model of `SplitTowerHypotheses`. The budget model `e = 0`
(`K3TwistsTest/BudgetModel.lean`) cannot serve, because the split hypotheses ask for
`e(𝒪_x) = 2`. This file builds an instance from

* a slicing `s` with a nonzero semistable object `P`, and
* a Mukai budget `b` with `b.e P = 2` and no semistable object of budget `1`,

with the empty word, paths with no steps, and the budget predicates `carrier := (e = 2)`,
`spherical := (e = 0)` (`SliceFields.ofBudget`). The split tower theorem then holds for `P`. On a
2-Calabi–Yau category (`TwoCYHypotheses`) the budget `e = dim Ext¹` has both properties when `P`
is simple with isotropic class: `e(P) = 2` is Riemann–Roch and `e` is even (`ofTwoCY`).

This is a relative check, like `K3TwistsTest/HNTowerModel.lean`: Mathlib has no triangulated
category with a slicing and a Mukai budget of value `2` (for instance the bounded derived category
of a K3 surface), so these are variables. The model exercises no transport step, and its slice
fields are those of the budget predicates, which every budget satisfies.

The file also keeps two vacuity statements as tests: a step with free Gram matrices exists
between any two slicings, and an anisotropic step exists exactly when carriers are transported. It
checks that the split theorem of `SplitTowerHypotheses.ofTowerHypotheses` is the conclusion of
`TowerHypotheses.tower`.

Built by `lake test`.
-/

noncomputable section

namespace CategoryTheory.Triangulated.SplitTowerModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

universe w u

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The path with no steps, staying at `s`. -/
def stayPath (b : MukaiBudget C) (carrier : Slicing C → ObjectProperty C) (s : Slicing C) :
    CarrierPath b carrier where
  n := 0
  chamber := fun _ => s
  step := fun _ hk => absurd hk (Nat.not_lt_zero _)

theorem stayPath_anisotropic (b : MukaiBudget C) (carrier : Slicing C → ObjectProperty C)
    (s : Slicing C) : (stayPath b carrier s).Anisotropic :=
  fun _ hk => absurd hk (Nat.not_lt_zero _)

/-- `Φ⁻¹ s = s` for the identity autoequivalence. -/
theorem id_symm_act (s : Slicing C) : (TriEquiv.id (C := C)).symm.act s = s :=
  Slicing.ext C (by funext φ X; rfl)

/-- **A model of the split tower hypotheses with `e(point) = 2`.** From a slicing `s`, a nonzero
`s`-semistable `P` and a budget with `e(P) = 2` and no semistable object of budget `1`: the empty
word, no steps, and the budget predicates. -/
def ofBudget (s : Slicing C) (P : C) (φ : ℝ) (hP : s.P φ P) (hP0 : ¬IsZero P)
    (b : MukaiBudget C) (heP : b.e P = 2)
    (hne : ∀ (s : Slicing C) (φ : ℝ) (M : C), s.P φ M → b.e M ≠ 1) :
    SplitTowerHypotheses C where
  budget := b
  carrier := fun _ X => b.e X = 2
  spherical := fun _ X => b.e X = 0
  slice := SliceFields.ofBudget b hne
  point := P
  letter := fun _ => TriEquiv.id
  length := 0
  anchor := s
  target := s
  e_point := heP
  e_letter := fun _ _ => rfl
  point_nonzero := hP0
  point_semistable := ⟨φ, hP⟩
  carrier_point := heP
  carrier_letter := fun _ _ _ h => h
  leg := fun _ => stayPath b _ s
  leg_start := fun _ => rfl
  leg_end := fun _ => (id_symm_act s).symm
  final := stayPath b _ s
  final_start := rfl
  final_end := rfl
  anisotropic_leg := fun _ => stayPath_anisotropic b _ s
  anisotropic_final := stayPath_anisotropic b _ s

/-- The split tower theorem holds in the model: `P` carries `e = 2` once at `s`. -/
example (s : Slicing C) (P : C) (φ : ℝ) (hP : s.P φ P) (hP0 : ¬IsZero P) (b : MukaiBudget C)
    (heP : b.e P = 2) (hne : ∀ (s : Slicing C) (φ : ℝ) (M : C), s.P φ M → b.e M ≠ 1) :
    s.CarriesOnce (fun X => b.e X = 2) (fun X => b.e X = 0) P :=
  (ofBudget s P φ hP hP0 b heP hne).tower

/-- **On a 2-Calabi–Yau category.** A nonzero semistable `P` with `End(P) = k`, no negative
self-extensions and isotropic class has `e(P) = 2` by Riemann–Roch, and `e` is even, so the model
applies to the budget `e = dim Ext¹`. -/
def ofTwoCY {k : Type*} [Field k] [Linear k C] {Λ : Type*} [AddCommGroup Λ]
    {q : LinearMap.BilinForm ℤ Λ} {v : K₀ C →+ Λ} (h : TwoCYHypotheses k C q v) (s : Slicing C)
    (P : C) (φ : ℝ) (hP : s.P φ P) (hP0 : ¬IsZero P) (hEnd : Module.finrank k (P ⟶ P) = 1)
    (hneg : ∀ n : ℤ, n < 0 → ∀ f : P ⟶ P⟦n⟧, f = 0)
    (hiso : q (classOf C v P) (classOf C v P) = 0) : SplitTowerHypotheses C :=
  ofBudget s P φ hP hP0 h.toMukaiBudget (h.selfExtDim_eq_two_of_isotropic hEnd hneg hiso)
    fun _ _ M _ h1 => by
      obtain ⟨r, hr⟩ := h.even_e M
      lia

theorem ofTwoCY_e_point {k : Type*} [Field k] [Linear k C] {Λ : Type*} [AddCommGroup Λ]
    {q : LinearMap.BilinForm ℤ Λ} {v : K₀ C →+ Λ} (h : TwoCYHypotheses k C q v) (s : Slicing C)
    (P : C) (φ : ℝ) (hP : s.P φ P) (hP0 : ¬IsZero P) (hEnd : Module.finrank k (P ⟶ P) = 1)
    (hneg : ∀ n : ℤ, n < 0 → ∀ f : P ⟶ P⟦n⟧, f = 0)
    (hiso : q (classOf C v P) (classOf C v P) = 0) :
    selfExtDim k (ofTwoCY h s P φ hP hP0 hEnd hneg hiso).point = 2 :=
  (ofTwoCY h s P φ hP hP0 hEnd hneg hiso).e_point

/-! ### Vacuity of free Gram matrices -/

/-- **A step with free Gram matrices exists between any two slicings**: take the isotropic matrix
of two spheres of pairing `2` at every phase. So a `CarrierStep` says nothing about the slicings
until its Gram matrices are tied to a wall. -/
def anyStep (b : MukaiBudget C) (carrier : Slicing C → ObjectProperty C) (t₁ t₂ : Slicing C) :
    CarrierStep b carrier t₁ t₂ where
  ι := fun _ => ULift (Fin 2)
  gram := fun _ => Matrix.of fun i j => if i = j then -2 else 2
  lost_isotropic := fun _ _ _ _ => ⟨0, (Matrix.isotropicSphereSum_iff_of_fintype _).mpr
    ⟨fun _ => 1, fun h => by simpa using congrFun h ⟨0⟩, by decide⟩⟩

/-- An anisotropic step is the transport hypothesis. -/
example (b : MukaiBudget C) (carrier : Slicing C → ObjectProperty C) (t₁ t₂ : Slicing C) :
    (∃ S : CarrierStep b carrier t₁ t₂, S.Anisotropic) ↔
      ∀ E, b.e E = 2 → t₁.HasCarrier (carrier t₁) E → t₂.HasCarrier (carrier t₂) E :=
  CarrierStep.exists_anisotropic_iff

/-- The split theorem of the old data is the old theorem. -/
example [IsTriangulated C] (T : TowerHypotheses C) (b : MukaiBudget C)
    (hS : SliceFields b T.carrier T.spherical) (h𝒪 : ∀ E, b.e E = 2 → T.pointLike E)
    (e_point : b.e T.point = 2) (e_letter : ∀ j E, b.e ((T.letter j).e.functor.obj E) = b.e E) :
    T.target.CarriesOnce (T.carrier T.target) (T.spherical T.target) (T.word T.length) :=
  SplitTowerHypotheses.tower_ofTowerHypotheses T b hS h𝒪 e_point e_letter

/-- `Matrix.isotropic_block`, as a regression test: anisotropy is per phase, not per wall. -/
example : (!![(-2 : ℤ), 0, 0; 0, -2, 3; 0, 3, -2]).IsotropicSphereSum :=
  Matrix.isotropic_block

end CategoryTheory.Triangulated.SplitTowerModel
