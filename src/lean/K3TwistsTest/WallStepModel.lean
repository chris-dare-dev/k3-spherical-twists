/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.Lattice
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.AnisotropicWall
import K3TwistsTest.PairingTwoWallTowerModel

/-!
# Walls: the pairing-two wall, regression tests, and consistency models

* **The pairing-two wall.** On an elliptic K3 surface with a section `C`, the wall that contracts
  `C` has the stable spheres `A = 𝒪_C` and `B = 𝒪_C(-1)[1]` with `⟨v(A), v(B)⟩ = ext¹ = 2`. Their
  Gram matrix is `[[-2, 2], [2, -2]]`, the matrix of `Matrix.isotropic_two`, and `(1, 1)` is an
  isotropic sphere sum: the class `v(A) + v(B) = v(𝒪_x)` of a point. So a wall whose phase has
  these two sphere types is not anisotropic there (`not_anisotropic_curveWall`), as it must not
  be: on the side where `𝒪_C` has the larger phase, a point `𝒪_x` with `x ∈ C` has the two rigid
  HN factors `𝒪_C` and `𝒪_C(-1)[1]` and no carrier (`K3TwistsTest/PairingTwoWallTowerModel.lean`).
  The anisotropy field of the split tower theorem fails exactly at this wall, and
  `WallStep.lost_isotropic` locates the loss there.
* **Regression tests** for the per-phase and natural-coefficient forms of anisotropy: the block
  matrix `[-2] ⊕ [[-2, 3], [3, -2]]` has the isotropic sum `(1, 1, 1)`; with natural coefficients
  `[[-2, -2], [-2, -2]]` is anisotropic although `(1, -1)` is an isotropic integer vector; three
  spheres of pairwise pairings `4, 5, 6` have the isotropic sum `(4, 35, 3)`.
* **Consistency models** of `WallStep` and `WallTowerHypotheses`, relative to a pre-stability
  condition with a nonzero semistable object of isotropic class and budget `2` (Mathlib has no
  such category yet). The wall step there crosses no wall: its slicings agree, every nonzero
  semistable object is declared its own stable constituent, and the carrier is the isomorphism
  class of that object. It shows the fields can hold together; it is not an instance from real
  objects, which needs the bounded derived category of a K3 surface.

Built by `lake test`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Matrix

/-! ### The pairing-two wall -/

namespace AlgebraicGeometry.K3.EllipticWithSection.WallStepTest

open Mukai

/-- The Gram matrix of `𝒪_C` and `𝒪_C(-1)[1]` is that of `Matrix.isotropic_two`. -/
theorem gram_curveWall :
    BilinearForm.gram (mukaiForm intersection) ![wallA, wallB] = !![-2, 2; 2, -2] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact isSpherical_wallA
  · exact pairing_wallA_wallB
  · exact (pairing_comm intersection intersection_comm _ _).trans pairing_wallA_wallB
  · exact isSpherical_wallB

/-- The curve wall has an isotropic sphere sum, `(1, 1)`. -/
theorem isotropicSphereSum_curveWall :
    (BilinearForm.gram (mukaiForm intersection) ![wallA, wallB]).IsotropicSphereSum := by
  rw [gram_curveWall]
  exact isotropic_two

/-- The isotropic sum `(1, 1)` is the class of a point. -/
example : wallA + wallB = point :=
  wallA_add_wallB

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {b : MukaiBudget C}
  {v : K₀ C →+ MukaiLattice ℤ NS} {carrier : Slicing C → ObjectProperty C} {t₁ t₂ : Slicing C}

/-- **A wall whose phase has the sphere types `𝒪_C`, `𝒪_C(-1)[1]` is not anisotropic there.** -/
theorem not_anisotropic_curveWall (W : WallStep b (mukaiForm intersection) v carrier t₁ t₂)
    {φ : ℝ} (e : W.SphereType φ ≃ Fin 2)
    (hc : ∀ i, W.sphereClass φ (e.symm i) = ![wallA, wallB] i) :
    ¬W.Anisotropic := fun h =>
  h φ ((W.isotropicSphereSum_gram_iff_of_equiv e _ hc).mpr isotropicSphereSum_curveWall)

/-- **The carrier is lost, and the loss is located at an isotropic phase.** Let the outgoing chamber
`t₂` be the side of the curve wall where `𝒪_C` has the larger phase, so that `𝒪_x` has the two
rigid HN factors `𝒪_C`, `𝒪_C(-1)[1]` there (`PairingTwoWallTowerModel.Config`), and let `𝒪_x` have
a carrier at `t₁`. Then some phase of the wall has an isotropic sphere sum. -/
example {Λ : Type*} [AddCommGroup Λ] {q : LinearMap.BilinForm ℤ Λ} {v' : K₀ C →+ Λ}
    (K : PairingTwoWallTowerModel.Config t₂ b)
    (W : WallStep b q v' (fun _ X => b.e X = 2) t₁ t₂)
    (h₁ : t₁.HasCarrier (fun X => b.e X = 2) K.P) :
    ∃ φ, (W.gram φ).IsotropicSphereSum :=
  W.lost_isotropic K.P K.eP h₁ K.not_hasCarrier

end AlgebraicGeometry.K3.EllipticWithSection.WallStepTest

/-! ### Regression tests -/

namespace CategoryTheory.Triangulated.WallStepModel

/-- Anisotropy is per phase: each block is anisotropic, the orthogonal sum is not. -/
example : (!![(-2 : ℤ), 0, 0; 0, -2, 3; 0, 3, -2]).IsotropicSphereSum ∧
    ¬(!![(-2 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ).IsotropicSphereSum ∧
    ¬(!![(-2 : ℤ), 3; 3, -2]).IsotropicSphereSum :=
  ⟨isotropic_block, noIsotropic_one _ rfl, noIsotropic_two (by norm_num)⟩

/-- Natural coefficients matter already for two spheres, at pairing `-2`. -/
example : ¬(!![(-2 : ℤ), -2; -2, -2]).IsotropicSphereSum ∧
    (![1, -1] : Fin 2 → ℤ) ⬝ᵥ (!![(-2 : ℤ), -2; -2, -2]) *ᵥ ![1, -1] = 0 :=
  ⟨fun h => by simpa using (isotropicSphereSum_two_iff (-2)).mp h, by decide⟩

/-- Three spheres with pairwise pairings `4, 5, 6`, all at least `3`, have the isotropic sum
`(4, 35, 3)`. -/
example : (!![(-2 : ℤ), 4, 5; 4, -2, 6; 5, 6, -2]).IsotropicSphereSum :=
  (isotropicSphereSum_iff_of_fintype _).mpr
    ⟨![4, 35, 3], fun h => by simpa using congrFun h 0, by decide⟩

/-! ### Consistency models -/

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {Λ : Type u'} [AddCommGroup Λ]
  {q : LinearMap.BilinForm ℤ Λ} {v : K₀ C →+ Λ}

/-- The objects isomorphic to `P`. -/
def isoClass (P : C) : ObjectProperty C := fun X => Nonempty (X ≅ P)

open Classical in
/-- **A wall step that crosses no wall.** Its two slicings are the slicing of `σ`; every nonzero
semistable object is its own stable constituent; the carrier is the isomorphism class of a nonzero
semistable `P` of isotropic class. -/
def stayWall (σ : PreStabilityCondition.WithClassMap C v) (b : MukaiBudget C) (P : C) (φ₀ : ℝ)
    (hP : σ.slicing.P φ₀ P) (hP0 : ¬IsZero P) (hiso : q (classOf C v P) (classOf C v P) = 0) :
    WallStep b q v (fun _ => isoClass P) σ.slicing σ.slicing where
  wall := σ
  Stable φ S := σ.slicing.P φ S ∧ ¬IsZero S
  semistable_of_stable _ _ h := h.1
  nonzero_of_stable _ _ h := h.2
  constituents _ X := if IsZero X then [] else [X]
  stable_of_mem_constituents φ X hX T hT := by
    split_ifs at hT with h0
    · simp at hT
    · rw [List.mem_singleton] at hT
      subst hT
      exact ⟨hX, h0⟩
  sum_classOf_constituents φ X _ := by
    split_ifs with h0
    · simp [classOf_isZero C v h0]
    · simp
  CarrierConstituent E ψ X := σ.slicing.HasCarrier (isoClass P) E ∧ ψ = φ₀ ∧ X = P
  exists_carrierConstituent E _ h := ⟨φ₀, P, h, rfl, rfl⟩
  semistable_of_carrierConstituent := by
    rintro E ψ X ⟨-, rfl, rfl⟩
    exact hP
  nonzero_of_carrierConstituent := by
    rintro E ψ X ⟨-, -, rfl⟩
    exact hP0
  isotropic_of_carrierConstituent := by
    rintro E ψ X ⟨-, -, rfl⟩
    exact hiso
  hasCarrier_of_nonrigid_constituent E _ _ _ h _ := h.1

/-- The path of named walls with no wall, staying at `s`. -/
def stayPath (b : MukaiBudget C) (carrier : Slicing C → ObjectProperty C) (s : Slicing C) :
    WallPath b q v carrier where
  n := 0
  chamber := fun _ => s
  step := fun _ hk => absurd hk (Nat.not_lt_zero _)

open WeakStabilityCondition.StabilityCondition.GroupAction in
/-- **A model of `WallTowerHypotheses` with `e(point) = 2`**: the empty word and paths with no
wall, from a slicing with a nonzero semistable `P` and a budget with `e(P) = 2` and no semistable
object of budget `1`. -/
def wallTowerModel (s : Slicing C) (P : C) (φ : ℝ) (hP : s.P φ P) (hP0 : ¬IsZero P)
    (b : MukaiBudget C) (heP : b.e P = 2)
    (hne : ∀ (s : Slicing C) (φ : ℝ) (M : C), s.P φ M → b.e M ≠ 1) :
    WallTowerHypotheses C q v where
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
  leg_end := fun _ => Slicing.ext C (by funext φ X; rfl)
  final := stayPath b _ s
  final_start := rfl
  final_end := rfl

/-- The rank-one tower theorem applies to the model with no wall: the rank-one inputs are vacuous
on a path with no wall. -/
example (s : Slicing C) (P : C) (φ : ℝ) (hP : s.P φ P) (hP0 : ¬IsZero P) (b : MukaiBudget C)
    (heP : b.e P = 2) (hne : ∀ (s : Slicing C) (φ : ℝ) (M : C), s.P φ M → b.e M ≠ 1)
    {v : K₀ C →+ MukaiVector ℤ} :
    s.CarriesOnce (fun X => b.e X = 2) (fun X => b.e X = 0) P :=
  AlgebraicGeometry.K3.PicardRankOne.WallTowerHypotheses.tower_of_rankOne
    (wallTowerModel (q := MukaiVector.mukaiForm 1) (v := v) s P φ hP hP0 b heP hne) one_pos
    (fun _ _ hk => absurd hk (Nat.not_lt_zero _)) (fun _ hk => absurd hk (Nat.not_lt_zero _))

end CategoryTheory.Triangulated.WallStepModel
