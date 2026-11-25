/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PairingTwoWall
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Tower

/-!
# A point with two rigid HN factors: existence is independent of the budget

Near the wall that contracts a `(-2)`-curve `C`, on the side where `φ(𝒪_C) > φ(𝒪_C(-1)[1])`, a
point `𝒪_x` with `x ∈ C` has the HN filtration `0 ⊂ 𝒪_C ⊂ 𝒪_x` with the two spherical factors
`𝒪_C` and `𝒪_C(-1)[1]` (`PairingTwoWallHypotheses.hn_P_of_phase_gt`, with `A = 𝒪_C`,
`B = 𝒪_C(-1)[1]`, `P = 𝒪_x`). So at that slicing `e(𝒪_x) = 2` while every HN factor is rigid: the
budget defect is `2`, and no factor carries the point. This happens already for the empty word,
before any spherical twist.

This file states the configuration in triangulated form, relative to a slicing and a Mukai budget
(Mathlib cannot construct `D^b(X)` with a stability condition yet): a distinguished triangle
`A → P → B → A⟦1⟧` with `A`, `B` nonzero semistable of phases `φ(B) < φ(A)`, `e(A) = e(B) = 0`
and `e(P) = 2`. Then

* `P` has the HN filtration with factors `A`, `B` (`twoStep`), of defect `2`;
* that filtration has `e = 2` and `e = 0` at most once (`atMostOnce_twoStep`): the half of the
  tower property that the budget gives;
* `P` does not carry `e = 2` once at this slicing (`not_carriesOnce`): the other half, existence
  of a carrier, fails.

So `CarriesOnce` is not a consequence of the budget; the tower theorem needs the transport of a
carrier along its path as a separate input.

Built by `lake test`.
-/

noncomputable section

namespace CategoryTheory.Triangulated.PairingTwoWallTowerModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The configuration of a point at the curve wall**: a distinguished triangle
`A → P → B → A⟦1⟧` with `A`, `B` nonzero semistable for `s`, of phases `φ_B < φ_A`, rigid for the
budget `b`, while `e(P) = 2`. -/
structure Config (s : Slicing C) (b : MukaiBudget C) where
  /-- `𝒪_C`. -/
  A : C
  /-- `𝒪_x`. -/
  P : C
  /-- `𝒪_C(-1)[1]`. -/
  B : C
  /-- The triangle `𝒪_C → 𝒪_x → 𝒪_C(-1)[1] → 𝒪_C[1]`. -/
  T : Triangle C
  hT : T ∈ distTriang C
  e₁ : T.obj₁ ≅ A
  e₂ : T.obj₂ ≅ P
  e₃ : T.obj₃ = B
  φA : ℝ
  φB : ℝ
  hφ : φB < φA
  hA : s.P φA A
  hB : s.P φB B
  hA0 : ¬IsZero A
  hB0 : ¬IsZero B
  eA : b.e A = 0
  eB : b.e B = 0
  eP : b.e P = 2

namespace Config

variable {s : Slicing C} {b : MukaiBudget C} (K : Config s b)

/-- The HN filtration `0 ⊂ A ⊂ P`, with factors `A` and `B`. -/
def twoStep : HNFiltration C s.P K.P :=
  (HNFiltration.single C K.A K.φA K.hA).appendFactor C K.T K.hT K.e₁ K.e₂ K.φB
    (K.e₃ ▸ K.hB) fun _ => K.hφ

theorem twoStep_n : K.twoStep.n = 2 := rfl

theorem twoStep_factor_zero : K.twoStep.factor ⟨0, by simp [twoStep_n]⟩ = K.A := rfl

theorem twoStep_factor_one : K.twoStep.factor ⟨1, by simp [twoStep_n]⟩ = K.B := K.e₃

theorem twoStep_factor (i : Fin K.twoStep.n) :
    K.twoStep.factor i = K.A ∨ K.twoStep.factor i = K.B := by
  rcases i with ⟨i, hi⟩
  have hi' : i < 2 := hi
  interval_cases i
  · exact Or.inl K.twoStep_factor_zero
  · exact Or.inr K.twoStep_factor_one

theorem twoStep_nonzero (i : Fin K.twoStep.n) : ¬IsZero (K.twoStep.factor i) := by
  rcases K.twoStep_factor i with h | h <;> rw [h]
  · exact K.hA0
  · exact K.hB0

theorem e_twoStep_factor (i : Fin K.twoStep.n) : b.e (K.twoStep.factor i) = 0 := by
  rcases K.twoStep_factor i with h | h <;> rw [h]
  · exact K.eA
  · exact K.eB

/-- **The defect is `2`**: both factors are rigid, `e(P) = 2`. -/
theorem sum_e_twoStep : ∑ i, b.e (K.twoStep.factor i) = 0 := by
  simp [K.e_twoStep_factor]

/-- **At most once holds**: no factor has `e = 2`, and every factor has `e = 0`. -/
theorem atMostOnce_twoStep :
    K.twoStep.AtMostOnce (fun X => b.e X = 2) (fun X => b.e X = 0) :=
  b.atMostOnce_e s.hom_vanishing K.eP _ fun i => by rw [K.e_twoStep_factor]; exact zero_ne_one

/-- **Existence fails**: no HN filtration of `P` with nonzero factors has a factor with `e = 2`.
Every such filtration has the budget sum of `twoStep` (HN uniqueness), which is `0 < e(P)`. -/
theorem not_hasCarrier : ¬ s.HasCarrier (fun X => b.e X = 2) K.P := by
  rintro ⟨G, hG, i, hi⟩
  have hsum := b.sum_e_eq_of_nonzero s G K.twoStep hG K.twoStep_nonzero
  rw [K.sum_e_twoStep] at hsum
  have := Finset.single_le_sum (f := fun j => b.e (G.factor j)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  change b.e (G.factor i) = 2 at hi
  lia

/-- **The tower property fails**: `P` does not carry `e = 2` once at `s`. -/
theorem not_carriesOnce : ¬ s.CarriesOnce (fun X => b.e X = 2) (fun X => b.e X = 0) K.P :=
  fun h => K.not_hasCarrier h.hasCarrier

end Config

end CategoryTheory.Triangulated.PairingTwoWallTowerModel
