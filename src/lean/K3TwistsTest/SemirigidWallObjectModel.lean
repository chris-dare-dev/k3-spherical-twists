/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.OneCopyClassification
import K3Twists.RepresentationTheory.Quiver.Kronecker.TwoCopyExclusion

/-!
# Semirigid wall objects on explicit representations

* The length-three object `M_α ⊕ S` with `α = (1, 0)`, `β = (0, 1)` over `ℚ` is a semirigid wall
  object with `p = 3`: preprojective, nilpotent, and `dim End + p(2 - p) = 2`.
* A wall object of multiplicities `(2, 2)` with no arrow back, `A₁ = 1`, `A₂ = 0`: it is
  preprojective and nilpotent, and `dim End ≥ 2`, so it is not semirigid.
-/

open Module Quiver.Kronecker Quiver.Kronecker.DoubledRep

namespace K3TwistsTest.SemirigidWallObjectModel

/-- `α = (1, 0)`. -/
def α₀ : Fin 2 → ℚ := ![1, 0]

/-- `β = (0, 1)`, orthogonal to `α`. -/
def β₀ : Fin 2 → ℚ := ![0, 1]

lemma α₀_ne_zero : α₀ ≠ 0 := fun h => by simpa [α₀] using congrFun h 0

lemma β₀_ne_zero : β₀ ≠ 0 := fun h => by simpa [β₀] using congrFun h 1

lemma sum_α₀_β₀ : ∑ i, α₀ i * β₀ i = 0 := by simp [α₀, β₀, Fin.sum_univ_two]

/-- `M_α ⊕ S` satisfies the preprojective relations. -/
example : ((lengthThree α₀ β₀).addSimple (Fin 1 → ℚ)).IsPreprojective :=
  lengthThree_addSimple_isPreprojective sum_α₀_β₀ _

/-- `M_α ⊕ S` is nilpotent. -/
example : ((lengthThree α₀ β₀).addSimple (Fin 1 → ℚ)).IsNilpotent :=
  lengthThree_addSimple_isNilpotent _ _ _

/-- `M_α ⊕ S` is semirigid: `dim End + p(2 - p) = 2` with `p = 3`. -/
example : (finrank ℚ (Hom ((lengthThree α₀ β₀).addSimple (Fin 1 → ℚ))
        ((lengthThree α₀ β₀).addSimple (Fin 1 → ℚ))) : ℤ) +
      finrank ℚ ((ℚ × ℚ) × (Fin 1 → ℚ)) *
        (Fintype.card (Fin 2) - finrank ℚ ((ℚ × ℚ) × (Fin 1 → ℚ))) = 2 :=
  lengthThree_addSimple_semirigid α₀_ne_zero β₀_ne_zero (by simp) 1

/-- The wall object of multiplicities `(2, 2)` with `A₁ = 1`, `A₂ = 0` and no arrow back. -/
def twoTwo : DoubledRep ℚ (Fin 2) (Fin 2 → ℚ) (Fin 2 → ℚ) where
  A i := if i = 0 then LinearMap.id else 0
  B _ := 0

lemma twoTwo_isPreprojective : twoTwo.IsPreprojective := by
  refine ⟨?_, ?_⟩ <;> simp [twoTwo]

lemma twoTwo_isNilpotent : twoTwo.IsNilpotent := by
  have h2 : ∀ a b : Fin 2 ⊕ Fin 2, twoTwo.arrow a * twoTwo.arrow b = 0 := by
    intro a b
    refine LinearMap.ext fun x => ?_
    rcases a with i | i <;> rcases b with j | j <;> simp [twoTwo, mul_apply_eq_comp]
  refine ⟨2, fun w hw => ?_⟩
  obtain ⟨a, b, w', rfl⟩ : ∃ a b w', w = a :: b :: w' := by
    match w, hw with
    | a :: b :: w', _ => exact ⟨a, b, w', rfl⟩
  simp only [List.map_cons, List.prod_cons, ← mul_assoc, h2, zero_mul]

/-- **No semirigid `(2, 2)` object**: this one has `dim End ≥ 2`. -/
example : 2 ≤ finrank ℚ (Hom twoTwo twoTwo) :=
  twoTwo.two_le_finrank_Hom_of_twoTwo (by simp) (by simp) (by simp) twoTwo_isPreprojective
    twoTwo_isNilpotent

end K3TwistsTest.SemirigidWallObjectModel
