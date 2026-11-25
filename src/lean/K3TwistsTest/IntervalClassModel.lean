/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.IntervalClass
import K3Twists.RepresentationTheory.Quiver.Kronecker.Radical

/-!
# Interval classes: models and counterexamples

* **The restriction formula does not give heredity.** On the chain `0 < 1 < 2 < 3` with
  `Q = refl ∪ {(1, 3), (2, 3)}` the radical is `0`, so `t(A) = A ⊓ t(R)` holds for every `A`;
  yet the class is not hereditary (`3 / 1` is in it, `2 / 1` is not), so the nested formula
  fails for some `a ≤ c` (`IntervalClass.hereditary_iff_nested`).
* **Defining the saturation needs `trans`.** On `Fin 2 × Fin 2`, the predicate
  `refl ∪ {((0,0), (1,0)), ((0,0), (0,1)), ((1,0), (1,1)), ((0,1), (1,1))}` satisfies `push` but
  not `trans`, and the candidates over `(0, 0)` have no greatest element.
* **The socle iteration** on the chain `0 < 1 < 2 < 3`, with the whole chain as the class and the
  steps of length at most one as the layer, reaches the radical `3` in three steps, the bound of
  `IntervalClass.Layer.socleSeq_bot_eq_rad_of_le` for the length `Fin.val`.

Built by `lake test`.
-/

namespace IntervalClassModel

/-! ### The restriction formula without heredity -/

/-- `Q a b` on the chain `0 < 1 < 2 < 3`: `a = b`, or `(a, b)` is `(1, 3)` or `(2, 3)`. -/
def chainQ (a b : Fin 4) : Prop :=
  a = b ∨ (a.val = 1 ∧ b.val = 3) ∨ (a.val = 2 ∧ b.val = 3)

instance : DecidableRel chainQ := fun a b => by unfold chainQ; infer_instance

lemma chainQ_trans : ∀ a b c : Fin 4, a ≤ b → b ≤ c → chainQ a b → chainQ b c → chainQ a c := by
  decide

lemma chainQ_push : ∀ a a' s : Fin 4, a ≤ a' → a ≤ s → chainQ a s → chainQ a' (a' ⊔ s) := by
  decide

/-- The interval class `refl ∪ {(1, 3), (2, 3)}` on the chain `0 < 1 < 2 < 3`. -/
def chainClass : IntervalClass (Fin 4) where
  Q := chainQ
  refl _ := Or.inl rfl
  trans {a b c} := chainQ_trans a b c
  push {a a' s} := chainQ_push a a' s

theorem chainClass_not_hereditary : ¬ chainClass.Hereditary := by
  intro h
  have := @h 1 2 3 (by decide) (by decide) (Or.inr (Or.inl ⟨rfl, rfl⟩))
  exact absurd (show chainQ 1 2 from this) (by decide)

theorem chainClass_rad : chainClass.rad = ⊥ := by
  have h : chainQ ⊥ chainClass.rad := chainClass.Q_rad
  have hb : (⊥ : Fin 4).val = 0 := rfl
  rcases h with h | ⟨h, _⟩ | ⟨h, _⟩
  · exact h.symm
  · rw [hb] at h; exact absurd h (by decide)
  · rw [hb] at h; exact absurd h (by decide)

/-- The restriction formula `t(A) = A ⊓ t(R)` holds for every `A`. -/
theorem chainClass_restriction (c : Fin 4) :
    IsGreatest (chainClass.cands ⊥ c) (c ⊓ chainClass.rad) := by
  rw [chainClass_rad, inf_bot_eq]
  refine ⟨⟨le_rfl, bot_le, chainClass.refl ⊥⟩, ?_⟩
  rintro b ⟨_, _, hQ⟩
  have hb : (⊥ : Fin 4).val = 0 := rfl
  rcases hQ with h | ⟨h, _⟩ | ⟨h, _⟩
  · exact h.symm.le
  · rw [hb] at h; exact absurd h (by decide)
  · rw [hb] at h; exact absurd h (by decide)

/-- The nested formula fails for some `a ≤ c`. -/
theorem chainClass_nested_fails :
    ¬ ∀ ⦃a c : Fin 4⦄, a ≤ c → IsGreatest (chainClass.cands a c) (c ⊓ chainClass.sat a) :=
  fun h => chainClass_not_hereditary (chainClass.hereditary_iff_nested.mpr h)

/-! ### Without `trans` there is no greatest candidate -/

/-- `refl ∪ {((0,0), (1,0)), ((0,0), (0,1)), ((1,0), (1,1)), ((0,1), (1,1))}` on
`Fin 2 × Fin 2`. -/
def squareQ (a b : Fin 2 × Fin 2) : Prop :=
  a = b ∨ (a = (0, 0) ∧ (b = (1, 0) ∨ b = (0, 1))) ∨ ((a = (1, 0) ∨ a = (0, 1)) ∧ b = (1, 1))

instance : DecidableRel squareQ := fun a b => by unfold squareQ; infer_instance

lemma squareQ_push :
    ∀ a a' s : Fin 2 × Fin 2, a ≤ a' → a ≤ s → squareQ a s → squareQ a' (a' ⊔ s) := by
  decide

lemma squareQ_not_trans :
    ¬ ∀ a b c : Fin 2 × Fin 2, a ≤ b → b ≤ c → squareQ a b → squareQ b c → squareQ a c := by
  decide

lemma squareQ_no_greatest :
    ¬ ∃ s : Fin 2 × Fin 2, IsGreatest {b | (0, 0) ≤ b ∧ b ≤ (1, 1) ∧ squareQ (0, 0) b} s := by
  rintro ⟨s, ⟨_, _, hs⟩, hmax⟩
  have h₁ := hmax ⟨by decide, by decide, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
  have h₂ := hmax ⟨by decide, by decide, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)⟩
  clear hmax
  revert hs h₁ h₂
  revert s
  decide

/-! ### The socle iteration on a chain -/

/-- The whole chain `0 < 1 < 2 < 3` as an interval class. -/
def fullClass : IntervalClass (Fin 4) where
  Q _ _ := True
  refl _ := trivial
  trans _ _ _ _ := trivial
  push _ _ _ := trivial

/-- The steps of length at most one, a layer of the whole chain. -/
def stepLayer : fullClass.Layer where
  S a b := b.val ≤ a.val + 1
  refl a := Nat.le_succ _
  sup _ b b' _ _ h h' := by
    rcases le_total b b' with hb | hb
    · rwa [sup_eq_right.mpr hb]
    · rwa [sup_eq_left.mpr hb]
  le _ _ _ _ := trivial
  exists_of_lt a b hlt _ := by
    refine ⟨⟨a.val + 1, by omega⟩, ?_, ?_, le_rfl⟩
    · exact Fin.lt_def.mpr (Nat.lt_succ_self _)
    · exact Fin.le_def.mpr (Fin.lt_def.mp hlt)

theorem fullClass_rad : fullClass.rad = ⊤ :=
  top_le_iff.mp (fullClass.le_rad_of_Q trivial)

/-- The socle iteration reaches the radical `3` after three steps. -/
theorem stepLayer_socleSeq_three : stepLayer.socleSeq ⊥ 3 = ⊤ := by
  rw [← fullClass_rad]
  exact stepLayer.socleSeq_bot_eq_rad_of_le Fin.val Fin.val_strictMono (by
    rw [fullClass_rad]
    decide)

/-! ### The class supported at vertex zero -/

open Quiver.Kronecker

/-- The radical of the class supported at vertex zero is `(⋂ ker Aᵢ, 0)`, for every
representation on finite-dimensional spaces. -/
example {k ι V₀ V₁ : Type*} [Field k] [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
    [Module k V₁] [FiniteDimensional k V₀] [FiniteDimensional k V₁] (M : DoubledRep k ι V₀ V₁) :
    ((DoubledRep.vertexZeroClass M).rad : Submodule k V₀ × Submodule k V₁) =
      (⨅ i, LinearMap.ker (M.A i), ⊥) :=
  DoubledRep.rad_vertexZeroClass

end IntervalClassModel
