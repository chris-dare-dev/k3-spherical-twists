/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Mass.CutLoss
import Mathlib.Data.NNRat.Floor

/-!
# The cut-loss lemma in the cases with a known answer

Mathlib has no triangulated category with a prestability condition yet, so the prestability
condition is a variable here, as in `ConeCutModel`. The examples apply the statements where the
answer is known independently:

* a split triangle `E → E ⊞ G → G →0 E⟦1⟧` with `E` of phases at least `s` and `G` of phases at
  most `s` loses no mass, as the biproduct formula says;
* a triangle `E → F → G` with `E` of phases at least `s` and `G` of phases at most `s` loses no
  mass, and the cut-loss lemma and its dual with the zero cuts `0 → G → G` and `E → E → 0` give
  the same answer under subadditivity;
* if the outer terms of a triangle are semistable of one phase `φ`, so is the middle term, whose
  mass is then the norm of its charge; equal-phase additivity gives the same answer, the sum of
  the norms of two charges on one ray;
* `r` copies of an object have `r` times its mass;
* the cell count at a few values.

Built by `lake test`.
-/

namespace CategoryTheory.Triangulated.CutLossModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- **Zero loss for a split triangle.** For `E` of phases at least `s` and `G` of phases at most
`s`, equal-phase additivity on the split triangle `E → E ⊞ G → G →0 E⟦1⟧` gives
`m(E ⊞ G) = m(E) + m(G)`, the biproduct formula `mass_biprod`. -/
example (σ : PreStabilityCondition.WithClassMap C v) {s : ℝ} {E G : C}
    (hE : σ.slicing.geProp C s E) (hG : σ.slicing.leProp C s G) :
    σ.mass (E ⊞ G) = σ.mass E + σ.mass G :=
  σ.mass_eq_add_of_geProp_leProp (binaryBiproductTriangle_distinguished E G) hE hG

/-- **No loss from the zero cut.** If the third term `G` has phases at most `s`, the cut-loss
lemma with the cut `0 → G → G` gives `m(E) + m(G) ≤ m(F)`, so with subadditivity
`m(F) = m(E) + m(G)`, which equal-phase additivity gives without it. -/
example (σ : PreStabilityCondition.WithClassMap C v) (hσ : σ.MassSubadditive) {s : ℝ}
    {E F G : C} {f : E ⟶ F} {g : F ⟶ G} {h : G ⟶ E⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) (hE : σ.slicing.geProp C s E)
    (hG : σ.slicing.leProp C s G) : σ.mass F = σ.mass E + σ.mass G := by
  have h₁ := σ.mass_add_mass_sub_two_mul_le hσ hT hE (contractible_distinguished₁ G)
    (σ.slicing.geProp_of_isZero C (isZero_zero C) s) hG
  rw [σ.mass_of_isZero (isZero_zero C), mul_zero, sub_zero] at h₁
  exact le_antisymm (σ.mass_le_mass_add_mass hσ hT) h₁

/-- **No loss from the zero cut, dual form.** If the first term `E` has phases at least `s`, the
dual cut-loss lemma with the cut `E → E → 0` gives `m(E) + m(G) ≤ m(F)`. -/
example (σ : PreStabilityCondition.WithClassMap C v) (hσ : σ.MassSubadditive) {s : ℝ}
    {E F G : C} {f : E ⟶ F} {g : F ⟶ G} {h : G ⟶ E⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) (hE : σ.slicing.geProp C s E)
    (hG : σ.slicing.leProp C s G) : σ.mass F = σ.mass E + σ.mass G := by
  have h₁ := σ.mass_add_mass_sub_two_mul_le_dual hσ hT hG (contractible_distinguished E) hE
    (σ.slicing.leProp_of_isZero C (isZero_zero C) s)
  rw [σ.mass_of_isZero (isZero_zero C), mul_zero, sub_zero] at h₁
  exact le_antisymm (σ.mass_le_mass_add_mass hσ hT) h₁

/-- **Equal phases.** If the outer terms of `U → E → Q → U⟦1⟧` are semistable of phase `φ`,
then `m(E) = |Z(U)| + |Z(Q)|`. -/
example (σ : PreStabilityCondition.WithClassMap C v) {φ : ℝ} {U E Q : C} {u : U ⟶ E}
    {e : E ⟶ Q} {δ : Q ⟶ U⟦(1 : ℤ)⟧} (hT : Triangle.mk u e δ ∈ distTriang C)
    (hU : σ.slicing.P φ U) (hQ : σ.slicing.P φ Q) :
    σ.mass E = ‖σ.charge U‖ + ‖σ.charge Q‖ := by
  rw [σ.mass_eq_add_of_geProp_leProp hT (σ.slicing.geProp_of_semistable C hU)
      (σ.slicing.leProp_of_semistable C hQ le_rfl),
    σ.mass_eq_norm_charge_of_semistable hU, σ.mass_eq_norm_charge_of_semistable hQ]

/-- **The same answer from semistability.** In the triangle above, `E` is semistable of phase
`φ` by extension closure, so `m(E) = |Z(E)| = |Z(U) + Z(Q)|`; equal-phase additivity then says
that the norms of the two charges on the ray of phase `φ` add. -/
example (σ : PreStabilityCondition.WithClassMap C v) {φ : ℝ} {U E Q : C} {u : U ⟶ E}
    {e : E ⟶ Q} {δ : Q ⟶ U⟦(1 : ℤ)⟧} (hT : Triangle.mk u e δ ∈ distTriang C)
    (hU : σ.slicing.P φ U) (hQ : σ.slicing.P φ Q) :
    ‖σ.charge U + σ.charge Q‖ = ‖σ.charge U‖ + ‖σ.charge Q‖ := by
  have hE : σ.slicing.P φ E := σ.slicing.semistable_of_geProp_of_leProp
    (σ.slicing.geProp_ext₂ hT (σ.slicing.geProp_of_semistable C hU)
      (σ.slicing.geProp_of_semistable C hQ))
    (σ.slicing.leProp_ext₂ hT (σ.slicing.leProp_of_semistable C hU le_rfl)
      (σ.slicing.leProp_of_semistable C hQ le_rfl))
  have hZ : σ.charge E = σ.charge U + σ.charge Q := by
    have hK := classOf_triangle C v _ hT
    simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at hK
    rw [PreStabilityCondition.WithClassMap.charge_def, hK, map_add]
  rw [← hZ, ← σ.mass_eq_norm_charge_of_semistable hE,
    σ.mass_eq_add_of_geProp_leProp hT (σ.slicing.geProp_of_semistable C hU)
      (σ.slicing.leProp_of_semistable C hQ le_rfl),
    σ.mass_eq_norm_charge_of_semistable hU, σ.mass_eq_norm_charge_of_semistable hQ]

/-- `r` copies of `S` have `r` times its mass. -/
example (σ : PreStabilityCondition.WithClassMap C v) (S : C) (r : ℕ) :
    σ.mass (⨁ fun _ : Fin r ↦ S) = r * σ.mass S := by
  simp [σ.mass_biproduct]

/-- Of the cells `0, 1`, both lie below `5/2`. -/
example : ((Finset.range 2).filter fun j : ℕ ↦ (j : ℝ) < 5 / 2).card = 2 := by
  rw [Nat.card_filter_range_lt_eq_min_ceil]
  norm_num

/-- No cell lies below `0`. -/
example : ((Finset.range 2).filter fun j : ℕ ↦ (j : ℝ) < 0).card = 0 := by
  rw [Nat.card_filter_range_lt_eq_min_ceil]
  simp

/-- No cell lies below `-1`. -/
example : ((Finset.range 2).filter fun j : ℕ ↦ (j : ℝ) < -1).card = 0 := by
  rw [Nat.card_filter_range_lt_eq_min_ceil]
  norm_num

/-- Of the cells `0, 1`, only `0` lies below `3/10`. -/
example : ((Finset.range 2).filter fun j : ℕ ↦ (j : ℝ) < 3 / 10).card = 1 := by
  rw [Nat.card_filter_range_lt_eq_min_ceil]
  norm_num

/-- A ladder of four cells of phases `5/2, 3/2, 1/2, -1/2` has three above the cut `0`. -/
example : ((Finset.range 4).filter fun j : ℕ ↦ (0 : ℝ) < 5 / 2 - j).card = 3 := by
  rw [Nat.card_filter_range_lt_sub_eq_min_ceil]
  norm_num

end CategoryTheory.Triangulated.CutLossModel
