/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.DivisibilityObstruction
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Foundation.OneUnitOfWeight

/-!
# The cut criterion for cones in the cases with a known answer

Mathlib has no triangulated category with a slicing yet, so the slicing is a variable here, as in
`HNTowerModel`. The examples apply the statements where the answer is known independently:

* every object splits at `t` both ways, and an object with phases at least `t` and at most `t`
  is semistable of phase `t`;
* a cone on zero, `0 → E → E`, has cut composite zero, so it truncates compatibly;
* a split triangle `P → P ⊞ Q → Q →0 P⟦1⟧` lands in the first branch of the divisibility
  obstruction: `P` is a direct summand of the phase-`φ` factor;
* the one-unit-of-weight lemma when `w(Λ) ⊆ δℤ` and `w(E) = δ`.

Built by `lake test`.
-/

namespace CategoryTheory.Triangulated.ConeCutModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Both splits exist, and the two lower cuts are the left orthogonals of the two upper ones. -/
example (s : Slicing C) (t : ℝ) (E : C) :
    (∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ s.geProp C t X ∧ s.ltProp C t Y) ∧
    (∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ s.gtProp C t X ∧ s.leProp C t Y) :=
  ⟨s.exists_split_geProp_ltProp t E, s.exists_split_gtProp_leProp t E⟩

/-- The slice `P(t)` is the intersection of the cuts `P(≥ t)` and `P(≤ t)`. -/
example (s : Slicing C) (t : ℝ) (X : C) : s.P t X ↔ s.geProp C t X ∧ s.leProp C t X :=
  ⟨fun h => ⟨s.geProp_of_semistable C h, s.leProp_of_semistable C h le_rfl⟩,
    fun h => s.semistable_of_geProp_of_leProp h.1 h.2⟩

/-- A cone on zero truncates compatibly: the truncation of `E` sits in a triangle
`0 → E₁ → E₁ → 0⟦1⟧` over the identity of `E`. -/
example (s : Slicing C) (t : ℝ) (E : C) {E₁ : C} {ι : E₁ ⟶ E}
    (hι : (s.geProp C t).IsCoreflection ι) :
    ∃ (a : (0 : C) ⟶ E₁) (b : E₁ ⟶ E₁),
      Triangle.mk a b (ι ≫ 0) ∈ distTriang C ∧ a ≫ ι = 0 ∧ b ≫ ι = ι ≫ 𝟙 E :=
  s.exists_truncation_triangle_of_geProp (contractible_distinguished₁ E)
    (s.geProp_of_isZero C (isZero_zero C) t) hι hι

/-- A cone on zero has cut composite zero, so all three conditions of the cut criterion hold. -/
example (s : Slicing C) (t : ℝ) (E : C) {E₁ : C} {ι : E₁ ⟶ E}
    (hι : (s.geProp C t).IsCoreflection ι) :
    ∃ c : E₁ ⟶ (0 : C)⟦(1 : ℤ)⟧, c ≫ (𝟙 (0 : C))⟦(1 : ℤ)⟧' = ι ≫ 0 :=
  ((s.cut_criterion (contractible_distinguished₁ E) (contractible_distinguished (0 : C))
    (s.geProp_of_isZero C (isZero_zero C) t) (s.ltProp_of_isZero C (isZero_zero C) t) hι
    hι).out 1 2).1 (by simp)

/-- **The split branch.** For the split triangle `P → P ⊞ Q → Q →0 P⟦1⟧`, the connecting map
vanishes, so `P` is a direct summand of the phase-`φ` HN factor of `P ⊞ Q`. -/
example {k : Type*} [Field k] [Linear k C] (s : Slicing C) {φ : ℝ} {P Q : C} (hP : s.P φ P)
    (hEnd : ∀ f : P ⟶ P, ∃ a : k, f = a • 𝟙 P) {V : C} {ιV : V ⟶ Q}
    (hιV : (s.geProp C φ).IsCoreflection ιV) {E₁ : C} {ιE : E₁ ⟶ P ⊞ Q}
    (hιE : (s.geProp C φ).IsCoreflection ιE) {K G : C} {j : K ⟶ E₁} {π : E₁ ⟶ G}
    {ε : G ⟶ K⟦(1 : ℤ)⟧} (hG : Triangle.mk j π ε ∈ distTriang C) (hK : s.gtProp C φ K) :
    ∃ G' : C, Nonempty (G ≅ P ⊞ G') :=
  (s.divisibility_obstruction_top (k := k) hP hEnd (binaryBiproductTriangle_distinguished P Q)
    hιV hιE hG hK).1 (comp_zero)

/-- **One unit of weight with integral weights.** If `w(Λ) ⊆ δℤ` and `E` has phases in
`[a, a + 1]` with `w(E) = δ`, the middle HN factor of `E` is a nonzero stable object of a phase
in `(a, a + 1)` carrying all of `w(E)`. -/
example {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ} (σ : PreStabilityCondition.WithClassMap C v)
    (a δ : ℝ) (hδ : 0 < δ)
    (hΛ : ∀ γ : Λ, ∃ n : ℤ,
      (Complex.exp ((-(Real.pi * a) : ℝ) * Complex.I) * σ.Z γ).im = n * δ)
    {E : C} (hE₁ : σ.slicing.geProp C a E) (hE₂ : σ.slicing.leProp C (a + 1) E)
    (hE : σ.imChargeAt a E = δ) :
    ∃ (S : C) (ψ : ℝ), a < ψ ∧ ψ < a + 1 ∧ σ.slicing.P ψ S ∧ ¬IsZero S ∧
      σ.imChargeAt a S = δ := by
  obtain ⟨-, -, S, -, -, -, -, -, -, -, ψ, -, -, -, -, -, -, h₁, h₂, hS, hS0, hw, -⟩ :=
    σ.one_unit_of_weight a
      (fun _ _ h₁ h₂ hX hX0 => σ.le_imChargeAt_of_mem_zmultiples a hδ hΛ hX hX0 h₁ h₂)
      hE₁ hE₂ (by rw [hE]; exact hδ) (by rw [hE]; linarith)
  exact ⟨S, ψ, h₁, h₂, hS, hS0, hw.trans hE⟩

end CategoryTheory.Triangulated.ConeCutModel
