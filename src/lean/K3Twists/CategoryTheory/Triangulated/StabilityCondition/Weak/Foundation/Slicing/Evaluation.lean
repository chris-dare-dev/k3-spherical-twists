/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Uniqueness

/-!
# Evaluation of one phase

The lemma "Evaluation of one phase" of the draft *Harder–Narasimhan towers of spherical twist
words on a Picard-rank-one K3 surface*, as far as it holds in an arbitrary slicing. Let
`M → D → C → M⟦1⟧` be distinguished, `M` the top HN quotient of phase `φ` and every phase of `C`
below `φ`. The draft replaces `D` by the cone of the evaluation `⊕_S Hom⁰(S, D) ⊗ S → D` from the
stable objects `S` of phase `φ`, repeats until these Hom spaces vanish, and recovers `M` as the
fibre of the composite `D → D_final`. Here:

* **Phase separation**: for `S` with all phases at least `φ`, composition with `M → D` is a
  bijection `Hom(S, M) ≃ Hom(S, D)`, since `Hom(S, C) = Hom(S, C⟦-1⟧) = 0`
  (`Slicing.comp_bijective_of_top`); dually for the bottom quotient
  (`Slicing.comp_bijective_of_bottom`).
* **One step keeps the lower tail**: the cone of `S' → M → D` sits in a triangle
  `cone(S' → M) → cone(S' → D) → C`, with the maps from `D` and to `C` compatible
  (`Slicing.exists_evaluation_step`, the octahedral axiom).
* **The end**: an object with phases at most `φ` that receives no nonzero map from `P(φ)` has all
  phases below `φ` (`Slicing.ltProp_of_leProp_of_hom_eq_zero`), and then the fibre of
  `D → D_final`, if its phases are at least `φ`, is `M → D` up to isomorphism over `D`
  (`Slicing.exists_iso_top`).

What needs the abelian structure of the phase slice `P(φ)` is the socle step: that the evaluation
from the socle is a monomorphism in `P(φ)`, so that `cone(S' → M)` is again in `P(φ)` and shorter.
That is a statement about the length category `P(φ)` (Bridgeland, arXiv:math/0212237, Lemma 5.2,
and local finiteness), not formalized here.

## Tags

stability condition, slicing, Harder–Narasimhan filtration, evaluation, octahedral axiom
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Slicing

/-- Every map from an object with phases at least `t` to one with phases below `t` vanishes. -/
theorem hom_eq_zero_of_geProp_ltProp (s : Slicing C) {t : ℝ} {X Y : C} (hX : s.geProp C t X)
    (hY : s.ltProp C t Y) (f : X ⟶ Y) : f = 0 :=
  s.zero_of_geProp_ltProp_at C t hX hY f

/-- Every map from an object with phases above `t` to one with phases at most `t` vanishes. -/
theorem hom_eq_zero_of_gtProp_leProp (s : Slicing C) {t : ℝ} {X Y : C} (hX : s.gtProp C t X)
    (hY : s.leProp C t Y) (f : X ⟶ Y) : f = 0 := by
  rcases hX with hX | ⟨FX, hFX, hFXgt⟩
  · exact hX.eq_of_src f 0
  rcases hY with hY | ⟨FY, hFY, hFYle⟩
  · exact hY.eq_of_tgt f 0
  exact s.hom_eq_zero_of_phase_gap C FX FY
    (fun i j => lt_of_le_of_lt ((FY.phase_mem_range C hFY j).2.trans hFYle)
      (hFXgt.trans_le (FX.phase_mem_range C hFX i).1)) f

/-- Phases below `t` stay below `t` after a negative shift. -/
theorem ltProp_shift_neg_one (s : Slicing C) {t : ℝ} {X : C} (hX : s.ltProp C t X) :
    s.ltProp C t (X⟦(-1 : ℤ)⟧) :=
  s.ltProp_mono C (show t + ((-1 : ℤ) : ℝ) ≤ t by push_cast; linarith) _
    (s.ltProp_shift C t X (-1) hX)

/-- Phases above `t` stay above `t` after a positive shift. -/
theorem gtProp_shift_one (s : Slicing C) {t : ℝ} {X : C} (hX : s.gtProp C t X) :
    s.gtProp C t (X⟦(1 : ℤ)⟧) :=
  s.gtProp_anti C (show t ≤ t + ((1 : ℤ) : ℝ) by push_cast; linarith) _
    (s.gtProp_shift C t X 1 hX)

/-- **Phase separation at the top.** Let `M → D → C → M⟦1⟧` be distinguished with every phase
of `C` below `t`. For `S` with every phase at least `t`, composition with `M → D` is a bijection
`Hom(S, M) → Hom(S, D)`. -/
theorem comp_bijective_of_top (s : Slicing C) {t : ℝ} {M D C' S : C} {ι : M ⟶ D}
    {q : D ⟶ C'} {δ : C' ⟶ M⟦(1 : ℤ)⟧} (hT : Triangle.mk ι q δ ∈ distTriang C)
    (hC : s.ltProp C t C') (hS : s.geProp C t S) :
    Function.Bijective (fun f : S ⟶ M => f ≫ ι) := by
  refine ⟨fun f₁ f₂ h => ?_, fun g => ?_⟩
  · have hx : (f₁ - f₂) ≫ ι = 0 := by
      simp only at h
      rw [Preadditive.sub_comp, h, sub_self]
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ (Triangle.mk ι q δ).invRotate
      (inv_rot_of_distTriang _ hT) (f₁ - f₂) hx
    have hy0 : y = 0 := s.hom_eq_zero_of_geProp_ltProp hS (s.ltProp_shift_neg_one hC) y
    rw [hy0, zero_comp] at hy
    exact sub_eq_zero.mp hy
  · obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₂ (Triangle.mk ι q δ) hT g
      (s.hom_eq_zero_of_geProp_ltProp hS hC _)
    exact ⟨f, hf.symm⟩

/-- **Phase separation at the bottom.** Let `N' → D → N → N'⟦1⟧` be distinguished with every
phase of `N'` above `t`. For `S` with every phase at most `t`, composition with `D → N` is a
bijection `Hom(N, S) → Hom(D, S)`: the dual evaluation `D → ⊕ Hom⁰(D, S)^* ⊗ S` of the draft
sees only the bottom quotient. -/
theorem comp_bijective_of_bottom (s : Slicing C) {t : ℝ} {N' D N S : C} {j : N' ⟶ D}
    {p : D ⟶ N} {d : N ⟶ N'⟦(1 : ℤ)⟧} (hT : Triangle.mk j p d ∈ distTriang C)
    (hN' : s.gtProp C t N') (hS : s.leProp C t S) :
    Function.Bijective (fun f : N ⟶ S => p ≫ f) := by
  refine ⟨fun f₁ f₂ h => ?_, fun g => ?_⟩
  · have hx : p ≫ (f₁ - f₂) = 0 := by
      simp only at h
      rw [Preadditive.comp_sub, h, sub_self]
    obtain ⟨y, hy⟩ := Triangle.yoneda_exact₃ (Triangle.mk j p d) hT (f₁ - f₂) hx
    have hy0 : y = 0 := s.hom_eq_zero_of_gtProp_leProp (s.gtProp_shift_one hN') hS y
    rw [hy0, comp_zero] at hy
    exact sub_eq_zero.mp hy
  · obtain ⟨f, hf⟩ := Triangle.yoneda_exact₂ (Triangle.mk j p d) hT g
      (s.hom_eq_zero_of_gtProp_leProp hN' hS _)
    exact ⟨f, hf.symm⟩

/-- **The end of the evaluation.** An object whose phases are at most `t` and which receives no
nonzero map from a semistable object of phase `t` has all its phases below `t`. -/
theorem ltProp_of_leProp_of_hom_eq_zero (s : Slicing C) {t : ℝ} {D : C}
    (hD : s.leProp C t D) (h : ∀ (S : C), s.P t S → ∀ f : S ⟶ D, f = 0) :
    s.ltProp C t D := by
  rcases hD with hD | ⟨F, hn, hle⟩
  · exact Or.inl hD
  by_cases hlt : F.phiPlus C hn < t
  · exact Or.inr ⟨F, hn, hlt⟩
  have heq : F.φ ⟨0, hn⟩ = t := le_antisymm hle (not_lt.mp hlt)
  have hzero : IsZero (F.factor ⟨0, hn⟩) :=
    F.firstFactor_isZero_of_hom_eq_zero C s hn (h _ (heq ▸ F.semistable ⟨0, hn⟩))
  by_cases hn1 : 1 < F.n
  · refine Or.inr ⟨F.dropFirst C hn1 hzero, by change 0 < F.n - 1; omega, ?_⟩
    change F.φ ⟨0 + 1, by omega⟩ < t
    rw [← heq]
    exact F.hφ (Fin.mk_lt_mk.mpr (by omega))
  · refine Or.inl ?_
    by_contra hD
    obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hD
    exact hi (by rwa [show i = ⟨0, hn⟩ from Fin.ext (by omega)])

/-- **The fibre is the top quotient.** Let `M → D → C → M⟦1⟧` and `K → D → D' → K⟦1⟧` be
distinguished, with `M` and `K` of phases at least `t` and `C` and `D'` of phases below `t`. Then
the two triangles are isomorphic by an isomorphism that is the identity on `D`; in particular
`K → D` is `M → D` up to an isomorphism `K ≅ M`. -/
theorem exists_iso_top (s : Slicing C) {t : ℝ} {M D C' K D' : C} {ι : M ⟶ D} {q : D ⟶ C'}
    {δ : C' ⟶ M⟦(1 : ℤ)⟧} (hT : Triangle.mk ι q δ ∈ distTriang C) {κ : K ⟶ D} {p : D ⟶ D'}
    {ε : D' ⟶ K⟦(1 : ℤ)⟧} (hT' : Triangle.mk κ p ε ∈ distTriang C) (hM : s.geProp C t M)
    (hC : s.ltProp C t C') (hK : s.geProp C t K) (hD' : s.ltProp C t D') :
    ∃ e : K ≅ M, κ = e.hom ≫ ι ∧ Nonempty (D' ≅ C') := by
  obtain ⟨i, hi⟩ := exists_iso_of_hom_eq_zero hT' hT (Iso.refl D)
    (fun f => s.hom_eq_zero_of_geProp_ltProp hK hC f)
    (fun f => s.hom_eq_zero_of_geProp_ltProp hM hD' f)
    (fun f => s.hom_eq_zero_of_geProp_ltProp hK (s.ltProp_shift_neg_one hD') f)
    (fun f => s.hom_eq_zero_of_geProp_ltProp hM (s.ltProp_shift_neg_one hC) f)
  refine ⟨Triangle.π₁.mapIso i, ?_, ⟨Triangle.π₃.mapIso i⟩⟩
  have hc := i.hom.comm₁
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, hi, Iso.refl_hom,
    Category.comp_id] at hc
  simpa using hc

end Slicing

/-- **One evaluation step keeps the lower tail.** Let `M → D → C → M⟦1⟧` be distinguished and
`S' → M → M₁ → S'⟦1⟧` distinguished. The cone `D₁` of the composite `S' → M → D` sits in a
distinguished triangle `M₁ → D₁ → C → M₁⟦1⟧` whose maps are compatible with `D → D₁` and
`D → C`: removing part of the top quotient leaves the lower tail `C` unchanged. -/
theorem Slicing.exists_evaluation_step [IsTriangulated C] {S' M D C' M₁ : C} {a : S' ⟶ M}
    {b : M ⟶ M₁} {c : M₁ ⟶ S'⟦(1 : ℤ)⟧} (hA : Triangle.mk a b c ∈ distTriang C) {ι : M ⟶ D}
    {q : D ⟶ C'} {δ : C' ⟶ M⟦(1 : ℤ)⟧} (hT : Triangle.mk ι q δ ∈ distTriang C) :
    ∃ (D₁ : C) (r : D ⟶ D₁) (w : D₁ ⟶ S'⟦(1 : ℤ)⟧) (m : M₁ ⟶ D₁) (n : D₁ ⟶ C'),
      Triangle.mk (a ≫ ι) r w ∈ distTriang C ∧
        Triangle.mk m n (δ ≫ b⟦(1 : ℤ)⟧') ∈ distTriang C ∧ b ≫ m = ι ≫ r ∧ r ≫ n = q := by
  obtain ⟨D₁, r, w, hD⟩ := distinguished_cocone_triangle (a ≫ ι)
  let o := Triangulated.someOctahedron rfl hA hT hD
  exact ⟨D₁, r, w, o.m₁, o.m₃, hD, o.mem, o.comm₁, o.comm₃⟩

end CategoryTheory.Triangulated
