/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ConeHN
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.TStructure

/-!
# The cut criterion for cones at a strict cut

`Slicing/ConeHN.lean` cuts a distinguished triangle `U → E → Q →δ U⟦1⟧` at a real number `t`
with the `(≥ t, < t)` truncations. This file states the same criterion for the
`(> t, ≤ t)` truncations: the cut that an HN filtration produces directly
(`Slicing.exists_split_gtProp_leProp`, `HNFiltration.exists_split_at_cutoff`), and whose two
classes `P(> t)`, `P(≤ t)` are the aisle and coaisle of the t-structure `s.toTStructure t`. Write
`U_{>t} → U → U_{≤t}` and `Q_{>t} → Q → Q_{≤t}` for the truncations of the two ends,

  `d_t : Q_{>t} → Q →δ U⟦1⟧ → U_{≤t}⟦1⟧`

for the cut composite, and `E' = cofib(U_{>t} → U → E)`; the octahedral axiom places `E'` in a
distinguished triangle `U_{≤t} → E' → Q → U_{≤t}⟦1⟧` (`Pretriangulated.exists_cofib_triangles`).

* **(A)** `E_{>t} = E ×ʰ_{E'} E'_{>t}` (`Slicing.exists_gtProp_pullback`), and the induced map
  `κ : E'_{>t} → Q_{>t}` represents the kernel of `d_t ∘ −` on objects of phases above `t`
  (`Slicing.cutMap_injective_gtProp`, `Slicing.exists_comp_cutMap_iff_gtProp`).
* **(B)** The triangle truncates compatibly at `t`, there is a distinguished triangle
  `U_{>t} → E_{>t} → Q_{>t} → U_{>t}⟦1⟧` mapping to `U → E → Q → U⟦1⟧`, exactly when `κ` is an
  isomorphism, exactly when `d_t = 0` (`Slicing.isIso_cutMap_iff_gtProp`,
  `Slicing.cut_criterion_gtProp`); the lift `Q_{>t} → U_{>t}⟦1⟧` is then unique
  (`Slicing.existsUnique_cut_lift_iff_gtProp`). If `U` has all its phases above `t`, the criterion
  holds (`Slicing.exists_truncation_triangle_of_gtProp`).
* **(C)** If `Q` has no phase above `θ ≥ t`, then `E'_{>t}` and `Q_{>t}` have their phases in
  `(t, θ]`, and `κ` is the largest map into `Q_{>t}` from that interval killed by `d_t`
  (`Slicing.cutMap_gtProp_of_leProp`). For `θ = t + 1` the interval is the heart `P((t, t + 1])`,
  an abelian category (`Slicing.HeartCat`): there `κ` is the largest monomorphism into `Q_{>t}`
  killed by `d_t` (`Slicing.cutMap_gtProp_heart`). The single slice `P(θ)` of the
  `(≥ θ, < θ)` form has no analogue here, since `P(> t) ∩ P(≤ θ)` is never one slice.

As in `Slicing/ConeHN.lean`, everything holds for an arbitrary slicing on a triangulated category,
the truncations of `U` and the cofibre enter as distinguished triangles (any choice), and those of
`Q`, `E` and `E'` through their coreflection property.

## Tags

slicing, stability condition, Harder–Narasimhan filtration, cone, octahedral axiom, truncation
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated.Slicing

/-! ### (A) The top truncation as a homotopy pullback -/

/-- **Cut criterion for cones at a strict cut, (A): the homotopy pullback.** Let
`U₁ → E → E' →w U₁⟦1⟧` be distinguished with `U₁` of phases above `t` (in the criterion,
`U₁ = U_{>t}`), and let `E'₁ → E' → E'₂` be the `(> t, ≤ t)` truncation of `E'`. The fibre `E₁` of
`E → E' → E'₂` sits in distinguished triangles `U₁ → E₁ → E'₁` and `E₁ → E → E'₂`; it has phases
above `t` and `E₁ → E` is the coreflection of `E` into `P(> t)`. So
`E_{>t} = E ×ʰ_{E'} E'_{>t}`. -/
theorem exists_gtProp_pullback [IsTriangulated C] (s : Slicing C) {t : ℝ} {U₁ E E' : C}
    {f : U₁ ⟶ E} {p : E ⟶ E'} {w : E' ⟶ U₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f p w ∈ distTriang C)
    (hU₁ : s.gtProp C t U₁) {E'₁ E'₂ : C} {ι : E'₁ ⟶ E'} {π : E' ⟶ E'₂}
    {ε : E'₂ ⟶ E'₁⟦(1 : ℤ)⟧} (hT' : Triangle.mk ι π ε ∈ distTriang C)
    (hE'₁ : s.gtProp C t E'₁) (hE'₂ : s.leProp C t E'₂) :
    ∃ (E₁ : C) (f' : U₁ ⟶ E₁) (g' : E₁ ⟶ E'₁) (ιE : E₁ ⟶ E) (w' : E'₂ ⟶ E₁⟦(1 : ℤ)⟧),
      Triangle.mk f' g' (ι ≫ w) ∈ distTriang C ∧ Triangle.mk ιE (p ≫ π) w' ∈ distTriang C ∧
        f' ≫ ιE = f ∧ g' ≫ ι = ιE ≫ p ∧ s.gtProp C t E₁ ∧
          (s.gtProp C t).IsCoreflection ιE := by
  obtain ⟨E₁, f', g', ιE, w', h₁, h₂, c₁, c₂, -, -⟩ := exists_pullback_triangles hT hT'
  have hE₁ : s.gtProp C t E₁ := s.gtProp_ext₂ h₁ hU₁ hE'₁
  exact ⟨E₁, f', g', ιE, w', h₁, h₂, c₁, c₂, hE₁,
    s.isCoreflection_gtProp_of_triangle h₂ hE₁ hE'₂⟩

/-! ### (A) The kernel of the cut composite -/

section Kernel

variable (s : Slicing C) {t : ℝ} {U₂ E' Q : C} {m₁ : U₂ ⟶ E'} {m₃ : E' ⟶ Q}
  {δ' : Q ⟶ U₂⟦(1 : ℤ)⟧} {E'₁ Q₁ : C} {ι' : E'₁ ⟶ E'} {ιQ : Q₁ ⟶ Q} {κ : E'₁ ⟶ Q₁}

/-- **Cut criterion for cones at a strict cut, (A): `κ` is injective on `P(> t)`.** Let
`U₂ → E' → Q →δ' U₂⟦1⟧` be distinguished with `U₂` of phases at most `t` (in the criterion,
`U₂ = U_{≤t}` and `δ'` is `δ` followed by the truncation), let `ι' : E'₁ → E'` and
`ιQ : Q₁ → Q` be coreflections into `P(> t)`, and let `κ : E'₁ → Q₁` lie over `E' → Q`. For `X`
of phases above `t`, composition with `κ` is injective on `Hom(X, E'₁)`. -/
theorem cutMap_injective_gtProp (hT : Triangle.mk m₁ m₃ δ' ∈ distTriang C)
    (hU₂ : s.leProp C t U₂) (hι' : (s.gtProp C t).IsCoreflection ι')
    (hκ : κ ≫ ιQ = ι' ≫ m₃) {X : C} (hX : s.gtProp C t X) :
    Function.Injective fun g : X ⟶ E'₁ => g ≫ κ := by
  intro g₁ g₂ h
  simp only at h
  have hx : ((g₁ - g₂) ≫ ι') ≫ m₃ = 0 := by
    rw [Category.assoc, ← hκ, Preadditive.sub_comp, ← Category.assoc, h, Category.assoc,
      sub_self]
  obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ _ hT _ hx
  have hy0 : y = 0 := s.hom_eq_zero_of_gtProp_leProp hX hU₂ y
  rw [hy0, zero_comp, Preadditive.sub_comp, sub_eq_zero] at hy
  exact hι'.hom_ext hX hy

/-- **Cut criterion for cones at a strict cut, (A): `κ` represents `ker(d ∘ −)` on `P(> t)`.**
In the setting of `Slicing.cutMap_injective_gtProp`, a map `f : X → Q₁` from an object of phases
above `t` factors through `κ` exactly when it is killed by the cut composite `d = ιQ ≫ δ'`. -/
theorem exists_comp_cutMap_iff_gtProp (hT : Triangle.mk m₁ m₃ δ' ∈ distTriang C)
    (hι' : (s.gtProp C t).IsCoreflection ι') (hιQ : (s.gtProp C t).IsCoreflection ιQ)
    (hκ : κ ≫ ιQ = ι' ≫ m₃) {X : C} (hX : s.gtProp C t X) (f : X ⟶ Q₁) :
    (∃ g : X ⟶ E'₁, g ≫ κ = f) ↔ f ≫ ιQ ≫ δ' = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    have h0 : m₃ ≫ δ' = 0 := comp_distTriang_mor_zero₂₃ _ hT
    rw [Category.assoc, reassoc_of% hκ, h0, comp_zero, comp_zero]
  · intro hf
    obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₃ _ hT (f ≫ ιQ)
      (show (f ≫ ιQ) ≫ δ' = 0 by rw [Category.assoc, hf])
    have hx' : f ≫ ιQ = x ≫ m₃ := hx
    refine ⟨hι'.lift hX x, hιQ.hom_ext hX ?_⟩
    rw [Category.assoc, hκ, hι'.lift_comp_assoc]
    exact hx'.symm

/-- **Cut criterion for cones at a strict cut, (B): `κ` is an isomorphism exactly when `d = 0`.** -/
theorem isIso_cutMap_iff_gtProp (hT : Triangle.mk m₁ m₃ δ' ∈ distTriang C)
    (hU₂ : s.leProp C t U₂) (hι' : (s.gtProp C t).IsCoreflection ι')
    (hιQ : (s.gtProp C t).IsCoreflection ιQ) (hκ : κ ≫ ιQ = ι' ≫ m₃) :
    IsIso κ ↔ ιQ ≫ δ' = 0 := by
  constructor
  · intro _
    have := (s.exists_comp_cutMap_iff_gtProp hT hι' hιQ hκ hιQ.prop (𝟙 Q₁)).1 ⟨inv κ, by simp⟩
    simpa using this
  · intro hd
    obtain ⟨g, hg⟩ := (s.exists_comp_cutMap_iff_gtProp hT hι' hιQ hκ hιQ.prop (𝟙 Q₁)).2
      (by simpa using hd)
    refine ⟨g, s.cutMap_injective_gtProp hT hU₂ hι' hκ hι'.prop ?_, hg⟩
    simp only [Category.assoc, hg, Category.comp_id, Category.id_comp]

end Kernel

/-! ### (B) The cut criterion -/

/-- **Uniqueness of the lift at a strict cut.** Let `U₁ → U → U₂ → U₁⟦1⟧` be distinguished with
`U₂` of phases at most `t`. Two maps `Q₁ → U₁⟦1⟧` from an object of phases above `t` that agree
after `U₁⟦1⟧ → U⟦1⟧` are equal, since `Hom(Q₁, U₂) = 0`. -/
theorem cut_lift_unique_gtProp (s : Slicing C) {t : ℝ} {U U₁ U₂ : C} {ιU : U₁ ⟶ U}
    {πU : U ⟶ U₂} {εU : U₂ ⟶ U₁⟦(1 : ℤ)⟧} (hU : Triangle.mk ιU πU εU ∈ distTriang C)
    (hU₂ : s.leProp C t U₂) {Q₁ : C} (hQ₁ : s.gtProp C t Q₁) {c c' : Q₁ ⟶ U₁⟦(1 : ℤ)⟧}
    (h : c ≫ ιU⟦(1 : ℤ)⟧' = c' ≫ ιU⟦(1 : ℤ)⟧') : c = c' := by
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ hU (c - c')
    (show (c - c') ≫ ιU⟦(1 : ℤ)⟧' = 0 by rw [Preadditive.sub_comp, h, sub_self])
  have hg0 : g = 0 := s.hom_eq_zero_of_gtProp_leProp hQ₁ hU₂ g
  rw [hg0, zero_comp, sub_eq_zero] at hg
  exact hg

/-- The lift exists when the cut composite vanishes. -/
private theorem exists_cut_lift_gtProp {U U₁ U₂ : C} {ιU : U₁ ⟶ U} {πU : U ⟶ U₂}
    {εU : U₂ ⟶ U₁⟦(1 : ℤ)⟧} (hU : Triangle.mk ιU πU εU ∈ distTriang C) {Q₁ : C}
    (f : Q₁ ⟶ U⟦(1 : ℤ)⟧) (hf : f ≫ πU⟦(1 : ℤ)⟧' = 0) :
    ∃ c : Q₁ ⟶ U₁⟦(1 : ℤ)⟧, c ≫ ιU⟦(1 : ℤ)⟧' = f := by
  have hR := rot_of_distTriang _ (rot_of_distTriang _ hU)
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ hR f
    (show f ≫ (-(πU⟦(1 : ℤ)⟧')) = 0 by rw [Preadditive.comp_neg, hf, neg_zero])
  let g' : Q₁ ⟶ U₁⟦(1 : ℤ)⟧ := g
  have hg' : f = g' ≫ (-(ιU⟦(1 : ℤ)⟧')) := hg
  refine ⟨-g', ?_⟩
  rw [hg', Preadditive.comp_neg, Preadditive.neg_comp]

/-- **The cut criterion for cones at a strict cut, (B).** Let `U → E → Q →δ U⟦1⟧` be
distinguished, let `U₁ → U → U₂ → U₁⟦1⟧` be the `(> t, ≤ t)` truncation of `U`, and let
`ιQ : Q₁ → Q` and `ιE : E₁ → E` be the coreflections of `Q` and `E` into `P(> t)`. The following
are equivalent:

1. the cut composite `d_t : Q₁ → Q → U⟦1⟧ → U₂⟦1⟧` vanishes;
2. `Q₁ → Q → U⟦1⟧` lifts to `U₁⟦1⟧` (the lift is unique: `Slicing.cut_lift_unique_gtProp`);
3. the triangle truncates compatibly: there is a distinguished triangle
   `U₁ → E₁ → Q₁ → U₁⟦1⟧` whose three maps commute with the truncation maps and the maps of
   `U → E → Q → U⟦1⟧`. -/
theorem cut_criterion_gtProp [IsTriangulated C] (s : Slicing C) {t : ℝ} {U E Q : C}
    {u : U ⟶ E} {e : E ⟶ Q} {δ : Q ⟶ U⟦(1 : ℤ)⟧} (hT : Triangle.mk u e δ ∈ distTriang C)
    {U₁ U₂ : C} {ιU : U₁ ⟶ U} {πU : U ⟶ U₂} {εU : U₂ ⟶ U₁⟦(1 : ℤ)⟧}
    (hU : Triangle.mk ιU πU εU ∈ distTriang C) (hU₁ : s.gtProp C t U₁)
    (hU₂ : s.leProp C t U₂) {Q₁ : C} {ιQ : Q₁ ⟶ Q} (hιQ : (s.gtProp C t).IsCoreflection ιQ)
    {E₁ : C} {ιE : E₁ ⟶ E} (hιE : (s.gtProp C t).IsCoreflection ιE) :
    List.TFAE [ιQ ≫ δ ≫ πU⟦(1 : ℤ)⟧' = 0,
      ∃ c : Q₁ ⟶ U₁⟦(1 : ℤ)⟧, c ≫ ιU⟦(1 : ℤ)⟧' = ιQ ≫ δ,
      ∃ (a : U₁ ⟶ E₁) (b : E₁ ⟶ Q₁) (c : Q₁ ⟶ U₁⟦(1 : ℤ)⟧),
        Triangle.mk a b c ∈ distTriang C ∧ a ≫ ιE = ιU ≫ u ∧ b ≫ ιQ = ιE ≫ e ∧
          c ≫ ιU⟦(1 : ℤ)⟧' = ιQ ≫ δ] := by
  tfae_have 1 → 3 := by
    intro hd
    obtain ⟨E', p, w, m₁, m₃, hE', hM, -, -, hpm, hwm⟩ := exists_cofib_triangles hT hU
    obtain ⟨E'₁, E'₂, ι', π', ε', hS, h₁, h₂⟩ := s.exists_split_gtProp_leProp t E'
    have hι' := s.isCoreflection_gtProp_of_triangle hS h₁ h₂
    let κ : E'₁ ⟶ Q₁ := hιQ.lift h₁ (ι' ≫ m₃)
    have hκ : κ ≫ ιQ = ι' ≫ m₃ := hιQ.lift_comp h₁ _
    have : IsIso κ := (s.isIso_cutMap_iff_gtProp hM hU₂ hι' hιQ hκ).2 (by simpa using hd)
    obtain ⟨B, f', g', ιB, w', hB₁, -, cf, cg, -, hιB⟩ :=
      s.exists_gtProp_pullback hE' hU₁ hS h₁ h₂
    let φ : B ≅ E₁ := hιB.isoOfIsCoreflection hιE
    have hφ : φ.hom ≫ ιE = ιB := hιB.isoOfIsCoreflection_hom_comp hιE
    have hφ' : φ.inv ≫ ιB = ιE := by rw [← hφ, Iso.inv_hom_id_assoc]
    refine ⟨f' ≫ φ.hom, φ.inv ≫ g' ≫ κ, inv κ ≫ ι' ≫ w, ?_, ?_, ?_, ?_⟩
    · refine isomorphic_distinguished _ hB₁ _ (Triangle.isoMk _ _ (Iso.refl _) φ.symm
        (asIso κ).symm ?_ ?_ ?_)
      · simp
      · simp
      · simp
    · rw [Category.assoc, hφ, cf]
    · rw [Category.assoc, Category.assoc, hκ, reassoc_of% cg, hpm, reassoc_of% hφ']
    · rw [Category.assoc, Category.assoc, hwm, ← reassoc_of% hκ, IsIso.inv_hom_id_assoc]
  tfae_have 3 → 2 := fun ⟨_, _, c, _, _, _, hc⟩ => ⟨c, hc⟩
  tfae_have 2 → 1 := by
    rintro ⟨c, hc⟩
    have h0 : ιU ≫ πU = 0 := comp_distTriang_mor_zero₁₂ _ hU
    rw [← Category.assoc, ← hc, Category.assoc, ← Functor.map_comp, h0, Functor.map_zero,
      comp_zero]
  tfae_finish

/-- **The lift is unique at a strict cut.** In the setting of `Slicing.cut_criterion_gtProp`,
`Q₁ → Q → U⟦1⟧` has a unique lift to `U₁⟦1⟧` exactly when the cut composite vanishes. -/
theorem existsUnique_cut_lift_iff_gtProp (s : Slicing C) {t : ℝ} {U Q : C}
    {δ : Q ⟶ U⟦(1 : ℤ)⟧} {U₁ U₂ : C} {ιU : U₁ ⟶ U} {πU : U ⟶ U₂} {εU : U₂ ⟶ U₁⟦(1 : ℤ)⟧}
    (hU : Triangle.mk ιU πU εU ∈ distTriang C) (hU₂ : s.leProp C t U₂) {Q₁ : C}
    {ιQ : Q₁ ⟶ Q} (hQ₁ : s.gtProp C t Q₁) :
    (∃! c : Q₁ ⟶ U₁⟦(1 : ℤ)⟧, c ≫ ιU⟦(1 : ℤ)⟧' = ιQ ≫ δ) ↔ ιQ ≫ δ ≫ πU⟦(1 : ℤ)⟧' = 0 := by
  constructor
  · rintro ⟨c, hc, -⟩
    have h0 : ιU ≫ πU = 0 := comp_distTriang_mor_zero₁₂ _ hU
    rw [← Category.assoc, ← hc, Category.assoc, ← Functor.map_comp, h0, Functor.map_zero,
      comp_zero]
  · intro hd
    obtain ⟨c, hc⟩ := exists_cut_lift_gtProp hU (ιQ ≫ δ) (by simpa using hd)
    exact ⟨c, hc, fun c' hc' => s.cut_lift_unique_gtProp hU hU₂ hQ₁ (hc'.trans hc.symm)⟩

/-- **No cut on the first term at a strict cut.** If `U` has all its phases above `t`, every
distinguished triangle `U → E → Q →δ U⟦1⟧` truncates compatibly at `t`: for the coreflections
`ιQ : Q₁ → Q` and `ιE : E₁ → E` into `P(> t)` there is a distinguished triangle
`U → E₁ → Q₁ → U⟦1⟧` whose maps lie over `U → E`, over `E → Q`, and whose last map is
`ιQ ≫ δ`. -/
theorem exists_truncation_triangle_of_gtProp [IsTriangulated C] (s : Slicing C) {t : ℝ}
    {U E Q : C} {u : U ⟶ E} {e : E ⟶ Q} {δ : Q ⟶ U⟦(1 : ℤ)⟧}
    (hT : Triangle.mk u e δ ∈ distTriang C) (hU : s.gtProp C t U) {Q₁ : C} {ιQ : Q₁ ⟶ Q}
    (hιQ : (s.gtProp C t).IsCoreflection ιQ) {E₁ : C} {ιE : E₁ ⟶ E}
    (hιE : (s.gtProp C t).IsCoreflection ιE) :
    ∃ (a : U ⟶ E₁) (b : E₁ ⟶ Q₁),
      Triangle.mk a b (ιQ ≫ δ) ∈ distTriang C ∧ a ≫ ιE = u ∧ b ≫ ιQ = ιE ≫ e := by
  have h₀ : s.leProp C t (0 : C) := s.leProp_of_isZero C (isZero_zero C) t
  obtain ⟨a, b, c, hA, ha, hb, hc⟩ := ((s.cut_criterion_gtProp hT (contractible_distinguished U)
    hU h₀ hιQ hιE).out 1 3).1 (by simp)
  have hc' : c = ιQ ≫ δ := by simpa using hc
  subst hc'
  exact ⟨a, b, hA, by simpa using ha, hb⟩

/-! ### (C) The interval below a phase bound -/

/-- The coreflection into `P(> t)` of an object with no phase above `θ ≥ t` has no phase above
`θ`. -/
theorem leProp_of_isCoreflection_gtProp [IsTriangulated C] (s : Slicing C) {t θ : ℝ}
    (htθ : t ≤ θ) {D R : C} {ι : D ⟶ R} (hι : (s.gtProp C t).IsCoreflection ι)
    (hR : s.leProp C θ R) : s.leProp C θ D := by
  refine s.leProp_iff_hom_eq_zero.2 fun X hX f => ?_
  have hX' : s.gtProp C t X := s.gtProp_anti C htθ X hX
  refine hι.hom_ext hX' ?_
  rw [zero_comp]
  exact s.hom_eq_zero_of_gtProp_leProp hX hR _

/-- **Cut criterion for cones at a strict cut, (C): the interval below a phase bound.** In the
setting of `Slicing.cutMap_injective_gtProp`, suppose `Q` has no phase above `θ ≥ t`. Then
`E'₁ = E'_{>t}` and `Q₁ = Q_{>t}` have their phases in `(t, θ]`, and `κ : E'₁ → Q₁` is the
largest map into `Q₁` from `P(> t)` killed by `d_t = ιQ ≫ δ'`: composition with `κ` is injective
on maps from `P(> t)`, `κ` is killed by `d_t`, and every map from `P(> t)` to `Q₁` killed by `d_t`
factors uniquely through `κ`. -/
theorem cutMap_gtProp_of_leProp [IsTriangulated C] (s : Slicing C) {t θ : ℝ} (htθ : t ≤ θ)
    {U₂ E' Q : C} {m₁ : U₂ ⟶ E'} {m₃ : E' ⟶ Q} {δ' : Q ⟶ U₂⟦(1 : ℤ)⟧}
    (hT : Triangle.mk m₁ m₃ δ' ∈ distTriang C) (hU₂ : s.leProp C t U₂) (hQ : s.leProp C θ Q)
    {E'₁ Q₁ : C} {ι' : E'₁ ⟶ E'} (hι' : (s.gtProp C t).IsCoreflection ι') {ιQ : Q₁ ⟶ Q}
    (hιQ : (s.gtProp C t).IsCoreflection ιQ) {κ : E'₁ ⟶ Q₁} (hκ : κ ≫ ιQ = ι' ≫ m₃) :
    (s.gtProp C t E'₁ ∧ s.leProp C θ E'₁) ∧ (s.gtProp C t Q₁ ∧ s.leProp C θ Q₁) ∧
      κ ≫ ιQ ≫ δ' = 0 ∧
      (∀ ⦃X : C⦄, s.gtProp C t X → Function.Injective fun g : X ⟶ E'₁ => g ≫ κ) ∧
      ∀ ⦃X : C⦄, s.gtProp C t X → ∀ f : X ⟶ Q₁, f ≫ ιQ ≫ δ' = 0 →
        ∃! g : X ⟶ E'₁, g ≫ κ = f := by
  have hE' : s.leProp C θ E' := s.leProp_ext₂ hT (s.leProp_mono C htθ _ hU₂) hQ
  refine ⟨⟨hι'.prop, s.leProp_of_isCoreflection_gtProp htθ hι' hE'⟩,
    ⟨hιQ.prop, s.leProp_of_isCoreflection_gtProp htθ hιQ hQ⟩,
    (s.exists_comp_cutMap_iff_gtProp hT hι' hιQ hκ hι'.prop κ).1 ⟨𝟙 _, Category.id_comp _⟩,
    fun X hX => s.cutMap_injective_gtProp hT hU₂ hι' hκ hX, fun X hX f hf => ?_⟩
  obtain ⟨g, hg⟩ := (s.exists_comp_cutMap_iff_gtProp hT hι' hιQ hκ hX f).2 hf
  exact ⟨g, hg, fun g' hg' => s.cutMap_injective_gtProp hT hU₂ hι' hκ hX (hg'.trans hg.symm)⟩

/-- **(C) in the heart.** If `Q` has no phase above `t + 1`, then `E'_{>t}` and `Q_{>t}` lie in
the heart `P((t, t + 1])` of `s.toTStructure t`, an abelian category, and `κ` is the largest
monomorphism into `Q_{>t}` there killed by `d_t`: composition with `κ` is injective on maps from
the heart, `κ` is killed by `d_t`, and every map from the heart to `Q_{>t}` killed by `d_t`
factors uniquely through `κ`. -/
theorem cutMap_gtProp_heart [IsTriangulated C] (s : Slicing C) {t : ℝ} {U₂ E' Q : C}
    {m₁ : U₂ ⟶ E'} {m₃ : E' ⟶ Q} {δ' : Q ⟶ U₂⟦(1 : ℤ)⟧}
    (hT : Triangle.mk m₁ m₃ δ' ∈ distTriang C) (hU₂ : s.leProp C t U₂)
    (hQ : s.leProp C (t + 1) Q) {E'₁ Q₁ : C} {ι' : E'₁ ⟶ E'}
    (hι' : (s.gtProp C t).IsCoreflection ι') {ιQ : Q₁ ⟶ Q}
    (hιQ : (s.gtProp C t).IsCoreflection ιQ) {κ : E'₁ ⟶ Q₁} (hκ : κ ≫ ιQ = ι' ≫ m₃) :
    s.heartProp C t E'₁ ∧ s.heartProp C t Q₁ ∧ κ ≫ ιQ ≫ δ' = 0 ∧
      (∀ ⦃X : C⦄, s.heartProp C t X → Function.Injective fun g : X ⟶ E'₁ => g ≫ κ) ∧
      ∀ ⦃X : C⦄, s.heartProp C t X → ∀ f : X ⟶ Q₁, f ≫ ιQ ≫ δ' = 0 →
        ∃! g : X ⟶ E'₁, g ≫ κ = f := by
  obtain ⟨hE, hQ₁, hd, hinj, huniq⟩ :=
    s.cutMap_gtProp_of_leProp (by linarith) hT hU₂ hQ hι' hιQ hκ
  exact ⟨hE, hQ₁, hd, fun X hX => hinj hX.1, fun X hX => huniq hX.1⟩

end Triangulated.Slicing

end CategoryTheory
