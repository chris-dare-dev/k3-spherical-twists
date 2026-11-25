/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ExtensionClosure
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Insertion

/-!
# The cut criterion for cones

Let `U → E → Q →δ U⟦1⟧` be a distinguished triangle in a triangulated category with a slicing,
and fix a real number `t`. Write `U_{≥t} → U → U_{<t}` and `Q_{≥t} → Q → Q_{<t}` for the
`(≥ t, < t)` truncation triangles of the two ends (`Slicing.exists_split_geProp_ltProp`), and

  `d_t : Q_{≥t} → Q →δ U⟦1⟧ → U_{<t}⟦1⟧`

for the *cut composite*. Put `E' = cofib(U_{≥t} → U → E)`. The octahedral axiom places `E'` in a
distinguished triangle `U_{<t} → E' → Q → U_{<t}⟦1⟧` whose last map is `δ` followed by the
truncation (`Pretriangulated.exists_cofib_triangles`). The **cut criterion for cones** says how
the top truncation of `E` is cut out of the two ends:

* **(A)** `E_{≥t} = E ×ʰ_{E'} E'_{≥t}`: the fibre of `E → E' → E'_{<t}` is an extension of
  `E'_{≥t}` by `U_{≥t}` and is the top truncation of `E` (`Slicing.exists_geProp_pullback`); and
  the induced map `κ : E'_{≥t} → Q_{≥t}` represents the kernel of `d_t ∘ −` on objects of phases
  at least `t`: composition with `κ` is injective on maps from such an object, with image the
  maps killed by `d_t` (`Slicing.cutMap_injective`, `Slicing.exists_comp_cutMap_iff`).
* **(B)** The triangle has a compatible truncation `U_{≥t} → E_{≥t} → Q_{≥t} → U_{≥t}⟦1⟧` (a
  distinguished triangle mapping to `U → E → Q → U⟦1⟧` by the three truncation maps) exactly
  when `κ` is an isomorphism, exactly when `d_t = 0` (`Slicing.isIso_cutMap_iff`,
  `Slicing.cut_criterion`). The lift `Q_{≥t} → U_{≥t}⟦1⟧` of `Q_{≥t} → Q → U⟦1⟧` is then unique
  (`Slicing.existsUnique_cut_lift_iff`), since `Hom(Q_{≥t}, U_{<t}) = 0`. If `U` has no phase
  below `t`, the criterion always holds (`Slicing.exists_truncation_triangle_of_geProp`).
* **(C)** If `Q` has no phase above `θ`, then `E'_{≥θ}` and `Q_{≥θ}` are semistable of phase
  `θ`, and `κ` is the largest monomorphism into `Q_{≥θ}` in the slice `P(θ)` killed by `d_θ`: it
  is a monomorphism there, it is killed by `d_θ`, and every map from `P(θ)` killed by `d_θ`
  factors uniquely through it (`Slicing.cutMap_top_phase`).

Everything holds for an arbitrary slicing on a triangulated category; nothing uses a charge,
local finiteness or an enhancement. The truncation triangles of `U` and `Q` and the cofibre
`E'` are determined up to non-unique isomorphism, so the statements take them as hypotheses
(any choice) or produce them existentially; the truncations of `Q`, `E` and `E'` enter only
through their coreflection property (`ObjectProperty.IsCoreflection`), which pins them down up
to unique isomorphism over the object.

The criterion is the rectifiability condition of Bapat, Deopurkar and Licata
(arXiv:2011.07908, Appendix A) for one triangle, stated for an arbitrary slicing (Bridgeland,
arXiv:math/0212237, §3).

## Main results

* `CategoryTheory.Pretriangulated.exists_cofib_triangles`: the quotient `E'` by the top part.
* `CategoryTheory.Triangulated.Slicing.exists_geProp_pullback`: (A), the homotopy pullback.
* `CategoryTheory.Triangulated.Slicing.cutMap_injective`,
  `CategoryTheory.Triangulated.Slicing.exists_comp_cutMap_iff`: (A), the kernel of `d_t ∘ −`.
* `CategoryTheory.Triangulated.Slicing.isIso_cutMap_iff`,
  `CategoryTheory.Triangulated.Slicing.cut_criterion`,
  `CategoryTheory.Triangulated.Slicing.existsUnique_cut_lift_iff`,
  `CategoryTheory.Triangulated.Slicing.exists_truncation_triangle_of_geProp`: (B).
* `CategoryTheory.Triangulated.Slicing.cutMap_top_phase`: (C).

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

namespace Pretriangulated

/-- **The quotient by the top part of the first term.** Let `U → E → Q →δ U⟦1⟧` and
`U₁ → U → U₂ → U₁⟦1⟧` be distinguished. The cofibre `E'` of the composite `U₁ → U → E` sits in a
distinguished triangle `U₂ → E' → Q → U₂⟦1⟧` whose last map is `δ` followed by `U → U₂`; the
maps commute with those of the two given triangles. This is the octahedron of the composable
pair `U₁ → U → E`. -/
theorem exists_cofib_triangles [IsTriangulated C] {U E Q U₁ U₂ : C} {u : U ⟶ E} {e : E ⟶ Q}
    {δ : Q ⟶ U⟦(1 : ℤ)⟧} (hT : Triangle.mk u e δ ∈ distTriang C) {ιU : U₁ ⟶ U}
    {πU : U ⟶ U₂} {εU : U₂ ⟶ U₁⟦(1 : ℤ)⟧} (hU : Triangle.mk ιU πU εU ∈ distTriang C) :
    ∃ (E' : C) (p : E ⟶ E') (w : E' ⟶ U₁⟦(1 : ℤ)⟧) (m₁ : U₂ ⟶ E') (m₃ : E' ⟶ Q),
      Triangle.mk (ιU ≫ u) p w ∈ distTriang C ∧
        Triangle.mk m₁ m₃ (δ ≫ πU⟦(1 : ℤ)⟧') ∈ distTriang C ∧
        πU ≫ m₁ = u ≫ p ∧ m₁ ≫ w = εU ∧ p ≫ m₃ = e ∧ w ≫ ιU⟦(1 : ℤ)⟧' = m₃ ≫ δ := by
  obtain ⟨E', p, w, hE'⟩ := distinguished_cocone_triangle (ιU ≫ u)
  let o := Triangulated.someOctahedron rfl hU hT hE'
  exact ⟨E', p, w, o.m₁, o.m₃, hE', o.mem, o.comm₁, o.comm₂, o.comm₃, o.comm₄⟩

end Pretriangulated

namespace Triangulated.Slicing

/-! ### (A) The top truncation as a homotopy pullback -/

/-- **Cut criterion for cones, (A): the homotopy pullback.** Let `U₁ → E → E' →w U₁⟦1⟧` be
distinguished with `U₁` of phases at least `t` (in the criterion, `U₁ = U_{≥t}` and
`E' = cofib(U_{≥t} → E)`), and let `E'₁ → E' → E'₂` be the `(≥ t, < t)` truncation of `E'`. The
fibre `E₁` of `E → E' → E'₂` sits in distinguished triangles `U₁ → E₁ → E'₁` (an extension of
`E'_{≥t}` by `U₁`, whose last map is `E'₁ → E' → U₁⟦1⟧`) and `E₁ → E → E'₂`; it has phases at
least `t` and `E₁ → E` is the coreflection of `E` into `P(≥ t)`. So
`E_{≥t} = E ×ʰ_{E'} E'_{≥t}`. -/
theorem exists_geProp_pullback [IsTriangulated C] (s : Slicing C) {t : ℝ} {U₁ E E' : C}
    {f : U₁ ⟶ E} {p : E ⟶ E'} {w : E' ⟶ U₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f p w ∈ distTriang C)
    (hU₁ : s.geProp C t U₁) {E'₁ E'₂ : C} {ι : E'₁ ⟶ E'} {π : E' ⟶ E'₂}
    {ε : E'₂ ⟶ E'₁⟦(1 : ℤ)⟧} (hT' : Triangle.mk ι π ε ∈ distTriang C)
    (hE'₁ : s.geProp C t E'₁) (hE'₂ : s.ltProp C t E'₂) :
    ∃ (E₁ : C) (f' : U₁ ⟶ E₁) (g' : E₁ ⟶ E'₁) (ιE : E₁ ⟶ E) (w' : E'₂ ⟶ E₁⟦(1 : ℤ)⟧),
      Triangle.mk f' g' (ι ≫ w) ∈ distTriang C ∧ Triangle.mk ιE (p ≫ π) w' ∈ distTriang C ∧
        f' ≫ ιE = f ∧ g' ≫ ι = ιE ≫ p ∧ s.geProp C t E₁ ∧
          (s.geProp C t).IsCoreflection ιE := by
  obtain ⟨E₁, f', g', ιE, w', h₁, h₂, c₁, c₂, -, -⟩ := exists_pullback_triangles hT hT'
  have hE₁ : s.geProp C t E₁ := s.geProp_ext₂ h₁ hU₁ hE'₁
  exact ⟨E₁, f', g', ιE, w', h₁, h₂, c₁, c₂, hE₁, s.isCoreflection_geProp_of_top h₂ hE₁ hE'₂⟩

/-! ### (A) The kernel of the cut composite -/

section Kernel

variable (s : Slicing C) {t : ℝ} {U₂ E' Q : C} {m₁ : U₂ ⟶ E'} {m₃ : E' ⟶ Q}
  {δ' : Q ⟶ U₂⟦(1 : ℤ)⟧} {E'₁ Q₁ : C} {ι' : E'₁ ⟶ E'} {ιQ : Q₁ ⟶ Q} {κ : E'₁ ⟶ Q₁}

/-- **Cut criterion for cones, (A): `κ` is injective on `P(≥ t)`.** Let `U₂ → E' → Q →δ' U₂⟦1⟧`
be distinguished with `U₂` of phases below `t` (in the criterion, `U₂ = U_{<t}` and `δ'` is `δ`
followed by the truncation), let `ι' : E'₁ → E'` and `ιQ : Q₁ → Q` be coreflections into
`P(≥ t)`, and let `κ : E'₁ → Q₁` lie over `E' → Q`. For `X` of phases at least `t`, composition
with `κ` is injective on `Hom(X, E'₁)`. -/
theorem cutMap_injective (hT : Triangle.mk m₁ m₃ δ' ∈ distTriang C) (hU₂ : s.ltProp C t U₂)
    (hι' : (s.geProp C t).IsCoreflection ι') (hκ : κ ≫ ιQ = ι' ≫ m₃) {X : C}
    (hX : s.geProp C t X) : Function.Injective fun g : X ⟶ E'₁ => g ≫ κ := by
  intro g₁ g₂ h
  simp only at h
  have hx : ((g₁ - g₂) ≫ ι') ≫ m₃ = 0 := by
    rw [Category.assoc, ← hκ, Preadditive.sub_comp, ← Category.assoc, h, Category.assoc,
      sub_self]
  obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ _ hT _ hx
  have hy0 : y = 0 := s.hom_eq_zero_of_geProp_ltProp hX hU₂ y
  rw [hy0, zero_comp, Preadditive.sub_comp, sub_eq_zero] at hy
  exact hι'.hom_ext hX hy

/-- **Cut criterion for cones, (A): `κ` represents `ker(d ∘ −)` on `P(≥ t)`.** In the setting
of `Slicing.cutMap_injective`, a map `f : X → Q₁` from an object of phases at least `t` factors
through `κ` exactly when it is killed by the cut composite `d = ιQ ≫ δ'`. -/
theorem exists_comp_cutMap_iff (hT : Triangle.mk m₁ m₃ δ' ∈ distTriang C)
    (hι' : (s.geProp C t).IsCoreflection ι') (hιQ : (s.geProp C t).IsCoreflection ιQ)
    (hκ : κ ≫ ιQ = ι' ≫ m₃) {X : C} (hX : s.geProp C t X) (f : X ⟶ Q₁) :
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

/-- **Cut criterion for cones, (B): `κ` is an isomorphism exactly when `d = 0`.** In the setting
of `Slicing.cutMap_injective`, the map `κ : E'₁ → Q₁` is an isomorphism if and only if the cut
composite `ιQ ≫ δ'` vanishes. -/
theorem isIso_cutMap_iff (hT : Triangle.mk m₁ m₃ δ' ∈ distTriang C) (hU₂ : s.ltProp C t U₂)
    (hι' : (s.geProp C t).IsCoreflection ι') (hιQ : (s.geProp C t).IsCoreflection ιQ)
    (hκ : κ ≫ ιQ = ι' ≫ m₃) : IsIso κ ↔ ιQ ≫ δ' = 0 := by
  constructor
  · intro _
    have := (s.exists_comp_cutMap_iff hT hι' hιQ hκ hιQ.prop (𝟙 Q₁)).1 ⟨inv κ, by simp⟩
    simpa using this
  · intro hd
    obtain ⟨g, hg⟩ := (s.exists_comp_cutMap_iff hT hι' hιQ hκ hιQ.prop (𝟙 Q₁)).2
      (by simpa using hd)
    refine ⟨g, s.cutMap_injective hT hU₂ hι' hκ hι'.prop ?_, hg⟩
    simp only [Category.assoc, hg, Category.comp_id, Category.id_comp]

end Kernel

/-! ### (B) The cut criterion -/

/-- **Uniqueness of the lift.** Let `U₁ → U → U₂ → U₁⟦1⟧` be distinguished with `U₂` of phases
below `t`. Two maps `Q₁ → U₁⟦1⟧` from an object of phases at least `t` that agree after
`U₁⟦1⟧ → U⟦1⟧` are equal, since `Hom(Q₁, U₂) = 0`. -/
theorem cut_lift_unique (s : Slicing C) {t : ℝ} {U U₁ U₂ : C} {ιU : U₁ ⟶ U} {πU : U ⟶ U₂}
    {εU : U₂ ⟶ U₁⟦(1 : ℤ)⟧} (hU : Triangle.mk ιU πU εU ∈ distTriang C)
    (hU₂ : s.ltProp C t U₂) {Q₁ : C} (hQ₁ : s.geProp C t Q₁) {c c' : Q₁ ⟶ U₁⟦(1 : ℤ)⟧}
    (h : c ≫ ιU⟦(1 : ℤ)⟧' = c' ≫ ιU⟦(1 : ℤ)⟧') : c = c' := by
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ hU (c - c')
    (show (c - c') ≫ ιU⟦(1 : ℤ)⟧' = 0 by rw [Preadditive.sub_comp, h, sub_self])
  have hg0 : g = 0 := s.hom_eq_zero_of_geProp_ltProp hQ₁ hU₂ g
  rw [hg0, zero_comp, sub_eq_zero] at hg
  exact hg

/-- The lift exists when the cut composite vanishes. -/
private theorem exists_cut_lift {U U₁ U₂ : C} {ιU : U₁ ⟶ U} {πU : U ⟶ U₂}
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

/-- **The cut criterion for cones, (B).** Let `U → E → Q →δ U⟦1⟧` be distinguished, let
`U₁ → U → U₂ → U₁⟦1⟧` be the `(≥ t, < t)` truncation of `U`, and let `ιQ : Q₁ → Q` and
`ιE : E₁ → E` be the coreflections of `Q` and `E` into `P(≥ t)`. The following are equivalent:

1. the cut composite `d_t : Q₁ → Q → U⟦1⟧ → U₂⟦1⟧` vanishes;
2. `Q₁ → Q → U⟦1⟧` lifts to `U₁⟦1⟧` (the lift is unique: `Slicing.cut_lift_unique`);
3. the triangle truncates compatibly: there is a distinguished triangle
   `U₁ → E₁ → Q₁ → U₁⟦1⟧` whose three maps commute with the truncation maps and the maps of
   `U → E → Q → U⟦1⟧`.

In (3) the first two maps are the unique factorizations through `ιE` and `ιQ`, and the third is
the unique lift of (2). -/
theorem cut_criterion [IsTriangulated C] (s : Slicing C) {t : ℝ} {U E Q : C} {u : U ⟶ E}
    {e : E ⟶ Q} {δ : Q ⟶ U⟦(1 : ℤ)⟧} (hT : Triangle.mk u e δ ∈ distTriang C)
    {U₁ U₂ : C} {ιU : U₁ ⟶ U} {πU : U ⟶ U₂} {εU : U₂ ⟶ U₁⟦(1 : ℤ)⟧}
    (hU : Triangle.mk ιU πU εU ∈ distTriang C) (hU₁ : s.geProp C t U₁)
    (hU₂ : s.ltProp C t U₂) {Q₁ : C} {ιQ : Q₁ ⟶ Q} (hιQ : (s.geProp C t).IsCoreflection ιQ)
    {E₁ : C} {ιE : E₁ ⟶ E} (hιE : (s.geProp C t).IsCoreflection ιE) :
    List.TFAE [ιQ ≫ δ ≫ πU⟦(1 : ℤ)⟧' = 0,
      ∃ c : Q₁ ⟶ U₁⟦(1 : ℤ)⟧, c ≫ ιU⟦(1 : ℤ)⟧' = ιQ ≫ δ,
      ∃ (a : U₁ ⟶ E₁) (b : E₁ ⟶ Q₁) (c : Q₁ ⟶ U₁⟦(1 : ℤ)⟧),
        Triangle.mk a b c ∈ distTriang C ∧ a ≫ ιE = ιU ≫ u ∧ b ≫ ιQ = ιE ≫ e ∧
          c ≫ ιU⟦(1 : ℤ)⟧' = ιQ ≫ δ] := by
  tfae_have 1 → 3 := by
    intro hd
    obtain ⟨E', p, w, m₁, m₃, hE', hM, -, -, hpm, hwm⟩ := exists_cofib_triangles hT hU
    obtain ⟨E'₁, E'₂, ι', π', ε', hS, h₁, h₂⟩ := s.exists_split_geProp_ltProp t E'
    have hι' := s.isCoreflection_geProp_of_top hS h₁ h₂
    let κ : E'₁ ⟶ Q₁ := hιQ.lift h₁ (ι' ≫ m₃)
    have hκ : κ ≫ ιQ = ι' ≫ m₃ := hιQ.lift_comp h₁ _
    have : IsIso κ := (s.isIso_cutMap_iff hM hU₂ hι' hιQ hκ).2 (by simpa using hd)
    obtain ⟨B, f', g', ιB, w', hB₁, -, cf, cg, -, hιB⟩ := s.exists_geProp_pullback hE' hU₁ hS h₁ h₂
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

/-- **The lift is unique.** In the setting of `Slicing.cut_criterion`, `Q₁ → Q → U⟦1⟧` has a
unique lift to `U₁⟦1⟧` exactly when the cut composite vanishes. -/
theorem existsUnique_cut_lift_iff (s : Slicing C) {t : ℝ} {U Q : C} {δ : Q ⟶ U⟦(1 : ℤ)⟧}
    {U₁ U₂ : C} {ιU : U₁ ⟶ U} {πU : U ⟶ U₂} {εU : U₂ ⟶ U₁⟦(1 : ℤ)⟧}
    (hU : Triangle.mk ιU πU εU ∈ distTriang C) (hU₂ : s.ltProp C t U₂) {Q₁ : C}
    {ιQ : Q₁ ⟶ Q} (hQ₁ : s.geProp C t Q₁) :
    (∃! c : Q₁ ⟶ U₁⟦(1 : ℤ)⟧, c ≫ ιU⟦(1 : ℤ)⟧' = ιQ ≫ δ) ↔ ιQ ≫ δ ≫ πU⟦(1 : ℤ)⟧' = 0 := by
  constructor
  · rintro ⟨c, hc, -⟩
    have h0 : ιU ≫ πU = 0 := comp_distTriang_mor_zero₁₂ _ hU
    rw [← Category.assoc, ← hc, Category.assoc, ← Functor.map_comp, h0, Functor.map_zero,
      comp_zero]
  · intro hd
    obtain ⟨c, hc⟩ := exists_cut_lift hU (ιQ ≫ δ) (by simpa using hd)
    exact ⟨c, hc, fun c' hc' => s.cut_lift_unique hU hU₂ hQ₁ (hc'.trans hc.symm)⟩

/-- **No cut on the first term.** If `U` has no phase below `t`, every distinguished triangle
`U → E → Q →δ U⟦1⟧` truncates compatibly at `t`: for the coreflections `ιQ : Q₁ → Q` and
`ιE : E₁ → E` into `P(≥ t)` there is a distinguished triangle `U → E₁ → Q₁ → U⟦1⟧` whose maps lie
over `U → E`, over `E → Q`, and whose last map is `ιQ ≫ δ`. -/
theorem exists_truncation_triangle_of_geProp [IsTriangulated C] (s : Slicing C) {t : ℝ}
    {U E Q : C} {u : U ⟶ E} {e : E ⟶ Q} {δ : Q ⟶ U⟦(1 : ℤ)⟧}
    (hT : Triangle.mk u e δ ∈ distTriang C) (hU : s.geProp C t U) {Q₁ : C} {ιQ : Q₁ ⟶ Q}
    (hιQ : (s.geProp C t).IsCoreflection ιQ) {E₁ : C} {ιE : E₁ ⟶ E}
    (hιE : (s.geProp C t).IsCoreflection ιE) :
    ∃ (a : U ⟶ E₁) (b : E₁ ⟶ Q₁),
      Triangle.mk a b (ιQ ≫ δ) ∈ distTriang C ∧ a ≫ ιE = u ∧ b ≫ ιQ = ιE ≫ e := by
  have h₀ : s.ltProp C t (0 : C) := s.ltProp_of_isZero C (isZero_zero C) t
  obtain ⟨a, b, c, hA, ha, hb, hc⟩ := ((s.cut_criterion hT (contractible_distinguished U) hU h₀
    hιQ hιE).out 1 3).1 (by simp)
  have hc' : c = ιQ ≫ δ := by simpa using hc
  subst hc'
  exact ⟨a, b, hA, by simpa using ha, hb⟩

/-! ### (C) The top phase -/

/-- The coreflection into `P(≥ θ)` of an object with no phase above `θ` is semistable of
phase `θ`. -/
theorem semistable_of_isCoreflection_geProp [IsTriangulated C] (s : Slicing C) {θ : ℝ}
    {D R : C} {ι : D ⟶ R} (hι : (s.geProp C θ).IsCoreflection ι) (hR : s.leProp C θ R) :
    s.P θ D := by
  refine s.semistable_of_geProp_of_leProp hι.prop (s.leProp_iff_hom_eq_zero.2 ?_)
  intro X hX f
  refine hι.hom_ext (s.geProp_of_gtProp C _ hX) ?_
  rw [zero_comp]
  exact s.hom_eq_zero_of_gtProp_leProp hX hR _

/-- **Cut criterion for cones, (C): the top phase.** In the setting of
`Slicing.cutMap_injective` at a real number `θ`, suppose `Q` has no phase above `θ` (in the
criterion, `θ` is the greatest phase occurring in the two ends). Then `E'₁ = E'_{≥θ}` and
`Q₁ = Q_{≥θ}` are semistable of phase `θ`, and `κ : E'₁ → Q₁` is the largest monomorphism into
`Q₁` in the slice `P(θ)` killed by `d_θ = ιQ ≫ δ'`: composition with `κ` is injective on maps
from `P(θ)`, `κ` is killed by `d_θ`, and every map from `P(θ)` to `Q₁` killed by `d_θ` factors
uniquely through `κ`. -/
theorem cutMap_top_phase [IsTriangulated C] (s : Slicing C) {θ : ℝ} {U₂ E' Q : C}
    {m₁ : U₂ ⟶ E'} {m₃ : E' ⟶ Q} {δ' : Q ⟶ U₂⟦(1 : ℤ)⟧}
    (hT : Triangle.mk m₁ m₃ δ' ∈ distTriang C) (hU₂ : s.ltProp C θ U₂) (hQ : s.leProp C θ Q)
    {E'₁ Q₁ : C} {ι' : E'₁ ⟶ E'} (hι' : (s.geProp C θ).IsCoreflection ι') {ιQ : Q₁ ⟶ Q}
    (hιQ : (s.geProp C θ).IsCoreflection ιQ) {κ : E'₁ ⟶ Q₁} (hκ : κ ≫ ιQ = ι' ≫ m₃) :
    s.P θ E'₁ ∧ s.P θ Q₁ ∧ κ ≫ ιQ ≫ δ' = 0 ∧
      (∀ ⦃X : C⦄, s.P θ X → Function.Injective fun g : X ⟶ E'₁ => g ≫ κ) ∧
      ∀ ⦃X : C⦄, s.P θ X → ∀ f : X ⟶ Q₁, f ≫ ιQ ≫ δ' = 0 → ∃! g : X ⟶ E'₁, g ≫ κ = f := by
  have hE' : s.leProp C θ E' := s.leProp_ext₂ hT (s.leProp_of_ltProp C _ hU₂) hQ
  refine ⟨s.semistable_of_isCoreflection_geProp hι' hE',
    s.semistable_of_isCoreflection_geProp hιQ hQ,
    (s.exists_comp_cutMap_iff hT hι' hιQ hκ hι'.prop κ).1 ⟨𝟙 _, Category.id_comp _⟩,
    fun X hX => s.cutMap_injective hT hU₂ hι' hκ (s.geProp_of_semistable C hX),
    fun X hX f hf => ?_⟩
  obtain ⟨g, hg⟩ := (s.exists_comp_cutMap_iff hT hι' hιQ hκ (s.geProp_of_semistable C hX) f).2 hf
  exact ⟨g, hg, fun g' hg' =>
    s.cutMap_injective hT hU₂ hι' hκ (s.geProp_of_semistable C hX) (hg'.trans hg.symm)⟩

end Triangulated.Slicing

end CategoryTheory
