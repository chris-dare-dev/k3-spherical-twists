/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ConeHN
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The divisibility obstruction for a cone on a semistable object

Let `P` be semistable of phase `φ` for a slicing on a `k`-linear triangulated category, with only
scalar endomorphisms, and let `P → E → Q →c P⟦1⟧` be distinguished. For a spherical object `S`
with `RHom(S, P) = W` concentrated in degree `0` and `r = dim W`, the twist triangle
`S ⊗ W → P → T_S P` rotates to this shape with `E = T_S P` and `Q = (S⟦1⟧)^{⊕ r}`
(Seidel–Thomas, arXiv:math/0001043, §2). Let `G` be the phase-`φ` HN factor of `E` (zero if
`φ` is not a phase of `E`) and `V = Q_{≥φ}`. The cut criterion for cones at `φ` applies with
vanishing cut composite, since `P` has no phase below `φ`: the top truncation of `E` is an
extension `P → E_{≥φ} → V →c_V P⟦1⟧` with `c_V` the restriction of `c`
(`Slicing.exists_truncation_triangle_of_geProp`). Applying `Hom(−, P)` to it gives the
**divisibility obstruction** (`Slicing.divisibility_obstruction_top`):

* if `c_V = 0`, then `P` is a direct summand of `G`;
* if `c_V ≠ 0`, then precomposition is a `k`-linear isomorphism `Hom(V, P) ≅ Hom(G, P)`; for
  `Q = S'^{⊕ r}` this gives `dim Hom(G, P) = r · dim Hom(S'_{≥φ}, P)`
  (`Slicing.divisibility_obstruction_top_finrank`).

So either `P` splits off the phase-`φ` quotient, or `r` divides `dim Hom(G, P)`. Dually, for a
distinguished triangle `Q → E → P →c Q⟦1⟧` (for a spherical `S` in a 2-Calabi–Yau category, the
inverse twist triangle `S⟦1⟧ ⊗ W → T_S^{-1} P → P` has this shape), with `L = Q_{≤φ}` and `G` the
first quotient of phase `φ` of `E_{≤φ}`: either `P` is a direct summand of `G`, or
`Hom(P, L) ≅ Hom(P, G)` and `dim Hom(P, G) = r · dim Hom(P, S'_{≤φ})`
(`Slicing.divisibility_obstruction_bottom`, `Slicing.divisibility_obstruction_bottom_finrank`).

## Implementation notes

Twist functors are not available in Mathlib, so the statements take the twist triangle as a
distinguished triangle of the displayed shape. Its connecting map need not be an evaluation map,
`S'` need not be a shift of a spherical object, and no hypothesis on `RHom(S, P)` is used: the
obstruction holds for every such triangle. The truncations are hypotheses (any choice): the
top truncations through their coreflection property, the bottom ones through distinguished
triangles. The dimension count assumes that the relevant Hom spaces are finite-dimensional;
the linear isomorphisms do not.

## Tags

slicing, stability condition, spherical twist, divisibility, cone, Harder–Narasimhan filtration
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Pretriangulated

/-- **A retract is a direct summand.** In a pretriangulated category, if `a : P → G` has a
retraction, then `G ≅ P ⊞ G'` for some `G'`, compatibly with `a`. -/
theorem exists_iso_biprod_of_retraction {P G : C} {a : P ⟶ G} {b : G ⟶ P} (h : a ≫ b = 𝟙 P) :
    ∃ (G' : C) (e : G ≅ P ⊞ G'), a ≫ e.hom = biprod.inl := by
  obtain ⟨G', g, c, hT⟩ := distinguished_cocone_triangle a
  have : Mono a := (IsSplitMono.mk' ⟨b, h⟩).mono
  obtain ⟨e, he, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT
    (Triangle.mor₃_eq_zero_of_mono₁ _ hT this)
  exact ⟨G', e, he⟩

end Pretriangulated

namespace Linear

variable (k : Type w) [Semiring k] [Linear k C]

/-- Maps out of a finite biproduct are families of maps out of the summands. -/
def homBiproductLinearEquiv {ι : Type*} (f : ι → C)
    [HasBiproduct f] (X : C) : (⨁ f ⟶ X) ≃ₗ[k] ∀ i, f i ⟶ X where
  toFun g i := biproduct.ι f i ≫ g
  invFun h := biproduct.desc h
  map_add' g g' := by ext i; simp
  map_smul' a g := by ext i; simp
  left_inv g := by ext i; simp
  right_inv h := by ext i; simp

/-- Maps into a finite biproduct are families of maps into the summands. -/
def biproductHomLinearEquiv {ι : Type*} (f : ι → C)
    [HasBiproduct f] (X : C) : (X ⟶ ⨁ f) ≃ₗ[k] ∀ i, X ⟶ f i where
  toFun g i := g ≫ biproduct.π f i
  invFun h := biproduct.lift h
  map_add' g g' := by ext i; simp
  map_smul' a g := by ext i; simp
  left_inv g := by ext i; simp
  right_inv h := by ext i; simp

end Linear

namespace Triangulated.Slicing

/-! ### Truncations of finite biproducts -/

section Biproduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Top truncation of a finite biproduct.** If each `ιᵢ : Vᵢ → Sᵢ` is the coreflection of
`Sᵢ` into `P(≥ t)`, then `⨁ ιᵢ` is the coreflection of `⨁ Sᵢ`. -/
theorem isCoreflection_biproduct_map [IsTriangulated C] (s : Slicing C) {t : ℝ} {V S : ι → C}
    {f : ∀ i, V i ⟶ S i} (hf : ∀ i, (s.geProp C t).IsCoreflection (f i)) :
    (s.geProp C t).IsCoreflection (biproduct.map f) := by
  refine ⟨s.geProp_iff_hom_eq_zero.2 fun Y hY g => biproduct.hom_ext' _ _ fun i => ?_,
    fun X hX => ⟨fun g g' h => biproduct.hom_ext _ _ fun i => ?_, fun g => ?_⟩⟩
  · rw [comp_zero]
    exact s.geProp_iff_hom_eq_zero.1 (hf i).prop hY _
  · refine (hf i).hom_ext hX ?_
    have := congrArg (· ≫ biproduct.π S i) h
    simpa using this
  · refine ⟨biproduct.lift fun i => (hf i).lift hX (g ≫ biproduct.π S i), ?_⟩
    ext i
    simp

omit [DecidableEq ι] in
/-- **Bottom truncation of a finite biproduct.** Let `Q₁ → ⨁ Sᵢ → L → Q₁⟦1⟧` be distinguished with
`Q₁` of phases above `t` and `L` of phases at most `t`, and let `Uᵢ → Sᵢ → Lᵢ → Uᵢ⟦1⟧` be
distinguished with the same phase bounds. Then `L ≅ ⨁ Lᵢ` over `⨁ Sᵢ`. -/
theorem exists_iso_biproduct_of_leProp [IsTriangulated C] (s : Slicing C) {t : ℝ}
    {S U L₀ : ι → C} {u : ∀ i, U i ⟶ S i} {π₀ : ∀ i, S i ⟶ L₀ i}
    {ε₀ : ∀ i, L₀ i ⟶ (U i)⟦(1 : ℤ)⟧} (h₀ : ∀ i, Triangle.mk (u i) (π₀ i) (ε₀ i) ∈ distTriang C)
    (hU : ∀ i, s.gtProp C t (U i)) (hL₀ : ∀ i, s.leProp C t (L₀ i)) {Q₁ L : C}
    {ιQ : Q₁ ⟶ ⨁ S} {π : ⨁ S ⟶ L} {ε : L ⟶ Q₁⟦(1 : ℤ)⟧}
    (hT : Triangle.mk ιQ π ε ∈ distTriang C) (hQ₁ : s.gtProp C t Q₁)
    (hL : s.leProp C t L) : ∃ e : L ≅ ⨁ L₀, π ≫ e.hom = biproduct.map π₀ := by
  have hLsum : s.leProp C t (⨁ L₀) := s.leProp_iff_hom_eq_zero.2 fun X hX g =>
    biproduct.hom_ext _ _ fun i => by
      rw [zero_comp]
      exact s.leProp_iff_hom_eq_zero.1 (hL₀ i) hX _
  have hbij : ∀ {Y : C}, s.leProp C t Y → Function.Bijective fun g : L ⟶ Y => π ≫ g :=
    fun hY => s.comp_bijective_of_bottom hT hQ₁ hY
  have hbij₀ : ∀ i {Y : C}, s.leProp C t Y → Function.Bijective fun g : L₀ i ⟶ Y => π₀ i ≫ g :=
    fun i _ hY => s.comp_bijective_of_bottom (h₀ i) (hU i) hY
  obtain ⟨x, hx⟩ := (hbij hLsum).2 (biproduct.map π₀)
  choose y hy using fun i => (hbij₀ i hL).2 (biproduct.ι S i ≫ π)
  simp only at hx hy
  have hmap : biproduct.map π₀ ≫ biproduct.desc y = π := by
    ext i
    simp [hy]
  have hinj : ∀ {z z' : ⨁ L₀ ⟶ ⨁ L₀}, biproduct.map π₀ ≫ z = biproduct.map π₀ ≫ z' →
      z = z' := by
    intro z z' h
    refine biproduct.hom_ext' _ _ fun i => (hbij₀ i hLsum).1 ?_
    have := congrArg (biproduct.ι S i ≫ ·) h
    simpa using this
  refine ⟨⟨x, biproduct.desc y, (hbij hL).1 ?_, hinj ?_⟩, hx⟩
  · simp only [reassoc_of% hx, hmap, Category.comp_id]
  · simp only [reassoc_of% hmap, hx, Category.comp_id]

end Biproduct

/-! ### The divisibility obstruction -/

variable {k : Type w} [Field k] [Linear k C]

/-- **The divisibility obstruction, top side.** Let `P` be semistable of phase `φ` with only
scalar endomorphisms, `P →i E →p Q →c P⟦1⟧` distinguished, `ιV : V → Q` and `ιE : E₁ → E` the
coreflections into `P(≥ φ)`, and `K → E₁ → G → K⟦1⟧` distinguished with `K` of phases above `φ`
(so `G` is the phase-`φ` HN factor of `E`). Write `c_V = ιV ≫ c`.

* If `c_V = 0`, then `P` is a direct summand of `G`.
* If `c_V ≠ 0`, then `Hom(V, P)` and `Hom(G, P)` are isomorphic `k`-vector spaces: both are
  identified with `Hom(E₁, P)` by precomposition. -/
theorem divisibility_obstruction_top [IsTriangulated C] (s : Slicing C) {φ : ℝ} {P E Q : C}
    (hP : s.P φ P) (hEnd : ∀ f : P ⟶ P, ∃ a : k, f = a • 𝟙 P) {i : P ⟶ E} {p : E ⟶ Q}
    {c : Q ⟶ P⟦(1 : ℤ)⟧} (hT : Triangle.mk i p c ∈ distTriang C) {V : C} {ιV : V ⟶ Q}
    (hιV : (s.geProp C φ).IsCoreflection ιV) {E₁ : C} {ιE : E₁ ⟶ E}
    (hιE : (s.geProp C φ).IsCoreflection ιE) {K G : C} {j : K ⟶ E₁} {π : E₁ ⟶ G}
    {ε : G ⟶ K⟦(1 : ℤ)⟧} (hG : Triangle.mk j π ε ∈ distTriang C) (hK : s.gtProp C φ K) :
    (ιV ≫ c = 0 → ∃ (G' : C), Nonempty (G ≅ P ⊞ G')) ∧
      (ιV ≫ c ≠ 0 → Nonempty ((V ⟶ P) ≃ₗ[k] (G ⟶ P))) := by
  -- The compatible truncation `P → E₁ → V → P⟦1⟧`.
  obtain ⟨a, b, hA, -, -⟩ :=
    s.exists_truncation_triangle_of_geProp hT (s.geProp_of_semistable C hP) hιV hιE
  -- Maps from `G` to `P` are maps from `E₁` to `P`.
  have hPle : s.leProp C φ P := s.leProp_of_semistable C hP le_rfl
  have hπ : Function.Bijective fun g : G ⟶ P => π ≫ g := s.comp_bijective_of_bottom hG hK hPle
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · -- `c_V = 0`: the truncation splits and `P` splits off `G`.
    obtain ⟨e, he, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hA hc
    obtain ⟨r, hr⟩ := hπ.2 (e.hom ≫ biprod.fst)
    simp only at hr
    refine (exists_iso_biprod_of_retraction (a := a ≫ π) (b := r) ?_).imp fun G' h => ?_
    · rw [Category.assoc, hr, ← Category.assoc]
      exact (congrArg (· ≫ biprod.fst) he).trans (by simp)
    · obtain ⟨e', -⟩ := h
      exact ⟨e'⟩
  · -- `c_V ≠ 0`: precomposition with `E₁ → V` is bijective.
    have hb : Function.Bijective fun h : V ⟶ P => b ≫ h := by
      refine ⟨fun h₁ h₂ h => ?_, fun g => ?_⟩
      · simp only at h
        obtain ⟨y, hy⟩ := Triangle.yoneda_exact₃ _ hA (h₁ - h₂)
          (show b ≫ (h₁ - h₂) = 0 by rw [Preadditive.comp_sub, h, sub_self])
        have hy0 : y = 0 := s.hom_vanishing (φ + 1) φ _ _ (by linarith) (s.shift C φ P hP) hP y
        rw [hy0, comp_zero, sub_eq_zero] at hy
        exact hy
      · obtain ⟨x, hx⟩ := hEnd (a ≫ g)
        have hx0 : x = 0 := by
          by_contra hx0
          have : Mono a := (IsSplitMono.mk' ⟨x⁻¹ • g, by
            rw [Linear.comp_smul, hx, smul_smul, inv_mul_cancel₀ hx0, one_smul]⟩).mono
          exact hc (Triangle.mor₃_eq_zero_of_mono₁ _ hA this)
        obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ _ hA g
          (show a ≫ g = 0 by rw [hx, hx0, zero_smul])
        exact ⟨h, hh.symm⟩
    exact ⟨(LinearEquiv.ofBijective (Linear.leftComp k P b) hb).trans
      (LinearEquiv.ofBijective (Linear.leftComp k P π) hπ).symm⟩

/-- **The divisibility obstruction, bottom side.** Let `P` be semistable of phase `φ` with only
scalar endomorphisms and `Q →j E →q P →c Q⟦1⟧` distinguished. Let `Q₁ → Q →π L` be the
`(> φ, ≤ φ)` truncation of `Q`, `E₁ → E → E₂` that of `E`, and `G → E₂ → K` distinguished with
`K` of phases below `φ` (so `G` is the first quotient of phase `φ` of `E_{≤φ}`, the phase-`φ`
HN factor of `E`). Write `c_L = c ≫ π⟦1⟧`.

* If `c_L = 0`, then `P` is a direct summand of `G`.
* If `c_L ≠ 0`, then `Hom(P, L)` and `Hom(P, G)` are isomorphic `k`-vector spaces. -/
theorem divisibility_obstruction_bottom [IsTriangulated C] (s : Slicing C) {φ : ℝ} {P E Q : C}
    (hP : s.P φ P) (hEnd : ∀ f : P ⟶ P, ∃ a : k, f = a • 𝟙 P) {j : Q ⟶ E} {q : E ⟶ P}
    {c : P ⟶ Q⟦(1 : ℤ)⟧} (hT : Triangle.mk j q c ∈ distTriang C) {Q₁ L : C} {ιQ : Q₁ ⟶ Q}
    {π : Q ⟶ L} {εQ : L ⟶ Q₁⟦(1 : ℤ)⟧} (hQ : Triangle.mk ιQ π εQ ∈ distTriang C)
    (hQ₁ : s.gtProp C φ Q₁) (hL : s.leProp C φ L) {E₁ E₂ : C} {ιE : E₁ ⟶ E} {ρ : E ⟶ E₂}
    {εE : E₂ ⟶ E₁⟦(1 : ℤ)⟧} (hE : Triangle.mk ιE ρ εE ∈ distTriang C) (hE₁ : s.gtProp C φ E₁)
    (hE₂ : s.leProp C φ E₂) {G K : C} {γ : G ⟶ E₂} {κ : E₂ ⟶ K} {εG : K ⟶ G⟦(1 : ℤ)⟧}
    (hG : Triangle.mk γ κ εG ∈ distTriang C) (hK : s.ltProp C φ K) :
    (c ≫ π⟦(1 : ℤ)⟧' = 0 → ∃ (G' : C), Nonempty (G ≅ P ⊞ G')) ∧
      (c ≫ π⟦(1 : ℤ)⟧' ≠ 0 → Nonempty ((P ⟶ L) ≃ₗ[k] (P ⟶ G))) := by
  -- The quotient `E' = cofib(Q₁ → E)`, an extension of `P` by `L`, is the bottom truncation.
  obtain ⟨E', p, w, m₁, m₃, hE', hM, -, -, hpm, -⟩ := exists_cofib_triangles hT hQ
  have hPle : s.leProp C φ P := s.leProp_of_semistable C hP le_rfl
  have hE'le : s.leProp C φ E' := s.leProp_ext₂ hM hL hPle
  have hQ₁E : s.gtProp C φ Q₁ := hQ₁
  obtain ⟨x, hx⟩ := (s.comp_bijective_of_bottom hE hE₁ hE'le).2 p
  obtain ⟨y, hy⟩ := (s.comp_bijective_of_bottom hE' hQ₁E hE₂).2 ρ
  simp only at hx hy
  have hxy : x ≫ y = 𝟙 E₂ := (s.comp_bijective_of_bottom hE hE₁ hE₂).1
    (show ρ ≫ x ≫ y = ρ ≫ 𝟙 E₂ by rw [reassoc_of% hx, hy, Category.comp_id])
  have hyx : y ≫ x = 𝟙 E' := (s.comp_bijective_of_bottom hE' hQ₁E hE'le).1
    (show p ≫ y ≫ x = p ≫ 𝟙 E' by rw [reassoc_of% hy, hx, Category.comp_id])
  let e : E₂ ≅ E' := ⟨x, y, hxy, hyx⟩
  -- Maps from `P` to `G` are maps from `P` to `E₂`.
  have hγ : Function.Bijective fun g : P ⟶ G => g ≫ γ :=
    s.comp_bijective_of_top hG hK (s.geProp_of_semistable C hP)
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · -- `c_L = 0`: `E' → P` splits and `P` splits off `G`.
    obtain ⟨f, -, hf⟩ := exists_iso_binaryBiproduct_of_distTriang _ hM hc
    obtain ⟨a, ha⟩ := hγ.2 (biprod.inr ≫ f.inv ≫ e.inv)
    simp only at ha
    refine (exists_iso_biprod_of_retraction (a := a) (b := γ ≫ e.hom ≫ m₃) ?_).imp
      fun G' h => ?_
    · rw [reassoc_of% ha]
      have hf' : m₃ = f.hom ≫ biprod.snd := hf
      rw [Iso.inv_hom_id_assoc, hf', Iso.inv_hom_id_assoc]
      exact biprod.inr_snd
    · obtain ⟨e', -⟩ := h
      exact ⟨e'⟩
  · -- `c_L ≠ 0`: composition with `L → E'` is bijective.
    have hm : Function.Bijective fun h : P ⟶ L => h ≫ m₁ := by
      refine ⟨fun h₁ h₂ h => ?_, fun g => ?_⟩
      · simp only at h
        obtain ⟨y', hy'⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hM) (h₁ - h₂)
          (show (h₁ - h₂) ≫ m₁ = 0 by rw [Preadditive.sub_comp, h, sub_self])
        have hy0 : y' = 0 := by
          have hPm : s.P (φ + ((-1 : ℤ) : ℝ)) (P⟦(-1 : ℤ)⟧) := (s.shift_int C φ P (-1)).1 hP
          exact s.hom_vanishing φ _ _ _ (by push_cast; linarith) hP hPm y'
        have hd : h₁ - h₂ = 0 := by
          rw [hy0, zero_comp] at hy'
          exact hy'
        exact sub_eq_zero.mp hd
      · obtain ⟨a, ha⟩ := hEnd (g ≫ m₃)
        have ha0 : a = 0 := by
          by_contra ha0
          have : Epi m₃ := (IsSplitEpi.mk' ⟨a⁻¹ • g, by
            rw [Linear.smul_comp, ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩).epi
          exact hc (Triangle.mor₃_eq_zero_of_epi₂ _ hM this)
        obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ _ hM g
          (show g ≫ m₃ = 0 by rw [ha, ha0, zero_smul])
        exact ⟨h, hh.symm⟩
    exact ⟨((LinearEquiv.ofBijective (Linear.rightComp k P m₁) hm).trans
      (Linear.homCongr k (Iso.refl P) e.symm)).trans
      (LinearEquiv.ofBijective (Linear.rightComp k P γ) hγ).symm⟩

/-! ### The count for a cone on a sum of copies -/

/-- **The divisibility obstruction, top side, with `r` copies.** In
`Slicing.divisibility_obstruction_top` with `Q = S'^{⊕ r}` (for the twist triangle,
`S' = S⟦1⟧`) and the top truncation `S'₁ → S'`: either `P` is a direct summand of the phase-`φ`
HN factor `G` of `E`, or `dim Hom(G, P) = r · dim Hom(S'₁, P)`. -/
theorem divisibility_obstruction_top_finrank [IsTriangulated C] (s : Slicing C) {φ : ℝ}
    {P E S' S'₁ : C} (r : ℕ) (hP : s.P φ P) (hEnd : ∀ f : P ⟶ P, ∃ a : k, f = a • 𝟙 P)
    [Module.Finite k (S'₁ ⟶ P)] {i : P ⟶ E} {p : E ⟶ ⨁ fun _ : Fin r => S'}
    {c : (⨁ fun _ : Fin r => S') ⟶ P⟦(1 : ℤ)⟧} (hT : Triangle.mk i p c ∈ distTriang C)
    {ιS : S'₁ ⟶ S'} (hιS : (s.geProp C φ).IsCoreflection ιS) {E₁ : C} {ιE : E₁ ⟶ E}
    (hιE : (s.geProp C φ).IsCoreflection ιE) {K G : C} {j : K ⟶ E₁} {π : E₁ ⟶ G}
    {ε : G ⟶ K⟦(1 : ℤ)⟧} (hG : Triangle.mk j π ε ∈ distTriang C) (hK : s.gtProp C φ K) :
    (∃ (G' : C), Nonempty (G ≅ P ⊞ G')) ∨
      Module.finrank k (G ⟶ P) = r * Module.finrank k (S'₁ ⟶ P) := by
  have hιV := s.isCoreflection_biproduct_map (t := φ) (f := fun _ : Fin r => ιS) fun _ => hιS
  obtain ⟨h₁, h₂⟩ := s.divisibility_obstruction_top (k := k) hP hEnd hT hιV hιE hG hK
  by_cases hc : biproduct.map (fun _ : Fin r => ιS) ≫ c = 0
  · exact Or.inl (h₁ hc)
  · obtain ⟨e⟩ := h₂ hc
    right
    rw [← e.finrank_eq, (Linear.homBiproductLinearEquiv k (fun _ : Fin r => S'₁) P).finrank_eq,
      Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]

/-- **The divisibility obstruction, bottom side, with `r` copies.** In
`Slicing.divisibility_obstruction_bottom` with `Q = S'^{⊕ r}` (for the inverse twist triangle,
`S' = S⟦1⟧`) and the `(> φ, ≤ φ)` truncation `U → S' → L₀` of `S'`: either `P` is a direct
summand of `G`, or `dim Hom(P, G) = r · dim Hom(P, L₀)`. -/
theorem divisibility_obstruction_bottom_finrank [IsTriangulated C] (s : Slicing C) {φ : ℝ}
    {P E S' U L₀ : C} (r : ℕ) (hP : s.P φ P) (hEnd : ∀ f : P ⟶ P, ∃ a : k, f = a • 𝟙 P)
    [Module.Finite k (P ⟶ L₀)] {j : (⨁ fun _ : Fin r => S') ⟶ E} {q : E ⟶ P}
    {c : P ⟶ (⨁ fun _ : Fin r => S')⟦(1 : ℤ)⟧} (hT : Triangle.mk j q c ∈ distTriang C)
    {u : U ⟶ S'} {π₀ : S' ⟶ L₀} {ε₀ : L₀ ⟶ U⟦(1 : ℤ)⟧} (h₀ : Triangle.mk u π₀ ε₀ ∈ distTriang C)
    (hU : s.gtProp C φ U) (hL₀ : s.leProp C φ L₀) {Q₁ L : C}
    {ιQ : Q₁ ⟶ ⨁ fun _ : Fin r => S'} {π : (⨁ fun _ : Fin r => S') ⟶ L}
    {εQ : L ⟶ Q₁⟦(1 : ℤ)⟧} (hQ : Triangle.mk ιQ π εQ ∈ distTriang C) (hQ₁ : s.gtProp C φ Q₁)
    (hL : s.leProp C φ L) {E₁ E₂ : C} {ιE : E₁ ⟶ E} {ρ : E ⟶ E₂} {εE : E₂ ⟶ E₁⟦(1 : ℤ)⟧}
    (hE : Triangle.mk ιE ρ εE ∈ distTriang C) (hE₁ : s.gtProp C φ E₁) (hE₂ : s.leProp C φ E₂)
    {G K : C} {γ : G ⟶ E₂} {κ : E₂ ⟶ K} {εG : K ⟶ G⟦(1 : ℤ)⟧}
    (hG : Triangle.mk γ κ εG ∈ distTriang C) (hK : s.ltProp C φ K) :
    (∃ (G' : C), Nonempty (G ≅ P ⊞ G')) ∨
      Module.finrank k (P ⟶ G) = r * Module.finrank k (P ⟶ L₀) := by
  obtain ⟨h₁, h₂⟩ := s.divisibility_obstruction_bottom (k := k) hP hEnd hT hQ hQ₁ hL hE hE₁ hE₂
    hG hK
  by_cases hc : c ≫ π⟦(1 : ℤ)⟧' = 0
  · exact Or.inl (h₁ hc)
  · obtain ⟨e⟩ := h₂ hc
    obtain ⟨eL, -⟩ := s.exists_iso_biproduct_of_leProp (S := fun _ : Fin r => S')
      (U := fun _ => U) (L₀ := fun _ => L₀) (fun _ => h₀) (fun _ => hU) (fun _ => hL₀) hQ hQ₁ hL
    right
    rw [← e.finrank_eq, (Linear.homCongr k (Iso.refl P) eL).finrank_eq,
      (Linear.biproductHomLinearEquiv k (fun _ : Fin r => L₀) P).finrank_eq,
      Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]

end Triangulated.Slicing

end CategoryTheory
