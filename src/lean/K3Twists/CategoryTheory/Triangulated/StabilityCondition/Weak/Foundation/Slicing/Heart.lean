/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.SerreClass.Additive
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Foundation.PreStabilityCondition
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhases
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.TStructure
import K3Twists.CategoryTheory.Triangulated.TStructure.HeartAbelian

/-!
# The heart of a slicing as an abelian category

For a slicing `s` of a triangulated category and `a ∈ ℝ`, the half-open interval
`P((a, a+1])` (`Slicing.HeartCat s a`) is the heart of the t-structure `s.toTStructure a`, so it
is an abelian category (Bridgeland, arXiv:math/0212237, §3; Beilinson–Bernstein–Deligne,
*Faisceaux pervers*, Théorème 1.3.6). Its short exact sequences are
the distinguished triangles of the ambient category with vertices in `P((a, a+1])`.

Inside the heart sit the phase-`(a+1)` objects `P(a+1)` (`Slicing.heartTop`) and the thin
interval `P((a, a+1))` (`Slicing.heartFree`).

## Main results

* `Slicing.instAbelianHeartCat`: `P((a, a+1])` is abelian.
* `Slicing.HeartCat.shortExact_of_distTriang`, `Slicing.HeartCat.exists_distTriang_of_shortExact`:
  short exact sequences of the heart are the distinguished triangles on heart objects.
* `Slicing.torsionTheory_heartTop`: for any slicing, `(P(a+1), P((a, a+1)))` is a torsion pair in
  the heart; `Slicing.torsionTheory_heartAbove` is the torsion pair `(P((θ, a+1]), P((a, θ]))` of
  an interior cut `θ ∈ [a, a+1]`. Both come from the HN filtration cut at a phase.
* `Slicing.isSerreClass_heartTop`: given a charge, that is an additive `w : K₀ → ℝ` positive on
  nonzero semistable objects of phase in `(a, a+1)` and zero on `P(a+1)`, the class `P(a+1)` is a
  Serre class of the heart, so the torsion pair is hereditary (`Slicing.heartTop_hereditary`):
  `P(a+1)` is the kernel of `w`, which is nonnegative on the heart
  (`Slicing.weight_eq_zero_iff_of_heartProp`).
* `PreStabilityCondition.WithClassMap.isSerreClass_heartTop`: for a prestability condition the
  charge is `w = Im(e^{-iπa} Z)`.

## Implementation notes

For a bare slicing `P(a+1)` need not be closed under subobjects in the heart. On the derived
category of the `A₂` quiver, with simples `S₁`, `S₂` and the projective cover
`0 → S₂ → P → S₁ → 0` of `S₁`, give `S₁` and `P` phase `1` and `S₂` phase `1/2`: this is a
slicing, and the subobject `S₂ ⊂ P` leaves `P(1)`. So the Serre property needs the charge, and
the theorem takes it as the hypotheses `hpos`, `htop` on `w`.

## Tags

slicing, heart, abelian category, t-structure
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- **The heart of a slicing is abelian**: `P((a, a+1])` is the heart of `s.toTStructure a`. -/
instance Slicing.instAbelianHeartCat (s : Slicing C) (a : ℝ) : Abelian (s.HeartCat C a) :=
  (s.toTStructure C a).heartAbelian (s.HeartCat C a)

variable {C}

namespace Slicing.HeartCat

variable {s : Slicing C} {a : ℝ}

/-- A distinguished triangle `X₁ → X₂ → X₃ → X₁⟦1⟧` with vertices in `P((a, a+1])` is a short
exact sequence of the heart. -/
theorem shortExact_of_distTriang {X₁ X₂ X₃ : s.HeartCat C a} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
    {δ : X₃.obj ⟶ X₁.obj⟦(1 : ℤ)⟧} (hT : Triangle.mk f.hom g.hom δ ∈ distTriang C) :
    (ShortComplex.mk f g (ObjectProperty.hom_ext _ (by
      simpa using comp_distTriang_mor_zero₁₂ _ hT))).ShortExact :=
  (s.toTStructure C a).shortExact_of_distTriang (H := s.HeartCat C a) hT

/-- A short exact sequence of `P((a, a+1])` extends to a distinguished triangle of the ambient
category. -/
theorem exists_distTriang_of_shortExact {S : ShortComplex (s.HeartCat C a)}
    (hS : S.ShortExact) :
    ∃ δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧, Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C :=
  (s.toTStructure C a).exists_distTriang_of_shortExact (H := s.HeartCat C a) hS

end Slicing.HeartCat

variable (C)

/-! ### HN filtrations of heart objects -/

omit [IsTriangulated C] in
/-- A nonzero object of `P((a, a+1])` has an HN filtration with nonzero first and last factors
and all phases in `(a, a+1]`. -/
theorem Slicing.exists_hn_of_heartProp (s : Slicing C) {a : ℝ} {E : C}
    (hE : s.heartProp C a E) (hZ : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n), ¬IsZero (F.factor ⟨0, hn⟩) ∧
      ¬IsZero (F.factor ⟨F.n - 1, by omega⟩) ∧ ∀ i, a < F.φ i ∧ F.φ i ≤ a + 1 := by
  obtain ⟨G, hG, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hZ
  have hplus : G.phiPlus C hG ≤ a + 1 := by
    rcases hE.2 with h | ⟨F, hn, hF⟩
    · exact absurd h hZ
    · exact (G.phiPlus_le_of_firstFactor_nonzero C s F hG hn hfirst).trans hF
  have hminus : a < G.phiMinus C hG := by
    rcases hE.1 with h | ⟨F, hn, hF⟩
    · exact absurd h hZ
    · exact hF.trans_le (F.phiMinus_le_of_lastFactor_nonzero C s G hn hG hlast)
  exact ⟨G, hG, hfirst, hlast, fun i => ⟨hminus.trans_le (G.phase_mem_range C hG i).1,
    (G.phase_mem_range C hG i).2.trans hplus⟩⟩

omit [IsTriangulated C] in
/-- Strictly decreasing phases that all equal one value leave at most one factor, so the object
is semistable of that phase. -/
theorem Slicing.semistable_of_hn_phases_eq (s : Slicing C) {E : C} (F : HNFiltration C s.P E)
    {φ : ℝ} (hF : ∀ i, F.φ i = φ) : s.P φ E := by
  by_cases h0 : F.n = 0
  · exact s.zero_mem_of_isZero C φ E (F.isZero_of_length_zero h0)
  have h1 : F.n = 1 := by
    by_contra h2
    have := F.hφ (show (⟨0, by omega⟩ : Fin F.n) < ⟨1, by omega⟩ from Fin.mk_lt_mk.2 (by omega))
    rw [hF, hF] at this
    exact lt_irrefl _ this
  have := HNFiltration.semistable_of_length_one C s.closedUnderIso F h1
  rwa [hF] at this

/-- A finite family of reals below `b` has a cut `t ∈ [a, b)` above all its members below `b`. -/
private theorem exists_cut_below {n : ℕ} (φ : Fin n → ℝ) {a b : ℝ} (hab : a < b) :
    ∃ t, a ≤ t ∧ t < b ∧ ∀ i, φ i < b → φ i ≤ t := by
  classical
  let S := (Finset.univ.filter fun i => φ i < b).image φ
  by_cases hS : S.Nonempty
  · obtain ⟨i₀, hi₀, hi₀'⟩ := Finset.mem_image.1 (S.max'_mem hS)
    refine ⟨max a (S.max' hS), le_max_left _ _, max_lt hab ?_, fun i hi => ?_⟩
    · rw [← hi₀']
      exact (Finset.mem_filter.1 hi₀).2
    · exact le_max_of_le_right (S.le_max' _
        (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)))
  · exact ⟨a, le_rfl, hab, fun i hi => absurd
      ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)⟩ hS⟩

/-! ### Torsion pairs of the heart -/

/-- The objects of phase `a + 1` of the heart `P((a, a+1])`. -/
def Slicing.heartTop (s : Slicing C) (a : ℝ) : ObjectProperty (s.HeartCat C a) :=
  (s.P (a + 1)).inverseImage (s.heartProp C a).ι

/-- The objects of the heart `P((a, a+1])` with all phases below `a + 1`: the thin interval
`P((a, a+1))`. -/
def Slicing.heartFree (s : Slicing C) (a : ℝ) : ObjectProperty (s.HeartCat C a) :=
  (s.intervalProp C a (a + 1)).inverseImage (s.heartProp C a).ι

/-- The objects of the heart `P((a, a+1])` with all phases above `θ`: `P((θ, a+1])` when
`a ≤ θ`. -/
def Slicing.heartAbove (s : Slicing C) (a θ : ℝ) : ObjectProperty (s.HeartCat C a) :=
  (s.gtProp C θ).inverseImage (s.heartProp C a).ι

/-- The objects of the heart `P((a, a+1])` with all phases at most `θ`: `P((a, θ])` when
`θ ≤ a + 1`. -/
def Slicing.heartBelow (s : Slicing C) (a θ : ℝ) : ObjectProperty (s.HeartCat C a) :=
  (s.leProp C θ).inverseImage (s.heartProp C a).ι

omit [IsTriangulated C] in
theorem Slicing.intervalProp_isClosedUnderIsomorphisms (s : Slicing C) (a b : ℝ) :
    (s.intervalProp C a b).IsClosedUnderIsomorphisms where
  of_iso e h := h.elim (fun hE => Or.inl (IsZero.of_iso hE e.symm))
    (fun ⟨F, hF⟩ => Or.inr ⟨F.ofIso C e, hF⟩)

instance (s : Slicing C) (a : ℝ) : (s.heartTop C a).IsClosedUnderIsomorphisms := by
  dsimp [Slicing.heartTop]
  infer_instance

instance (s : Slicing C) (a : ℝ) : (s.heartFree C a).IsClosedUnderIsomorphisms := by
  have := s.intervalProp_isClosedUnderIsomorphisms C a (a + 1)
  dsimp [Slicing.heartFree]
  infer_instance

instance (s : Slicing C) (a θ : ℝ) : (s.heartAbove C a θ).IsClosedUnderIsomorphisms := by
  dsimp [Slicing.heartAbove]
  infer_instance

instance (s : Slicing C) (a θ : ℝ) : (s.heartBelow C a θ).IsClosedUnderIsomorphisms := by
  dsimp [Slicing.heartBelow]
  infer_instance

omit [IsTriangulated C] in
/-- A heart object whose underlying object is zero is a zero object of the heart. -/
theorem Slicing.HeartCat.isZero_of_obj_isZero {s : Slicing C} {a : ℝ} {X : s.HeartCat C a}
    (hX : IsZero X.obj) : IsZero X :=
  (IsZero.iff_id_eq_zero X).2 (ObjectProperty.hom_ext _ (hX.eq_of_src _ _))

/-- For a zero object `X`, the sequence `X → X → X` (the identity, then zero) is short exact: the
torsion sequence of a zero object. -/
private theorem shortExact_of_isZero {A : Type*} [Category A] [Abelian A] {X : A}
    (hX : IsZero X) : (ShortComplex.mk (𝟙 X) (0 : X ⟶ X) (by simp)).ShortExact :=
  { exact := ShortComplex.exact_of_isZero_X₂ _ hX
    mono_f := by dsimp; infer_instance
    epi_g := ⟨fun _ _ _ => hX.eq_of_src _ _⟩ }

/-- **The torsion pair of an interior cut.** For `θ ∈ [a, a+1]`, the objects of phases in
`(θ, a+1]` and those of phases in `(a, θ]` form a torsion pair in the heart `P((a, a+1])`; the
torsion sequence of an object is its HN filtration cut at `θ`. No charge is needed. -/
theorem Slicing.torsionTheory_heartAbove (s : Slicing C) {a θ : ℝ} (h₁ : a ≤ θ)
    (h₂ : θ ≤ a + 1) : Abelian.TorsionTheory (s.heartAbove C a θ) (s.heartBelow C a θ) := by
  refine Abelian.TorsionTheory.of_shortExact
    (fun X Y f hX hY => ObjectProperty.hom_ext _ (Slicing.hom_eq_zero_of_gtProp_leProp s hX hY _))
    (fun X => ?_)
  by_cases hZ : IsZero X.obj
  · exact ⟨X, X, 𝟙 X, 0, by simp, shortExact_of_isZero (HeartCat.isZero_of_obj_isZero C hZ),
      Or.inl hZ, Or.inl hZ⟩
  obtain ⟨F, hn, -, -, hF⟩ := s.exists_hn_of_heartProp C X.property hZ
  obtain ⟨X₁, X₃, GX, GY, f, g, h, hT, hGX, hGY, hGYlow, hGXorig⟩ :=
    F.exists_split_at_cutoff C θ
  have hX₁ : s.heartProp C a X₁ := s.heartProp_of_hn C GX fun j => by
    obtain ⟨i, hi⟩ := hGXorig j
    exact ⟨h₁.trans_lt (hGX j), hi ▸ (hF i).2⟩
  have hX₃ : s.heartProp C a X₃ := s.heartProp_of_hn C GY fun j =>
    ⟨(hF _).1.trans_le (hGYlow hn j), (hGY j).trans h₂⟩
  have hX₁' : s.gtProp C θ X₁ := by
    by_cases hn' : 0 < GX.n
    · exact s.gtProp_of_hn C GX θ hGX hn'
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  have hX₃' : s.leProp C θ X₃ := by
    by_cases hn' : 0 < GY.n
    · exact s.leProp_of_hn C GY θ hGY hn'
    · exact Or.inl (GY.isZero_of_length_zero (by omega))
  exact ⟨⟨X₁, hX₁⟩, ⟨X₃, hX₃⟩, ObjectProperty.homMk f, ObjectProperty.homMk g, _,
    HeartCat.shortExact_of_distTriang (δ := h) hT, hX₁', hX₃'⟩

/-- **The torsion pair of the heart** for any slicing: the objects of phase `a + 1` and the thin
interval `P((a, a+1))` form a torsion pair in `P((a, a+1])`. The torsion sequence of an object is
its HN filtration cut just below `a + 1`. -/
theorem Slicing.torsionTheory_heartTop (s : Slicing C) (a : ℝ) :
    Abelian.TorsionTheory (s.heartTop C a) (s.heartFree C a) := by
  refine Abelian.TorsionTheory.of_shortExact (fun X Y f hX hY => ObjectProperty.hom_ext _ ?_)
    (fun X => ?_)
  · rcases hY with hY | ⟨FY, hFY⟩
    · exact hY.eq_of_tgt _ _
    · exact s.hom_eq_zero_of_phase_gap C (HNFiltration.single C X.obj (a + 1) hX) FY
        (fun _ j => by simpa [HNFiltration.single] using (hFY j).2) _
  by_cases hZ : IsZero X.obj
  · exact ⟨X, X, 𝟙 X, 0, by simp, shortExact_of_isZero (HeartCat.isZero_of_obj_isZero C hZ),
      s.zero_mem_of_isZero C _ _ hZ, Or.inl hZ⟩
  obtain ⟨F, hn, -, -, hF⟩ := s.exists_hn_of_heartProp C X.property hZ
  obtain ⟨t, hta, ht1, hgap⟩ := exists_cut_below F.φ (show a < a + 1 by linarith)
  obtain ⟨X₁, X₃, GX, GY, f, g, h, hT, hGX, hGY, hGYlow, hGXorig⟩ :=
    F.exists_split_at_cutoff C t
  have hX₁ : s.P (a + 1) X₁ := s.semistable_of_hn_phases_eq C GX fun j => by
    obtain ⟨i, hi⟩ := hGXorig j
    have h₁ := hGX j
    rw [hi] at h₁ ⊢
    by_contra hne
    linarith [hgap i (lt_of_le_of_ne (hF i).2 hne)]
  have hX₃ : s.intervalProp C a (a + 1) X₃ :=
    Or.inr ⟨GY, fun j => ⟨(hF _).1.trans_le (hGYlow hn j), (hGY j).trans_lt ht1⟩⟩
  exact ⟨⟨X₁, s.heartProp_of_semistable C hX₁ (by linarith) le_rfl⟩,
    ⟨X₃, s.intervalProp_le_heartProp C a X₃ hX₃⟩, ObjectProperty.homMk f,
    ObjectProperty.homMk g, _, HeartCat.shortExact_of_distTriang (δ := h) hT, hX₁, hX₃⟩

/-! ### The Serre property, given a charge -/

section Charge

variable {C} {s : Slicing C} {a : ℝ} (w : K₀ C →+ ℝ)

omit [IsTriangulated C] in
/-- Given a charge `w` (positive on nonzero semistable objects of phase in `(a, a+1)`, zero on
`P(a+1)`), every object of the heart has `0 ≤ w`, since `w` is the sum over the HN factors. -/
theorem Slicing.weight_nonneg_of_heartProp
    (hpos : ∀ φ E, a < φ → φ < a + 1 → s.P φ E → ¬IsZero E → 0 < w (K₀.of C E))
    (htop : ∀ E, s.P (a + 1) E → w (K₀.of C E) = 0) {E : C} (hE : s.heartProp C a E) :
    0 ≤ w (K₀.of C E) := by
  by_cases hZ : IsZero E
  · simp [K₀.of_isZero C hZ]
  obtain ⟨F, -, -, -, hF⟩ := s.exists_hn_of_heartProp C hE hZ
  rw [K₀.of_postnikovTower_eq_sum C F.toPostnikovTower, map_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rcases (hF i).2.lt_or_eq with hlt | heq
  · by_cases hZi : IsZero (F.factor i)
    · simp [K₀.of_isZero C hZi]
    · exact (hpos _ _ (hF i).1 hlt (F.semistable i) hZi).le
  · exact (htop _ (heq ▸ F.semistable i)).ge

omit [IsTriangulated C] in
/-- Given a charge `w`, an object of the heart lies in `P(a+1)` exactly when `w` vanishes on
it. -/
theorem Slicing.weight_eq_zero_iff_of_heartProp
    (hpos : ∀ φ E, a < φ → φ < a + 1 → s.P φ E → ¬IsZero E → 0 < w (K₀.of C E))
    (htop : ∀ E, s.P (a + 1) E → w (K₀.of C E) = 0) {E : C} (hE : s.heartProp C a E) :
    w (K₀.of C E) = 0 ↔ s.P (a + 1) E := by
  refine ⟨fun h0 => ?_, htop E⟩
  by_cases hZ : IsZero E
  · exact s.zero_mem_of_isZero C _ E hZ
  obtain ⟨F, hn, -, hlast, hF⟩ := s.exists_hn_of_heartProp C hE hZ
  have hterm : ∀ i, 0 ≤ w (K₀.of C (F.factor i)) := fun i => by
    rcases (hF i).2.lt_or_eq with hlt | heq
    · by_cases hZi : IsZero (F.factor i)
      · simp [K₀.of_isZero C hZi]
      · exact (hpos _ _ (hF i).1 hlt (F.semistable i) hZi).le
    · exact (htop _ (heq ▸ F.semistable i)).ge
  rw [K₀.of_postnikovTower_eq_sum C F.toPostnikovTower, map_sum,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i] at h0
  have hlast_eq : F.φ ⟨F.n - 1, by omega⟩ = a + 1 := by
    by_contra hne
    exact (hpos _ _ (hF _).1 (lt_of_le_of_ne (hF _).2 hne) (F.semistable _) hlast).ne'
      (h0 _ (Finset.mem_univ _))
  refine s.semistable_of_hn_phases_eq C F fun i => le_antisymm (hF i).2 ?_
  rw [← hlast_eq]
  exact F.hφ.antitone (Fin.mk_le_mk.2 (by omega))

/-- **`P(a+1)` is a Serre class of the heart, given a charge.** If `w : K₀ → ℝ` is positive on
nonzero semistable objects of phase in `(a, a+1)` and zero on `P(a+1)`, then the objects of
phase `a + 1` form a Serre class of the heart `P((a, a+1])`: it is the kernel of `w`, which is
additive on short exact sequences of the heart and nonnegative there. -/
theorem Slicing.isSerreClass_heartTop
    (hpos : ∀ φ E, a < φ → φ < a + 1 → s.P φ E → ¬IsZero E → 0 < w (K₀.of C E))
    (htop : ∀ E, s.P (a + 1) E → w (K₀.of C E) = 0) : (s.heartTop C a).IsSerreClass := by
  have heq : s.heartTop C a = fun X => w (K₀.of C X.obj) = 0 := by
    ext X
    exact (s.weight_eq_zero_iff_of_heartProp w hpos htop X.property).symm
  rw [heq]
  refine ObjectProperty.isSerreClass_of_additive_nonneg _ (fun S hS => ?_)
    (fun X => s.weight_nonneg_of_heartProp w hpos htop X.property)
  obtain ⟨δ, hT⟩ := HeartCat.exists_distTriang_of_shortExact hS
  have h := K₀.of_triangle C _ hT
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at h
  change w (K₀.of C S.X₂.obj) = w (K₀.of C S.X₁.obj) + w (K₀.of C S.X₃.obj)
  rw [h, map_add]

/-- **The torsion pair of the heart is hereditary, given a charge**: `P(a+1)` is closed under
subobjects in the heart. -/
theorem Slicing.heartTop_hereditary
    (hpos : ∀ φ E, a < φ → φ < a + 1 → s.P φ E → ¬IsZero E → 0 < w (K₀.of C E))
    (htop : ∀ E, s.P (a + 1) E → w (K₀.of C E) = 0) :
    (s.heartTop C a).IsClosedUnderSubobjects :=
  have := s.isSerreClass_heartTop w hpos htop
  inferInstance

end Charge

/-! ### The charge of a prestability condition -/

namespace PreStabilityCondition.WithClassMap

variable {C} {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- The weight of the heart `P((a, a+1])` of a prestability condition: the imaginary part of the
central charge rotated by `e^{-iπa}`, `w(E) = Im(e^{-iπa} Z(E))`. For `a = 0` it is `Im Z`. -/
def heartWeight (σ : WithClassMap C v) (a : ℝ) : K₀ C →+ ℝ :=
  Complex.imAddGroupHom.comp
    ((AddMonoidHom.mulLeft (Complex.exp (↑(-(Real.pi * a)) * Complex.I))).comp (σ.Z.comp v))

omit [IsTriangulated C] in
/-- On a nonzero semistable object of phase `φ` and mass `m > 0`, the weight is
`m sin(π(φ - a))`. -/
theorem heartWeight_of_semistable (σ : WithClassMap C v) (a φ : ℝ) {E : C}
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ∃ m : ℝ, 0 < m ∧ σ.heartWeight a (K₀.of C E) = m * Real.sin (Real.pi * (φ - a)) := by
  obtain ⟨m, hm, hZ⟩ := σ.compat φ E hP hE
  refine ⟨m, hm, ?_⟩
  have hZ' : σ.Z (v (K₀.of C E)) = (m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I) := hZ
  have hrot : Complex.exp (↑(-(Real.pi * a)) * Complex.I) *
      ((m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I)) =
      (m : ℂ) * Complex.exp ((Real.pi * (φ - a) : ℝ) * Complex.I) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp only [heartWeight, AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, hZ', hrot]
  change ((m : ℂ) * Complex.exp ((Real.pi * (φ - a) : ℝ) * Complex.I)).im = _
  rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

omit [IsTriangulated C] in
/-- The weight is positive on nonzero semistable objects of phase in `(a, a+1)`. -/
theorem heartWeight_pos (σ : WithClassMap C v) {a φ : ℝ} {E : C} (h₁ : a < φ) (h₂ : φ < a + 1)
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) : 0 < σ.heartWeight a (K₀.of C E) := by
  obtain ⟨m, hm, h⟩ := σ.heartWeight_of_semistable a φ hP hE
  rw [h]
  exact mul_pos hm (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos]))

omit [IsTriangulated C] in
/-- The weight vanishes on `P(a+1)`. -/
theorem heartWeight_eq_zero_of_top (σ : WithClassMap C v) {a : ℝ} {E : C}
    (hP : σ.slicing.P (a + 1) E) : σ.heartWeight a (K₀.of C E) = 0 := by
  by_cases hE : IsZero E
  · simp [K₀.of_isZero C hE]
  obtain ⟨m, -, h⟩ := σ.heartWeight_of_semistable a (a + 1) hP hE
  rw [h, show Real.pi * (a + 1 - a) = Real.pi by ring, Real.sin_pi, mul_zero]

/-- **`P(a+1)` is a Serre class of the heart of a prestability condition**, cut out by
`Im(e^{-iπa} Z) = 0`; for `a = 0`, the phase-one objects of `P((0, 1])` are the kernel of
`Im Z`. -/
theorem isSerreClass_heartTop (σ : WithClassMap C v) (a : ℝ) :
    (σ.slicing.heartTop C a).IsSerreClass :=
  σ.slicing.isSerreClass_heartTop (σ.heartWeight a)
    (fun _ _ h₁ h₂ hP hE => σ.heartWeight_pos h₁ h₂ hP hE)
    (fun _ hP => σ.heartWeight_eq_zero_of_top hP)

/-- The torsion pair `(P(a+1), P((a, a+1)))` of the heart of a prestability condition is
hereditary. -/
theorem heartTop_hereditary (σ : WithClassMap C v) (a : ℝ) :
    (σ.slicing.heartTop C a).IsClosedUnderSubobjects :=
  have := σ.isSerreClass_heartTop a
  inferInstance

end PreStabilityCondition.WithClassMap

end CategoryTheory.Triangulated
