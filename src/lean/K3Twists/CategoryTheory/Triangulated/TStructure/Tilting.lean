/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.SerreClass.Additive
import K3Twists.CategoryTheory.Triangulated.TStructure.HeartAbelian

/-!
# A heart between `A` and `A[1]` is a tilt of `A`

Let `t` and `t'` be t-structures on a triangulated category, in Mathlib's cohomological
convention (`t.le 0` is the aisle `D^{≤0}`), with
`D_t^{≤ -1} ⊆ D_{t'}^{≤ 0} ⊆ D_t^{≤ 0}`. Write `A` and `A'` for their hearts. This is the
converse of the tilting theorem of Happel–Reiten–Smalø (*Tilting in abelian categories and
quasitilted algebras*, Mem. Amer. Math. Soc. 120 (1996), Proposition I.2.1; Polishchuk,
arXiv:math/0606013, Lemma 1.1.2):

* `TStructure.exists_distTriang_heart_of_le`: every `X ∈ A` sits in a distinguished triangle
  `X₁ → X → X₃ → X₁⟦1⟧` with `X₁ ∈ A ∩ D_{t'}^{≤0}` and `X₃ ∈ A ∩ D_{t'}^{≥1}`: the
  `t'`-truncation of `X`.
* `TStructure.torsionTheory_of_le`: so `(A ∩ D_{t'}^{≤0}, A ∩ D_{t'}^{≥1})` is a torsion pair in
  the abelian category `A`.
* `TStructure.mem_heart_iff_of_le`: `A'` is the tilt of `A` at that torsion pair: `E ∈ A'` iff
  `E` lies in `t`-degrees `[-1, 0]`, `τ_{≥0} E ∈ D_{t'}^{≤0}` and `τ_{<0} E ∈ D_{t'}^{≥0}`, i.e.
  `H⁰_t(E)` is torsion and `H⁻¹_t(E)` is torsion-free.

The hypothesis is the inclusion of aisles. For bounded t-structures it is equivalent to
`A' ⊆ D_t^{[-1, 0]}`; that equivalence is not proved here.

## Tags

t-structure, heart, tilting, torsion pair
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v' u' v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {t t' : TStructure C}

/-! ### Moving aisle inclusions -/

/-- An inclusion of aisles moves along shifts: `t.le a ≤ t'.le b` gives
`t.le (a + n) ≤ t'.le (b + n)`. -/
theorem le_add_le_add {a b : ℤ} (h : t.le a ≤ t'.le b) (n : ℤ) : t.le (a + n) ≤ t'.le (b + n) := by
  intro X hX
  have : t.IsLE X (a + n) := ⟨hX⟩
  have h₁ : t.IsLE (X⟦n⟧) a := t.isLE_shift X (a + n) n a
  have : t'.IsLE (X⟦n⟧) b := ⟨h _ h₁.le⟩
  exact (t'.isLE_shift_iff X (b + n) n b).1 this |>.le

/-- An inclusion of aisles `t'.le n ≤ t.le n` reverses on coaisles: `t.ge (n + 1) ≤
t'.ge (n + 1)`. -/
theorem ge_le_ge_of_le {n m : ℤ} (h : t'.le n ≤ t.le m) : t.ge (m + 1) ≤ t'.ge (n + 1) := by
  intro X hX
  have : t.IsGE X (m + 1) := ⟨hX⟩
  refine ((t'.isGE_iff_orthogonal n (n + 1) rfl X).2 fun Y f hY => ?_).ge
  have : t.IsLE Y m := ⟨h _ hY.le⟩
  exact t.zero f m (m + 1)

variable (h₁ : t.le (-1) ≤ t'.le 0) (h₂ : t'.le 0 ≤ t.le 0)
include h₁ h₂

/-! ### The torsion triangle -/

/-- **The torsion triangle.** If `D_t^{≤ -1} ⊆ D_{t'}^{≤ 0} ⊆ D_t^{≤ 0}`, every object `X` of the
heart of `t` sits in a distinguished triangle `X₁ → X → X₃ → X₁⟦1⟧` with `X₁` and `X₃` in the
heart of `t`, `X₁` in `D_{t'}^{≤ 0}` and `X₃` in `D_{t'}^{≥ 1}`: its `t'`-truncation. -/
theorem exists_distTriang_heart_of_le {X : C} (hX : t.heart X) :
    ∃ (X₁ X₃ : C) (f : X₁ ⟶ X) (g : X ⟶ X₃) (h : X₃ ⟶ X₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ t.heart X₁ ∧ t'.le 0 X₁ ∧ t.heart X₃ ∧
        t'.ge 1 X₃ := by
  have hge : t'.ge 1 ≤ t.ge 0 := by simpa using ge_le_ge_of_le h₁
  have hXle : t.IsLE X 0 := ⟨hX.1⟩
  have hXge : t.IsGE X 0 := ⟨hX.2⟩
  let X₁ := (t'.truncLT 1).obj X
  let X₃ := (t'.truncGE 1).obj X
  have hT := t'.triangleLTGE_distinguished 1 X
  have h₁le' : t'.IsLE X₁ 0 := t'.isLE_truncLT_obj ..
  have h₃ge' : t'.IsGE X₃ 1 := t'.isGE_truncGE_obj ..
  have h₁le : t.IsLE X₁ 0 := ⟨h₂ _ h₁le'.le⟩
  have h₃ge : t.IsGE X₃ 0 := ⟨hge _ h₃ge'.ge⟩
  have h₁ge : t.IsGE X₁ 0 := by
    apply t.isGE₂ _ (inv_rot_of_distTriang _ hT) 0
    · change t.IsGE (X₃⟦(-1 : ℤ)⟧) 0
      have : t.IsGE (X₃⟦(-1 : ℤ)⟧) 1 := t.isGE_shift X₃ 0 (-1) 1
      exact t.isGE_of_ge _ 0 1
    · exact hXge
  have h₃le : t.IsLE X₃ 0 := by
    apply t.isLE₂ _ (rot_of_distTriang _ hT) 0
    · exact hXle
    · change t.IsLE (X₁⟦(1 : ℤ)⟧) 0
      have : t.IsLE (X₁⟦(1 : ℤ)⟧) (-1) := t.isLE_shift X₁ 0 1 (-1)
      exact t.isLE_of_le _ (-1) 0
  exact ⟨X₁, X₃, _, _, _, hT, ⟨h₁le.le, h₁ge.ge⟩, h₁le'.le, ⟨h₃le.le, h₃ge.ge⟩, h₃ge'.ge⟩

/-- **The tilted heart.** If `D_t^{≤ -1} ⊆ D_{t'}^{≤ 0} ⊆ D_t^{≤ 0}`, an object `E` lies in the
heart of `t'` exactly when it lies in `t`-degrees `[-1, 0]`, `τ_{≥0} E` lies in `D_{t'}^{≤ 0}`
and `τ_{<0} E` lies in `D_{t'}^{≥ 0}`: `H⁰_t(E)` is torsion and `H⁻¹_t(E)` torsion-free for the
torsion pair of `exists_distTriang_heart_of_le`. -/
theorem mem_heart_iff_of_le (E : C) :
    t'.heart E ↔ t.le 0 E ∧ t.ge (-1) E ∧ t'.le 0 ((t.truncGE 0).obj E) ∧
      t'.ge 0 ((t.truncLT 0).obj E) := by
  have hge₁ : t.ge 1 ≤ t'.ge 1 := by simpa using ge_le_ge_of_le h₂
  have hge₀ : t.ge 0 ≤ t'.ge 0 := by
    simpa using ge_le_ge_of_le (le_add_le_add h₂ (-1))
  have hle₁ : t.le (-1) ≤ t'.le 0 := h₁
  have hT := t.triangleLTGE_distinguished 0 E
  have hK : t.IsLE ((t.truncLT 0).obj E) (-1) := t.isLE_truncLT_obj ..
  have hQ : t.IsGE ((t.truncGE 0).obj E) 0 := t.isGE_truncGE_obj ..
  constructor
  · rintro ⟨hEle', hEge'⟩
    have hEle' : t'.IsLE E 0 := ⟨hEle'⟩
    have hEge' : t'.IsGE E 0 := ⟨hEge'⟩
    refine ⟨h₂ _ hEle'.le, ?_, ?_, ?_⟩
    · -- `t'.ge 0 ⊆ t.ge (-1)`, from `t'.ge 1 ⊆ t.ge 0` shifted
      have hge : t'.ge 0 ≤ t.ge (-1) := by
        simpa using ge_le_ge_of_le (le_add_le_add h₁ (-1))
      exact hge _ hEge'.ge
    · refine (t'.isLE₂ _ (rot_of_distTriang _ hT) 0 ?_ ?_).le
      · exact hEle'
      · change t'.IsLE (((t.truncLT 0).obj E)⟦(1 : ℤ)⟧) 0
        have : t.IsLE (((t.truncLT 0).obj E)⟦(1 : ℤ)⟧) (-2) := t.isLE_shift _ (-1) 1 (-2)
        have : t.IsLE (((t.truncLT 0).obj E)⟦(1 : ℤ)⟧) (-1) := t.isLE_of_le _ (-2) (-1)
        exact ⟨hle₁ _ this.le⟩
    · refine (t'.isGE₂ _ (inv_rot_of_distTriang _ hT) 0 ?_ ?_).ge
      · change t'.IsGE (((t.truncGE 0).obj E)⟦(-1 : ℤ)⟧) 0
        have : t.IsGE (((t.truncGE 0).obj E)⟦(-1 : ℤ)⟧) 1 := t.isGE_shift _ 0 (-1) 1
        have : t'.IsGE (((t.truncGE 0).obj E)⟦(-1 : ℤ)⟧) 1 := ⟨hge₁ _ this.ge⟩
        exact t'.isGE_of_ge _ 0 1
      · exact hEge'
  · rintro ⟨-, -, hQ', hK'⟩
    have hQ' : t'.IsLE ((t.truncGE 0).obj E) 0 := ⟨hQ'⟩
    have hK' : t'.IsGE ((t.truncLT 0).obj E) 0 := ⟨hK'⟩
    refine ⟨?_, ?_⟩
    · refine (t'.isLE₂ _ hT 0 ?_ ?_).le
      · exact ⟨hle₁ _ hK.le⟩
      · exact hQ'
    · refine (t'.isGE₂ _ hT 0 ?_ ?_).ge
      · exact hK'
      · exact ⟨hge₀ _ hQ.ge⟩

/-! ### The torsion pair -/

variable {H : Type u'} [Category.{v'} H] [Preadditive H] [t.Heart H]

/-- **The converse of the tilting theorem.** If `D_t^{≤ -1} ⊆ D_{t'}^{≤ 0} ⊆ D_t^{≤ 0}`, the
objects of the heart of `t` lying in `D_{t'}^{≤ 0}` and those lying in `D_{t'}^{≥ 1}` form a
torsion pair in the heart of `t`. -/
theorem torsionTheory_of_le [IsTriangulated C] :
    letI := t.heartAbelian H
    Abelian.TorsionTheory ((t'.le 0).inverseImage (t.ιHeart (H := H)))
      ((t'.ge 1).inverseImage (t.ιHeart (H := H))) := by
  letI := t.heartAbelian H
  refine Abelian.TorsionTheory.of_shortExact
    (fun X Y f hX hY => t.ιHeart.map_injective ?_) (fun X => ?_)
  · have : t'.IsLE (t.ιHeart.obj X) 0 := ⟨hX⟩
    have : t'.IsGE (t.ιHeart.obj Y) 1 := ⟨hY⟩
    rw [Functor.map_zero]
    exact t'.zero _ 0 1
  obtain ⟨X₁, X₃, f, g, h, hT, hX₁, hX₁', hX₃, hX₃'⟩ :=
    exists_distTriang_heart_of_le h₁ h₂ (t.ιHeart_obj_mem X)
  rw [← t.essImage_ιHeart H] at hX₁ hX₃
  obtain ⟨Y₁, ⟨e₁⟩⟩ := hX₁
  obtain ⟨Y₃, ⟨e₃⟩⟩ := hX₃
  let f' : Y₁ ⟶ X := t.ιHeart.preimage (e₁.hom ≫ f)
  let g' : X ⟶ Y₃ := t.ιHeart.preimage (g ≫ e₃.inv)
  have hT' : Triangle.mk (t.ιHeart.map f') (t.ιHeart.map g')
      (e₃.hom ≫ h ≫ e₁.inv⟦(1 : ℤ)⟧') ∈ distTriang C := by
    refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁ (Iso.refl _) e₃ ?_ ?_ ?_)
    · simp [f']
    · simp [g']
    · simp [← Functor.map_comp]
  exact ⟨Y₁, Y₃, f', g', _, t.shortExact_of_distTriang (H := H) hT',
    (t'.le 0).prop_of_iso e₁.symm hX₁', (t'.ge 1).prop_of_iso e₃.symm hX₃'⟩

end CategoryTheory.Triangulated.TStructure
