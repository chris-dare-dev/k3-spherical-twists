/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.FiveLemma
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Window dévissage

Let `F : C ⥤ D` be a triangulated functor between pretriangulated categories. For objects `X`,
`Y` of `C` and `n : ℤ`, write `F_n : Hom(X, Y⟦n⟧) → Hom(F X, (F Y)⟦n⟧)` for the action of `F` on
shifted morphisms, Mathlib's `ShiftedHom.map` (`f ↦ F.map f ≫ (F.commShiftIso n).hom.app Y`).

For integers `a`, `b`, the **window condition** `W_{a,b}(X, Y)` (`Functor.IsExtWindow`) asks that

* `F_n` be surjective on `Hom(X, Y⟦n⟧)` for `a - 1 ≤ n ≤ b`, and
* `F_n` be injective on `Hom(X, Y⟦n⟧)` for `a ≤ n ≤ b + 1`;

so `F_n` is bijective for `a ≤ n ≤ b`, surjective at `a - 1` and injective at `b + 1`.

**Window dévissage** (`Functor.isExtWindow_of_extensionClosure`): if `W_{a,b}(S, T)` holds for all
`S`, `T` in a family `𝒮`, it holds for all `X`, `Y` in the extension closure `𝒮̄` of `𝒮`. The
proof is the four lemma, applied to the two long exact Hom sequences of a distinguished triangle
(in the second variable through `Triangle.coyoneda_exact₂`/`₃`, in the first through
`Triangle.yoneda_exact₂`/`₃`), one degree at a time. No source class of objects with vanishing
negative self-extensions and no target class is needed. The window is not required to be
nonempty.

Consequences, for `𝒮̄` the extension closure:

* if `a ≤ 0 ≤ b`, then `F` is fully faithful on `𝒮̄` (`Functor.fullyFaithfulOfIsExtWindow`);
* if `a ≤ 2` and `1 ≤ b`, the essential image of `F` on `𝒮̄` is the extension closure of `F 𝒮`
  (`Functor.map_extensionClosure_eq`): a target extension class is `F_1` of a source class, and
  a distinguished triangle is determined by its third morphism up to isomorphism.

In particular for `a ≤ 0 < 1 ≤ b`, `F` restricted to `𝒮̄` is an equivalence onto the extension
closure of `F 𝒮`. The usual window `[0, 1]` asks for surjectivity of `F_{-1}`, for instance
`Hom(F S, (F T)⟦-1⟧) = 0`, and injectivity of `F_2`.

The **Yoneda compatibility** `F_{p+q}(u · w) = F_p(u) · F_q(w)` of the composition of shifted
morphisms holds for every functor that commutes with shifts, with no sign; it is Mathlib's
`ShiftedHom.map_comp` (`Functor.map_shiftedHom_comp`).

## The extension closure

`ObjectProperty.extensionClosure P` is defined inductively: it contains `P`, the zero objects, and
the middle term of every distinguished triangle whose outer terms it contains. It is closed under
isomorphisms. Mathlib's `ObjectProperty.extensionProductIter` describes iterated extensions;
its union is contained in the closure (`ObjectProperty.extensionProductIter_le_extensionClosure`)
and equals it only under the octahedral axiom, which is why the closure here is inductive.

## Main definitions

* `ShiftedHom.mapAddHom`: `F_n` as an additive map.
* `Functor.IsExtWindow F a b X Y`: the window condition `W_{a,b}(X, Y)`.
* `ObjectProperty.extensionClosure`: the extension closure.

## Main results

* `Functor.IsExtWindow.of_triangle_right`, `Functor.IsExtWindow.of_triangle_left`: the dévissage
  steps in each variable.
* `Functor.isExtWindow_of_extensionClosure`: window dévissage.
* `Functor.fullyFaithfulOfIsExtWindow`, `Functor.map_extensionClosure_eq`: full faithfulness and the
  essential image.

## References

The model is the full-faithfulness criterion for Fourier–Mukai functors: Bondal–Orlov,
*Semiorthogonal decomposition for algebraic varieties*, arXiv:alg-geom/9506012, Theorem 1.1
(the images of the skyscraper sheaves of distinct points are orthogonal in every degree, and those
of one point have endomorphisms `k` and no shifted self-morphisms outside `[0, dim M]`), and
Bridgeland, *Equivalences of triangulated categories and Fourier–Mukai transforms*,
arXiv:math/9809114, Theorem 1.1 (a strongly simple kernel) and Theorem 2.3 (an exact functor with
adjoints that is bijective on all shifted morphisms between the objects of a spanning class).
Window dévissage is the extension-closure argument without adjoints or a spanning class: it gives
full faithfulness on the extension closure of the family only, and keeps only the degrees the four
lemma uses.

## Tags

window dévissage, extension closure, full faithfulness, triangulated functor
-/

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits Pretriangulated Preadditive ZeroObject

namespace CategoryTheory

/-! ### The action of a functor on shifted morphisms, as an additive map -/

namespace ShiftedHom

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] [Preadditive C]
  [Preadditive D] {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M]

/-- `ShiftedHom.map` as an additive map `Hom(X, Y⟦n⟧) → Hom(F X, (F Y)⟦n⟧)`. -/
@[simps]
def mapAddHom (F : C ⥤ D) [F.CommShift M] [F.Additive] (X Y : C) (n : M) :
    ShiftedHom X Y n →+ ShiftedHom (F.obj X) (F.obj Y) n where
  toFun f := f.map F
  map_zero' := map_zero F
  map_add' f g := map_add f g F

end ShiftedHom

/-! ### The extension closure -/

namespace ObjectProperty

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The **extension closure** of a property of objects of a pretriangulated category: the
smallest property that contains `P` and the zero objects and contains the middle term of every
distinguished triangle whose outer terms it contains. -/
inductive extensionClosure (P : ObjectProperty C) : ObjectProperty C
  /-- Objects of `P` are in the closure. -/
  | of_prop {X : C} (hX : P X) : extensionClosure P X
  /-- Zero objects are in the closure. -/
  | of_isZero {X : C} (hX : IsZero X) : extensionClosure P X
  /-- The middle term of a distinguished triangle with outer terms in the closure. -/
  | ext (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : extensionClosure P T.obj₁)
      (h₃ : extensionClosure P T.obj₃) : extensionClosure P T.obj₂

variable (P : ObjectProperty C)

theorem le_extensionClosure : P ≤ P.extensionClosure :=
  fun _ hX ↦ .of_prop hX

/-- The closure is closed under isomorphisms: `X ⟶ X' ⟶ 0 ⟶ X⟦1⟧` is distinguished. -/
theorem extensionClosure_of_iso {X X' : C} (e : X ≅ X') (hX : P.extensionClosure X) :
    P.extensionClosure X' := by
  have hT : Triangle.mk e.hom (0 : X' ⟶ 0) 0 ∈ distTriang C :=
    (Triangle.distinguished_iff_of_isZero₃ _ (isZero_zero C)).2 (by dsimp; infer_instance)
  exact .ext _ hT hX (.of_isZero (isZero_zero C))

instance : P.extensionClosure.IsClosedUnderIsomorphisms where
  of_iso e hX := P.extensionClosure_of_iso e hX

instance : P.extensionClosure.ContainsZero where
  exists_zero := ⟨0, isZero_zero C, .of_isZero (isZero_zero C)⟩

instance : P.extensionClosure.IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ ↦ .ext T hT h₁ h₃

/-- The closure is the smallest property containing `P` and the zero objects that is closed under
extensions. -/
theorem extensionClosure_le {Q : ObjectProperty C} [Q.ContainsZero] [Q.IsTriangulatedClosed₂]
    [Q.IsClosedUnderIsomorphisms] (h : P ≤ Q) : P.extensionClosure ≤ Q := by
  intro X hX
  induction hX with
  | of_prop hX => exact h _ hX
  | of_isZero hX => exact Q.prop_of_isZero hX
  | ext T hT _ _ h₁ h₃ => exact Q.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

theorem extensionClosure_mono {Q : ObjectProperty C} (h : P ≤ Q) :
    P.extensionClosure ≤ Q.extensionClosure :=
  P.extensionClosure_le (h.trans Q.le_extensionClosure)

theorem extensionProduct_le_extensionClosure {Q R : ObjectProperty C}
    (hQ : Q ≤ P.extensionClosure) (hR : R ≤ P.extensionClosure) :
    Q.extensionProduct R ≤ P.extensionClosure := by
  rintro X ⟨Y, Z, f, g, h, hT, hY, hZ⟩
  exact .ext (Triangle.mk f g h) hT (hQ _ hY) (hR _ hZ)

/-- Iterated extensions of objects of `P` are in the extension closure. The converse holds when
`C` is triangulated (`ObjectProperty.extensionProductIter_succ'`), not in general. -/
theorem extensionProductIter_le_extensionClosure (n : ℕ) :
    P.extensionProductIter n ≤ P.extensionClosure := by
  induction n with
  | zero => exact P.le_extensionClosure
  | succ n ih =>
    rw [extensionProductIter_succ]
    exact P.extensionProduct_le_extensionClosure P.le_extensionClosure ih

end ObjectProperty

/-! ### The long exact Hom sequences of a distinguished triangle -/

section TriangleSequences

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- The shift of a distinguished triangle, written with `Triangle.mk`. -/
private theorem shift_mk_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) :
    Triangle.mk (n.negOnePow • T.mor₁⟦n⟧') (n.negOnePow • T.mor₂⟦n⟧')
      (n.negOnePow • T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁) ∈ distTriang C :=
  Triangle.shift_distinguished T hT n

private theorem coyoneda_exact₂_shift (T : Triangle C) (hT : T ∈ distTriang C) {X : C} (n : ℤ)
    (u : X ⟶ T.obj₂⟦n⟧) (hu : u ≫ T.mor₂⟦n⟧' = 0) : ∃ v, u = v ≫ T.mor₁⟦n⟧' := by
  obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _ (shift_mk_distinguished T hT n) u (by simp [hu])
  exact ⟨n.negOnePow • v, by simpa using hv⟩

private theorem coyoneda_exact₃_shift (T : Triangle C) (hT : T ∈ distTriang C) {X : C} (n : ℤ)
    (w : X ⟶ T.obj₃⟦n⟧) (hw : w ≫ T.mor₃⟦n⟧' = 0) : ∃ u, w = u ≫ T.mor₂⟦n⟧' := by
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₃ _ (shift_mk_distinguished T hT n) w
    (by simp [reassoc_of% hw])
  exact ⟨n.negOnePow • u, by simpa using hu⟩

private theorem coyoneda_exact₁_shift (T : Triangle C) (hT : T ∈ distTriang C) {X : C}
    (n n' : ℤ) (h : 1 + n = n') (v : X ⟶ T.obj₁⟦n'⟧) (hv : v ≫ T.mor₁⟦n'⟧' = 0) :
    ∃ w, v = w ≫ T.mor₃⟦n⟧' ≫ (shiftFunctorAdd' C 1 n n' h).inv.app T.obj₁ := by
  have hR : Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦(1 : ℤ)⟧') ∈ distTriang C := rot_of_distTriang _ hT
  have nat := (shiftFunctorAdd' C 1 n n' h).hom.naturality T.mor₁
  dsimp at nat
  have hw : (v ≫ (shiftFunctorAdd' C 1 n n' h).hom.app T.obj₁) ≫
      (-T.mor₁⟦(1 : ℤ)⟧')⟦n⟧' = 0 := by
    rw [Functor.map_neg, Preadditive.comp_neg, Category.assoc, ← nat, reassoc_of% hv,
      zero_comp, neg_zero]
  obtain ⟨u, hu⟩ := coyoneda_exact₃_shift _ hR n _ hw
  refine ⟨u, ?_⟩
  dsimp at hu
  rw [← reassoc_of% hu]
  simp

/-- Exactness of `Hom(X, T₁⟦n⟧) → Hom(X, T₂⟦n⟧) → Hom(X, T₃⟦n⟧)`. -/
theorem Pretriangulated.exact_rightComp_shift_mor₁ (T : Triangle C) (hT : T ∈ distTriang C)
    (X : C) (n : ℤ) :
    Function.Exact (rightComp X (T.mor₁⟦n⟧')) (rightComp X (T.mor₂⟦n⟧')) := by
  intro u
  simp only [rightComp, AddMonoidHom.mk'_apply, Set.mem_range]
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := coyoneda_exact₂_shift T hT n u hu
    exact ⟨v, hv.symm⟩
  · rintro ⟨v, rfl⟩
    simp [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT]

/-- Exactness of `Hom(X, T₂⟦n⟧) → Hom(X, T₃⟦n⟧) → Hom(X, T₁⟦n'⟧)` for `1 + n = n'`. The second
map is the composition `u ↦ u · T.mor₃` of shifted morphisms. -/
theorem Pretriangulated.exact_rightComp_shift_mor₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (X : C) (n n' : ℤ) (h : 1 + n = n') :
    Function.Exact (rightComp X (T.mor₂⟦n⟧'))
      (rightComp X (T.mor₃⟦n⟧' ≫ (shiftFunctorAdd' C 1 n n' h).inv.app T.obj₁)) := by
  intro w
  simp only [rightComp, AddMonoidHom.mk'_apply, Set.mem_range]
  constructor
  · intro hw
    rw [← Category.assoc, Preadditive.IsIso.comp_right_eq_zero] at hw
    obtain ⟨u, hu⟩ := coyoneda_exact₃_shift T hT n w hw
    exact ⟨u, hu.symm⟩
  · rintro ⟨u, rfl⟩
    simp [← Functor.map_comp_assoc, comp_distTriang_mor_zero₂₃ _ hT]

/-- Exactness of `Hom(X, T₃⟦n⟧) → Hom(X, T₁⟦n'⟧) → Hom(X, T₂⟦n'⟧)` for `1 + n = n'`. -/
theorem Pretriangulated.exact_rightComp_shift_mor₃ (T : Triangle C) (hT : T ∈ distTriang C)
    (X : C) (n n' : ℤ) (h : 1 + n = n') :
    Function.Exact (rightComp X (T.mor₃⟦n⟧' ≫ (shiftFunctorAdd' C 1 n n' h).inv.app T.obj₁))
      (rightComp X (T.mor₁⟦n'⟧')) := by
  intro v
  simp only [rightComp, AddMonoidHom.mk'_apply, Set.mem_range]
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := coyoneda_exact₁_shift T hT n n' h v hv
    exact ⟨w, hw.symm⟩
  · rintro ⟨u, rfl⟩
    have nat' := (shiftFunctorAdd' C 1 n n' h).inv.naturality T.mor₁
    dsimp at nat'
    simp only [Category.assoc, ← nat']
    simp [← Functor.map_comp_assoc, comp_distTriang_mor_zero₃₁ _ hT]

/-- Exactness of `Hom(T₃, Z) → Hom(T₂, Z) → Hom(T₁, Z)`. -/
theorem Pretriangulated.exact_leftComp_mor₂ (T : Triangle C) (hT : T ∈ distTriang C) (Z : C) :
    Function.Exact (leftComp Z T.mor₂) (leftComp Z T.mor₁) := by
  intro g
  simp only [leftComp, AddMonoidHom.mk'_apply, Set.mem_range]
  constructor
  · intro hg
    obtain ⟨h, rfl⟩ := Triangle.yoneda_exact₂ _ hT g hg
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    simp [comp_distTriang_mor_zero₁₂_assoc _ hT]

/-- The composition `u ↦ T.mor₃ · u` of shifted morphisms, `Hom(T₁, Y⟦m⟧) → Hom(T₃, Y⟦n⟧)` for
`m + 1 = n`, as an additive map. -/
def Pretriangulated.shiftedHomCompMor₃ (T : Triangle C) (Y : C) (m n : ℤ) (h : m + 1 = n) :
    ShiftedHom T.obj₁ Y m →+ ShiftedHom T.obj₃ Y n :=
  AddMonoidHom.mk' (fun u ↦ (show ShiftedHom T.obj₃ T.obj₁ (1 : ℤ) from T.mor₃).comp u h)
    fun _ _ ↦ ShiftedHom.comp_add _ _ _ _

omit [HasZeroObject C] [Pretriangulated C] in
@[simp]
theorem Pretriangulated.shiftedHomCompMor₃_apply (T : Triangle C) (Y : C) (m n : ℤ)
    (h : m + 1 = n) (u : ShiftedHom T.obj₁ Y m) :
    shiftedHomCompMor₃ T Y m n h u =
      T.mor₃ ≫ u⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C m 1 n h).inv.app Y :=
  rfl

/-- Exactness of `Hom(T₁, Y⟦m⟧) → Hom(T₃, Y⟦n⟧) → Hom(T₂, Y⟦n⟧)` for `m + 1 = n`. -/
theorem Pretriangulated.exact_shiftedHomCompMor₃_leftComp (T : Triangle C)
    (hT : T ∈ distTriang C) (Y : C) (m n : ℤ) (h : m + 1 = n) :
    Function.Exact (shiftedHomCompMor₃ T Y m n h) (leftComp (Y⟦n⟧) T.mor₂) := by
  intro g
  simp only [leftComp, AddMonoidHom.mk'_apply, Set.mem_range, shiftedHomCompMor₃_apply]
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Triangle.yoneda_exact₃ _ hT g hg
    obtain ⟨u, hu⟩ := (CategoryTheory.shiftFunctor C (1 : ℤ)).map_surjective
      (k ≫ (shiftFunctorAdd' C m 1 n h).hom.app Y)
    refine ⟨u, ?_⟩
    simp [hu]
  · rintro ⟨u, rfl⟩
    simp [comp_distTriang_mor_zero₂₃_assoc _ hT]

/-- Exactness of `Hom(T₂, Y⟦m⟧) → Hom(T₁, Y⟦m⟧) → Hom(T₃, Y⟦n⟧)` for `m + 1 = n`. -/
theorem Pretriangulated.exact_leftComp_shiftedHomCompMor₃ (T : Triangle C)
    (hT : T ∈ distTriang C) (Y : C) (m n : ℤ) (h : m + 1 = n) :
    Function.Exact (leftComp (Y⟦m⟧) T.mor₁) (shiftedHomCompMor₃ T Y m n h) := by
  intro u
  simp only [leftComp, AddMonoidHom.mk'_apply, Set.mem_range, shiftedHomCompMor₃_apply]
  constructor
  · intro hu
    rw [← Category.assoc, Preadditive.IsIso.comp_right_eq_zero] at hu
    have hR : Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦(1 : ℤ)⟧') ∈ distTriang C :=
      rot_of_distTriang _ hT
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ hR _ hu
    obtain ⟨g, rfl⟩ := (CategoryTheory.shiftFunctor C (1 : ℤ)).map_surjective k
    refine ⟨-g, (CategoryTheory.shiftFunctor C (1 : ℤ)).map_injective ?_⟩
    simpa using hk.symm
  · rintro ⟨g, rfl⟩
    simp [comp_distTriang_mor_zero₃₁_assoc _ hT]

end TriangleSequences

/-! ### The window condition -/

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]

/-- The **window condition** `W_{a,b}(X, Y)`: `F` is surjective on `Hom(X, Y⟦n⟧)` for
`a - 1 ≤ n ≤ b` and injective for `a ≤ n ≤ b + 1`, so bijective for `a ≤ n ≤ b`. -/
structure IsExtWindow (a b : ℤ) (X Y : C) : Prop where
  /-- Surjectivity of `F_n` for `a - 1 ≤ n ≤ b`. -/
  surjective (n : ℤ) : a ≤ n + 1 → n ≤ b →
    Function.Surjective (fun f : ShiftedHom X Y n ↦ f.map F)
  /-- Injectivity of `F_n` for `a ≤ n ≤ b + 1`. -/
  injective (n : ℤ) : a ≤ n → n ≤ b + 1 →
    Function.Injective (fun f : ShiftedHom X Y n ↦ f.map F)

variable {F}

theorem IsExtWindow.bijective {a b : ℤ} {X Y : C} (h : F.IsExtWindow a b X Y) (n : ℤ)
    (ha : a ≤ n) (hb : n ≤ b) :
    Function.Bijective (fun f : ShiftedHom X Y n ↦ f.map F) :=
  ⟨h.injective n ha (by lia), h.surjective n (by lia) hb⟩

/-- The window condition with all degrees bijective. -/
theorem IsExtWindow.of_bijective {a b : ℤ} {X Y : C}
    (h : ∀ n : ℤ, Function.Bijective (fun f : ShiftedHom X Y n ↦ f.map F)) :
    F.IsExtWindow a b X Y :=
  ⟨fun n _ _ ↦ (h n).2, fun n _ _ ↦ (h n).1⟩

/-- The window condition on the identity functor, for every window. -/
theorem isExtWindow_id (a b : ℤ) (X Y : C) : (𝟭 C).IsExtWindow a b X Y :=
  .of_bijective fun n ↦ by simp only [ShiftedHom.id_map]; exact Function.bijective_id

/-- In degree `0`, `F_0` is `F.map` up to the identifications `Hom(X, Y) ≃ Hom(X, Y⟦0⟧)`. -/
theorem map_bijective_iff_shiftedHom_zero {X Y : C} :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) ↔
      Function.Bijective (fun f : ShiftedHom X Y (0 : ℤ) ↦ f.map F) := by
  have key : (ShiftedHom.homEquiv 0 rfl).symm ∘
      (fun f : ShiftedHom X Y (0 : ℤ) ↦ f.map F) ∘ ShiftedHom.homEquiv 0 rfl = F.map := by
    ext f
    simp only [Function.comp_apply, ShiftedHom.homEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
      ShiftedHom.map_mk₀]
    simp [ShiftedHom.mk₀]
  rw [← key, Equiv.comp_bijective, Equiv.bijective_comp]

/-- On a window containing degree `0`, `F.map` is bijective on `Hom(X, Y)`. -/
theorem IsExtWindow.map_bijective {a b : ℤ} {X Y : C} (h : F.IsExtWindow a b X Y) (ha : a ≤ 0)
    (hb : 0 ≤ b) : Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  F.map_bijective_iff_shiftedHom_zero.2 (h.bijective 0 ha hb)

/-! ### Yoneda compatibility -/

/-- **Yoneda compatibility.** A functor that commutes with shifts preserves the composition of
shifted morphisms, `F_{p+q}(u · w) = F_p(u) · F_q(w)`, with no sign. This is Mathlib's
`ShiftedHom.map_comp`, restated in the degrees used for `Ext`. -/
theorem map_shiftedHom_comp (G : C ⥤ D) [G.CommShift ℤ] {X Y Z : C} {p q r : ℤ}
    (u : ShiftedHom X Y p) (w : ShiftedHom Y Z q) (h : q + p = r) :
    (u.comp w h).map G = (u.map G).comp (w.map G) h :=
  ShiftedHom.map_comp u w h G

variable [Preadditive C] [Preadditive D] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [F.IsTriangulated]

theorem IsExtWindow.of_isZero_left {a b : ℤ} {X : C} (hX : IsZero X) (Y : C) :
    F.IsExtWindow a b X Y := by
  have hFX : IsZero (F.obj X) := F.map_isZero hX
  refine .of_bijective fun n ↦ ⟨fun f g _ ↦ hX.eq_of_src f g, fun g ↦ ⟨0, ?_⟩⟩
  exact hFX.eq_of_src _ _

theorem IsExtWindow.of_isZero_right {a b : ℤ} (X : C) {Y : C} (hY : IsZero Y) :
    F.IsExtWindow a b X Y := by
  have hFY : ∀ n : ℤ, IsZero ((F.obj Y)⟦n⟧) := fun n ↦
    (shiftFunctor D n).map_isZero (F.map_isZero hY)
  refine .of_bijective fun n ↦
    ⟨fun f g _ ↦ ((shiftFunctor C n).map_isZero hY).eq_of_tgt f g, fun g ↦ ⟨0, ?_⟩⟩
  exact (hFY n).eq_of_tgt _ _

/-- **The exceptional case.** If `Hom(X, Y⟦n⟧) = 0` for every `n ≠ 0`, `Hom(F X, (F Y)⟦n⟧) = 0`
for `n ≠ 0` with `a - 1 ≤ n ≤ b`, and `F` is bijective on `Hom(X, Y)`, the window condition
holds. For `X = Y = k` in graded vector spaces and `F(V) = V ⊗ S`, this is the model
`vect → ⟨S⟩`: an object `S` with `End(S) = k` and `Hom(S, S⟦n⟧) = 0` in the window degrees
`n ≠ 0`. -/
theorem IsExtWindow.of_vanishing {a b : ℤ} {X Y : C} (hX : ∀ n : ℤ, n ≠ 0 → ∀ f : X ⟶ Y⟦n⟧, f = 0)
    (hY : ∀ n : ℤ, n ≠ 0 → a ≤ n + 1 → n ≤ b → ∀ g : F.obj X ⟶ (F.obj Y)⟦n⟧, g = 0)
    (h0 : Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) :
    F.IsExtWindow a b X Y := by
  have h0' := F.map_bijective_iff_shiftedHom_zero.1 h0
  constructor
  · intro n ha hb
    rcases eq_or_ne n 0 with rfl | hn
    · exact h0'.2
    · exact fun g ↦ ⟨0, by rw [hY n hn ha hb g]; exact ShiftedHom.map_zero F⟩
  · intro n _ _
    rcases eq_or_ne n 0 with rfl | hn
    · exact h0'.1
    · exact fun f g _ ↦ (hX n hn f).trans (hX n hn g).symm

/-! #### Naturality squares -/

section Squares

variable (F)

/-- `F_n` commutes with postcomposition by `f⟦n⟧'`. -/
theorem map_rightComp_shift (X : C) {Y Y' : C} (f : Y ⟶ Y') (n : ℤ) :
    (rightComp (F.obj X) ((F.map f)⟦n⟧')).comp (ShiftedHom.mapAddHom F X Y n) =
      (ShiftedHom.mapAddHom F X Y' n).comp (rightComp X (f⟦n⟧')) := by
  ext u
  simp [ShiftedHom.map, rightComp, F.commShiftIso_hom_naturality]

/-- `F_n` commutes with precomposition. -/
theorem map_leftComp {X X' : C} (f : X ⟶ X') (Y : C) (n : ℤ) :
    (leftComp ((F.obj Y)⟦n⟧) (F.map f)).comp (ShiftedHom.mapAddHom F X' Y n) =
      (ShiftedHom.mapAddHom F X Y n).comp (leftComp (Y⟦n⟧) f) := by
  ext u
  simp [ShiftedHom.map, leftComp]

/-- `F` commutes with the connecting map `u ↦ u · T.mor₃` of the covariant sequence. -/
theorem map_rightComp_mor₃ (T : Triangle C) (X : C) (n n' : ℤ) (h : 1 + n = n') :
    (rightComp (F.obj X) ((F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁)⟦n⟧' ≫
        (shiftFunctorAdd' D 1 n n' h).inv.app (F.obj T.obj₁))).comp
        (ShiftedHom.mapAddHom F X T.obj₃ n) =
      (ShiftedHom.mapAddHom F X T.obj₁ n').comp
        (rightComp X (T.mor₃⟦n⟧' ≫ (shiftFunctorAdd' C 1 n n' h).inv.app T.obj₁)) := by
  ext u
  exact (ShiftedHom.map_comp (a := n) (b := 1) u
    (show ShiftedHom T.obj₃ T.obj₁ (1 : ℤ) from T.mor₃) h F).symm

/-- `F` commutes with the connecting map `u ↦ T.mor₃ · u` of the contravariant sequence. -/
theorem map_shiftedHomCompMor₃ (T : Triangle C) (Y : C) (m n : ℤ) (h : m + 1 = n) :
    (shiftedHomCompMor₃ (F.mapTriangle.obj T) (F.obj Y) m n h).comp
        (ShiftedHom.mapAddHom F T.obj₁ Y m) =
      (ShiftedHom.mapAddHom F T.obj₃ Y n).comp (shiftedHomCompMor₃ T Y m n h) := by
  ext u
  exact (ShiftedHom.map_comp (show ShiftedHom T.obj₃ T.obj₁ (1 : ℤ) from T.mor₃) u h F).symm

end Squares

/-! #### The dévissage steps -/

/-- **Dévissage in the second variable.** If `T₁ → T₂ → T₃ → T₁⟦1⟧` is distinguished and the
window condition holds for `(X, T₁)` and `(X, T₃)`, it holds for `(X, T₂)`. -/
theorem IsExtWindow.of_triangle_right {a b : ℤ} {X : C} (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : F.IsExtWindow a b X T.obj₁) (h₃ : F.IsExtWindow a b X T.obj₃) :
    F.IsExtWindow a b X T.obj₂ := by
  have hFT := F.map_distinguished T hT
  constructor
  · intro n ha hb
    exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective _ _ _ _ _ _
      (ShiftedHom.mapAddHom F X T.obj₁ n) (ShiftedHom.mapAddHom F X T.obj₂ n)
      (ShiftedHom.mapAddHom F X T.obj₃ n) (ShiftedHom.mapAddHom F X T.obj₁ (n + 1))
      (F.map_rightComp_shift X T.mor₁ n) (F.map_rightComp_shift X T.mor₂ n)
      (F.map_rightComp_mor₃ T X n (n + 1) (add_comm 1 n))
      (exact_rightComp_shift_mor₂ T hT X n (n + 1) (add_comm 1 n))
      (exact_rightComp_shift_mor₁ _ hFT (F.obj X) n)
      (exact_rightComp_shift_mor₂ _ hFT (F.obj X) n (n + 1) (add_comm 1 n))
      (h₁.surjective n ha hb) (h₃.surjective n ha hb) (h₁.injective (n + 1) ha (by lia))
  · intro n ha hb
    exact AddMonoidHom.injective_of_surjective_of_injective_of_injective _ _ _ _ _ _
      (ShiftedHom.mapAddHom F X T.obj₃ (n - 1)) (ShiftedHom.mapAddHom F X T.obj₁ n)
      (ShiftedHom.mapAddHom F X T.obj₂ n) (ShiftedHom.mapAddHom F X T.obj₃ n)
      (F.map_rightComp_mor₃ T X (n - 1) n (by lia))
      (F.map_rightComp_shift X T.mor₁ n) (F.map_rightComp_shift X T.mor₂ n)
      (exact_rightComp_shift_mor₃ T hT X (n - 1) n (by lia))
      (exact_rightComp_shift_mor₁ T hT X n)
      (exact_rightComp_shift_mor₃ _ hFT (F.obj X) (n - 1) n (by lia))
      (h₃.surjective (n - 1) (by lia) (by lia)) (h₁.injective n ha hb) (h₃.injective n ha hb)


/-- **Dévissage in the first variable.** If `T₁ → T₂ → T₃ → T₁⟦1⟧` is distinguished and the
window condition holds for `(T₁, Y)` and `(T₃, Y)`, it holds for `(T₂, Y)`. -/
theorem IsExtWindow.of_triangle_left {a b : ℤ} {Y : C} (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : F.IsExtWindow a b T.obj₁ Y) (h₃ : F.IsExtWindow a b T.obj₃ Y) :
    F.IsExtWindow a b T.obj₂ Y := by
  have hFT := F.map_distinguished T hT
  constructor
  · intro n ha hb
    exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective _ _ _ _ _ _
      (ShiftedHom.mapAddHom F T.obj₃ Y n) (ShiftedHom.mapAddHom F T.obj₂ Y n)
      (ShiftedHom.mapAddHom F T.obj₁ Y n) (ShiftedHom.mapAddHom F T.obj₃ Y (n + 1))
      (F.map_leftComp T.mor₂ Y n) (F.map_leftComp T.mor₁ Y n)
      (F.map_shiftedHomCompMor₃ T Y n (n + 1) rfl)
      (exact_leftComp_shiftedHomCompMor₃ T hT Y n (n + 1) rfl)
      (exact_leftComp_mor₂ _ hFT ((F.obj Y)⟦n⟧))
      (exact_leftComp_shiftedHomCompMor₃ _ hFT (F.obj Y) n (n + 1) rfl)
      (h₃.surjective n ha hb) (h₁.surjective n ha hb) (h₃.injective (n + 1) ha (by lia))
  · intro n ha hb
    exact AddMonoidHom.injective_of_surjective_of_injective_of_injective _ _ _ _ _ _
      (ShiftedHom.mapAddHom F T.obj₁ Y (n - 1)) (ShiftedHom.mapAddHom F T.obj₃ Y n)
      (ShiftedHom.mapAddHom F T.obj₂ Y n) (ShiftedHom.mapAddHom F T.obj₁ Y n)
      (F.map_shiftedHomCompMor₃ T Y (n - 1) n (by lia))
      (F.map_leftComp T.mor₂ Y n) (F.map_leftComp T.mor₁ Y n)
      (exact_shiftedHomCompMor₃_leftComp T hT Y (n - 1) n (by lia))
      (exact_leftComp_mor₂ T hT (Y⟦n⟧))
      (exact_shiftedHomCompMor₃_leftComp _ hFT (F.obj Y) (n - 1) n (by lia))
      (h₁.surjective (n - 1) (by lia) (by lia)) (h₃.injective n ha hb) (h₁.injective n ha hb)

/-! #### Window dévissage -/

variable {P : ObjectProperty C} {a b : ℤ}

/-- **Window dévissage.** If the window condition `W_{a,b}` holds on all pairs of objects of `P`,
it holds on all pairs of objects of the extension closure of `P`. -/
theorem isExtWindow_of_extensionClosure (h : ∀ ⦃S T : C⦄, P S → P T → F.IsExtWindow a b S T)
    ⦃X Y : C⦄ (hX : P.extensionClosure X) (hY : P.extensionClosure Y) :
    F.IsExtWindow a b X Y := by
  have hright : ∀ ⦃S : C⦄, P S → ∀ ⦃Y : C⦄, P.extensionClosure Y → F.IsExtWindow a b S Y := by
    intro S hS Y hY
    induction hY with
    | of_prop hY => exact h hS hY
    | of_isZero hY => exact .of_isZero_right S hY
    | ext T hT _ _ h₁ h₃ => exact .of_triangle_right T hT h₁ h₃
  induction hX with
  | of_prop hX => exact hright hX hY
  | of_isZero hX => exact .of_isZero_left hX Y
  | ext T hT _ _ h₁ h₃ => exact .of_triangle_left T hT h₁ h₃

/-- **Full faithfulness from window dévissage.** If `a ≤ 0 ≤ b` and the window condition holds
on `P`, the restriction of `F` to the extension closure of `P` is fully faithful. -/
def fullyFaithfulOfIsExtWindow (ha : a ≤ 0) (hb : 0 ≤ b)
    (h : ∀ ⦃S T : C⦄, P S → P T → F.IsExtWindow a b S T) :
    (P.extensionClosure.ι ⋙ F).FullyFaithful :=
  haveI : (P.extensionClosure.ι ⋙ F).Full := ⟨fun {X Y} g ↦ by
    obtain ⟨f, hf⟩ :=
      ((isExtWindow_of_extensionClosure h X.2 Y.2).map_bijective ha hb).2 g
    exact ⟨ObjectProperty.homMk f, hf⟩⟩
  haveI : (P.extensionClosure.ι ⋙ F).Faithful := ⟨fun {X Y} f g hfg ↦ ObjectProperty.hom_ext _
    (((isExtWindow_of_extensionClosure h X.2 Y.2).map_bijective ha hb).1 hfg)⟩
  .ofFullyFaithful _

variable (F) in
/-- A triangulated functor maps the extension closure of `P` into the extension closure of the
objects `F S`, `S ∈ P`. -/
theorem map_extensionClosure_le (P : ObjectProperty C) :
    P.extensionClosure.map F ≤ (P.map F).extensionClosure := by
  rintro Y ⟨X, hX, ⟨e⟩⟩
  refine ObjectProperty.extensionClosure_of_iso _ e ?_
  clear e
  induction hX with
  | of_prop hX => exact .of_prop ⟨_, hX, ⟨Iso.refl _⟩⟩
  | of_isZero hX => exact .of_isZero (F.map_isZero hX)
  | ext T hT _ _ h₁ h₃ => exact .ext _ (F.map_distinguished T hT) h₁ h₃

/-- **The essential image.** If `a ≤ 2` and `1 ≤ b`, so that `F_1` is surjective on the
extension closure, the objects `F X` for `X` in the extension closure of `P` are, up to
isomorphism, the extension closure of the objects `F S`, `S ∈ P`. -/
theorem map_extensionClosure_eq (ha : a ≤ 2) (hb : 1 ≤ b)
    (h : ∀ ⦃S T : C⦄, P S → P T → F.IsExtWindow a b S T) :
    P.extensionClosure.map F = (P.map F).extensionClosure := by
  refine le_antisymm (F.map_extensionClosure_le P) ?_
  · intro Y hY
    induction hY with
    | of_prop hY =>
      obtain ⟨X, hX, ⟨e⟩⟩ := hY
      exact ⟨X, .of_prop hX, ⟨e⟩⟩
    | of_isZero hY =>
      exact ⟨0, .of_isZero (isZero_zero C), ⟨(F.map_isZero (isZero_zero C)).iso hY⟩⟩
    | ext T hT _ _ h₁ h₃ =>
      obtain ⟨X₁, hX₁, ⟨e₁⟩⟩ := h₁
      obtain ⟨X₃, hX₃, ⟨e₃⟩⟩ := h₃
      obtain ⟨u, hu⟩ := (isExtWindow_of_extensionClosure h hX₃ hX₁).surjective 1 ha hb
        (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧')
      replace hu : F.map u ≫ (F.commShiftIso (1 : ℤ)).hom.app X₁ =
          e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' := hu
      obtain ⟨X₂, f, g, hT'⟩ := distinguished_cocone_triangle₂ u
      have hFT' := F.map_distinguished _ hT'
      have comm : (F.mapTriangle.obj (Triangle.mk f g u)).mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' =
          e₃.hom ≫ T.mor₃ := by
        dsimp
        rw [hu]
        simp [← Functor.map_comp]
      obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism₂ _ _ hFT' hT
        e₁.hom e₃.hom comm
      let φ : F.mapTriangle.obj (Triangle.mk f g u) ⟶ T :=
        { hom₁ := e₁.hom, hom₂ := c, hom₃ := e₃.hom, comm₁ := hc₁, comm₂ := hc₂, comm₃ := comm }
      have : IsIso φ.hom₂ := isIso₂_of_isIso₁₃ φ hFT' hT (by dsimp [φ]; infer_instance)
        (by dsimp [φ]; infer_instance)
      exact ⟨X₂, .ext _ hT' hX₁ hX₃, ⟨asIso φ.hom₂⟩⟩

end Functor

end CategoryTheory
