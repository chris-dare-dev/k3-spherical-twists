/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.Subobject.Valuation
import K3Twists.CategoryTheory.Abelian.TorsionTheory.Radical
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Heart

/-!
# Radicals, interval classes and charge functions on the heart of a slicing

The abelian layers of the library (interval classes and saturation, radicals as coreflections,
charge functions on subobject lattices) apply to the heart `P((a, a+1])` of a slicing.

## Main results

For any slicing:

* `Slicing.isCoreflection_heartTop`, `Slicing.exists_isGreatest_heartTop`,
  `Slicing.isLeftAdjoint_ι_heartTop`: every object `R` of the heart has a radical for `P(a+1)`,
  the largest subobject of `R` of phase `a + 1`; it is the first term of the torsion sequence of
  `R`, and it is a coreflection. No chain condition on `R` is needed: the HN filtration of `R`
  provides it. `Slicing.isCoreflection_heartAbove` does the same for an interior cut.
* `P(a+1)` contains zero and is closed under quotients and extensions in the heart (it is a
  torsion class), so `(s.heartTop a).intervalClass R` is an interval class on `Subobject R`;
  `Slicing.isGreatest_intervalClass_rad_heartTop` is its radical on a Noetherian object.

Given a prestability condition:

* `PreStabilityCondition.WithClassMap.intervalClass_heartTop_hereditary`: that interval class is
  hereditary, and `isGreatest_inf_heartTop` is the restriction formula `t(A) = A ⊓ t(R)` for
  every subobject `A`, with no chain condition.
* `PreStabilityCondition.WithClassMap.heartChargeFunction`: `rk = Im Z` and `deg = -Re Z` form a
  charge function on the subobjects of an object of `P((0, 1])`; the subobject lattices of the
  heart are modular (`isModularLattice_subobject_heart`), and HN filtrations of subobjects exist on
  Noetherian objects whose maximal phase is attained (`nonempty_hnFiltration_heart`).

## Scope

Whether the hearts `P((a, a+1])` of the stability conditions of interest are Noetherian is not
known here. The radical of `P(a+1)` exists without it, as above, but the saturation of the
interval class and the HN filtrations of subobjects are stated on Noetherian objects only.

## Tags

heart, radical, coreflection, interval class, charge function, torsion class
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### The radical of `P(a+1)`, for any slicing -/

/-- In the heart, the objects of phase `a + 1` form a torsion class. -/
instance Slicing.isTorsionClass_heartTop (s : Slicing C) (a : ℝ) :
    Abelian.IsTorsionClass (s.heartTop C a) :=
  (s.torsionTheory_heartTop C a).isTorsionClass

instance Slicing.heartTop_containsZero (s : Slicing C) (a : ℝ) :
    (s.heartTop C a).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, s.zero_mem_of_isZero C _ _
    ((s.heartProp C a).ι.map_isZero (isZero_zero _))⟩

/-- **The radical of `P(a+1)` exists**, for any slicing and any object `R` of the heart: the
first term `D ↪ R` of the torsion sequence of `R` is a monic coreflection of `R` into `P(a+1)`. -/
theorem Slicing.isCoreflection_heartTop (s : Slicing C) (a : ℝ) (R : s.HeartCat C a) :
    ∃ (D : s.HeartCat C a) (ε : D ⟶ R), Mono ε ∧ (s.heartTop C a).IsCoreflection ε := by
  obtain ⟨X₁, X₃, i, p, w, hS, h₁, h₃⟩ := s.exists_shortExact_heartTop C a R
  exact ⟨X₁, i, hS.mono_f, ObjectProperty.isCoreflection_of_shortExact hS h₁
    fun _ f hY => s.heartTop_hom_heartFree_eq_zero C f hY h₃⟩

/-- Every object of the heart has a largest subobject of phase `a + 1`. -/
theorem Slicing.exists_isGreatest_heartTop (s : Slicing C) (a : ℝ) (R : s.HeartCat C a) :
    ∃ t : Subobject R, IsGreatest {A : Subobject R | s.heartTop C a (A : s.HeartCat C a)} t := by
  obtain ⟨D, ε, _, h⟩ := s.isCoreflection_heartTop C a R
  exact ⟨_, h.isGreatest⟩

/-- The inclusion of `P(a+1)` into the heart is a left adjoint: its right adjoint is the
radical. -/
theorem Slicing.isLeftAdjoint_ι_heartTop (s : Slicing C) (a : ℝ) :
    (s.heartTop C a).ι.IsLeftAdjoint :=
  ObjectProperty.isLeftAdjoint_ι_iff.2 fun R => by
    obtain ⟨D, ε, -, h⟩ := s.isCoreflection_heartTop C a R
    exact ⟨D, ε, h⟩

/-- The radical of an interior cut: for `θ ∈ [a, a+1]`, every object of the heart has a monic
coreflection into the objects of phases in `(θ, a+1]`. -/
theorem Slicing.isCoreflection_heartAbove (s : Slicing C) {a θ : ℝ} (h₁ : a ≤ θ)
    (h₂ : θ ≤ a + 1) (R : s.HeartCat C a) :
    ∃ (D : s.HeartCat C a) (ε : D ⟶ R), Mono ε ∧ (s.heartAbove C a θ).IsCoreflection ε := by
  obtain ⟨X₁, X₃, i, p, w, hS, hX₁, hX₃⟩ := s.exists_shortExact_heartAbove C h₁ h₂ R
  exact ⟨X₁, i, hS.mono_f, ObjectProperty.isCoreflection_of_shortExact hS hX₁
    fun _ f hY => ObjectProperty.hom_ext _ (Slicing.hom_eq_zero_of_gtProp_leProp s hY hX₃ _)⟩

/-- On a Noetherian object of the heart, the radical of the interval class of `P(a+1)` is the
largest subobject of phase `a + 1`. -/
theorem Slicing.isGreatest_intervalClass_rad_heartTop (s : Slicing C) (a : ℝ)
    (R : s.HeartCat C a) [IsNoetherianObject R] :
    IsGreatest {A : Subobject R | s.heartTop C a (A : s.HeartCat C a)}
      ((s.heartTop C a).intervalClass R).rad :=
  ObjectProperty.isGreatest_intervalClass_rad R

/-! ### Given a prestability condition -/

namespace PreStabilityCondition.WithClassMap

variable {C} {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- The interval class of `P(a+1)` on the subobjects of an object of the heart of a
prestability condition is hereditary. -/
theorem intervalClass_heartTop_hereditary (σ : WithClassMap C v) (a : ℝ)
    (R : σ.slicing.HeartCat C a) : ((σ.slicing.heartTop C a).intervalClass R).Hereditary :=
  have := σ.heartTop_hereditary a
  ObjectProperty.intervalClass_hereditary R

/-- **The restriction formula** `t(A) = A ⊓ t(R)` in the heart of a prestability condition, for
every subobject `A` of every object `R`, with no chain condition: `A ⊓ t(R)` is the largest
subobject of `R` below `A` of phase `a + 1`. -/
theorem isGreatest_inf_heartTop (σ : WithClassMap C v) (a : ℝ) {R : σ.slicing.HeartCat C a}
    {t : Subobject R}
    (ht : IsGreatest {A : Subobject R | σ.slicing.heartTop C a (A : σ.slicing.HeartCat C a)} t)
    (A : Subobject R) :
    IsGreatest {B : Subobject R | B ≤ A ∧ σ.slicing.heartTop C a (B : σ.slicing.HeartCat C a)}
      (A ⊓ t) := by
  have := σ.heartTop_hereditary a
  exact ⟨⟨inf_le_left, (σ.slicing.heartTop C a).prop_of_mono
      (Subobject.ofLE _ _ inf_le_right) ht.1⟩,
    fun B ⟨hBA, hB⟩ => le_inf hBA (ht.2 hB)⟩

omit [IsTriangulated C] in
theorem charge_ne_zero_of_heartProp (σ : WithClassMap C v) {E : C}
    (hE : σ.slicing.heartProp C 0 E) (hZ : ¬IsZero E) : σ.charge E ≠ 0 := fun h => by
  rcases σ.charge_mem_of_heartProp hE hZ with h' | ⟨-, h'⟩ <;> simp [h] at h'

/-- The central charge is additive on short exact sequences of the heart. -/
theorem charge_add_of_shortExact (σ : WithClassMap C v) {a : ℝ}
    {S : ShortComplex (σ.slicing.HeartCat C a)} (hS : S.ShortExact) :
    σ.charge S.X₂.obj = σ.charge S.X₁.obj + σ.charge S.X₃.obj := by
  change σ.Z (v (K₀.of C S.X₂.obj)) = σ.Z (v (K₀.of C S.X₁.obj)) + σ.Z (v (K₀.of C S.X₃.obj))
  rw [Slicing.HeartCat.K₀_of_shortExact C hS, map_add, map_add]

/-- **The charge function of the heart.** On the subobjects of an object `X` of `P((0, 1])`,
`rk = Im Z` and `deg = -Re Z` form a charge function: `Z` is a stability function on the heart,
and the subobjects of phase one (`Im Z = 0`) give the vertical steps. -/
def heartChargeFunction (σ : WithClassMap C v) (X : σ.slicing.HeartCat C 0) :
    Order.ChargeFunction (Subobject X) ℝ :=
  Subobject.chargeFunction (rk := fun E => (σ.charge E.obj).im)
    (deg := fun E => -(σ.charge E.obj).re)
    (fun _ hS => by simp only [σ.charge_add_of_shortExact hS, Complex.add_im])
    (fun _ hS => by simp only [σ.charge_add_of_shortExact hS, Complex.add_re]; ring)
    (fun E hE => by
      have hE' : ¬IsZero E.obj := fun h => hE (Slicing.HeartCat.isZero_of_obj_isZero C h)
      rcases σ.charge_mem_of_heartProp E.property hE' with h | ⟨h, h'⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by linarith⟩) X

/-- The subobject lattices of the heart `P((0, 1])` of a prestability condition are modular. -/
theorem isModularLattice_subobject_heart (σ : WithClassMap C v) (X : σ.slicing.HeartCat C 0) :
    IsModularLattice (Subobject X) :=
  Subobject.isModularLattice_of_additive (Z := fun E : σ.slicing.HeartCat C 0 => σ.charge E.obj)
    (fun _ hS => σ.charge_add_of_shortExact hS)
    (fun Y hY => by
      by_contra hYZ
      exact σ.charge_ne_zero_of_heartProp Y.property
        (fun h => hYZ (Slicing.HeartCat.isZero_of_obj_isZero C h)) hY) X

/-- Harder–Narasimhan filtrations of the subobjects of a Noetherian object of `P((0, 1])` whose
maximal phase is attained on every interval: they exist (and are unique). -/
theorem nonempty_hnFiltration_heart (σ : WithClassMap C v) (X : σ.slicing.HeartCat C 0)
    [IsNoetherianObject X] (hatt : (σ.heartChargeFunction X).MaxPhaseAttained) :
    Nonempty (σ.heartChargeFunction X).HNFiltration :=
  Subobject.nonempty_hnFiltration _ _ _ X hatt

end PreStabilityCondition.WithClassMap

end CategoryTheory.Triangulated
