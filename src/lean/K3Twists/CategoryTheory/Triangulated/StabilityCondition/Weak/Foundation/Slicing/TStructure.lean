/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Evaluation
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.FiltrationOperations
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
# The t-structure of a slicing

A slicing `s` of a triangulated category and a real number `a` give a bounded t-structure in
the cohomological convention of Mathlib's `Triangulated.TStructure`: the aisle `≤ n` is
`P(> a - n)` and the coaisle `≥ n` is `P(≤ a + 1 - n)`. Its heart is the half-open phase
interval `P((a, a+1])` (Bridgeland, *Stability conditions on triangulated categories*,
arXiv:math/0212237, §3).

## Main definitions

* `Slicing.heartProp s a`: the half-open predicate `P((a, a+1]) = P(> a) ⊓ P(≤ a + 1)`;
  `Slicing.HeartCat s a` is its full subcategory.
* `Slicing.toTStructure s a`: the t-structure with aisle `P(> a)` and coaisle `P(≤ a + 1)`.

## Main results

* `Slicing.exists_distTriang_gtProp_leProp`: every object `A` sits in a distinguished triangle
  `X → A → Y → X⟦1⟧` with `X` of phases `> t` and `Y` of phases `≤ t` (the HN filtration of `A`
  cut at `t`).
* `Slicing.toTStructure_heart`: the heart of `s.toTStructure a` is `s.heartProp a`, and
  `Slicing.instHeartHeartCat` makes `s.HeartCat a` the heart in the sense of
  `TStructure.Heart`.
* `Slicing.toTStructure_bounded`: the t-structure is bounded: every object lies in some
  `≤ n` and some `≥ m`.
* `Slicing.heartProp_of_semistable`, `Slicing.intervalProp_le_heartProp`: semistable objects of
  phase in `(a, a+1]` and the open interval `P((a, a+1))` lie in the heart.

## Implementation notes

The heart is not the thin interval category `s.IntervalCat a (a+1)`: that is the open interval
`P((a, a+1))`, which omits the phase `a + 1` and is not abelian in general. The heart needs the
half-open predicate defined here.

## Tags

slicing, t-structure, heart, stability condition
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### The half-open predicate -/

/-- The half-open phase interval `P((a, a+1])`: objects all of whose HN phases lie in
`(a, a+1]`. It is the heart of `s.toTStructure a` (`Slicing.toTStructure_heart`). -/
def Slicing.heartProp (s : Slicing C) (a : ℝ) : ObjectProperty C :=
  s.gtProp C a ⊓ s.leProp C (a + 1)

/-- The full subcategory `P((a, a+1])`, the heart of `s.toTStructure a`. -/
abbrev Slicing.HeartCat (s : Slicing C) (a : ℝ) :=
  (s.heartProp C a).FullSubcategory

theorem Slicing.heartProp_iff (s : Slicing C) (a : ℝ) (E : C) :
    s.heartProp C a E ↔ s.gtProp C a E ∧ s.leProp C (a + 1) E :=
  Iff.rfl

instance Slicing.heartProp_isClosedUnderIsomorphisms (s : Slicing C) (a : ℝ) :
    (s.heartProp C a).IsClosedUnderIsomorphisms := by
  dsimp [Slicing.heartProp]
  infer_instance

theorem Slicing.heartProp_of_isZero (s : Slicing C) {E : C} (hE : IsZero E) (a : ℝ) :
    s.heartProp C a E :=
  ⟨Or.inl hE, Or.inl hE⟩

instance Slicing.heartProp_containsZero (s : Slicing C) (a : ℝ) :
    (s.heartProp C a).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, s.heartProp_of_isZero C (isZero_zero C) a⟩

/-- An object with an HN filtration whose phases all lie in `(a, a+1]` is in the heart. -/
theorem Slicing.heartProp_of_hn (s : Slicing C) {a : ℝ} {E : C} (F : HNFiltration C s.P E)
    (hF : ∀ i, a < F.φ i ∧ F.φ i ≤ a + 1) : s.heartProp C a E := by
  by_cases hn : 0 < F.n
  · exact ⟨s.gtProp_of_hn C F a (fun i => (hF i).1) hn,
      s.leProp_of_hn C F (a + 1) (fun i => (hF i).2) hn⟩
  · exact s.heartProp_of_isZero C (F.isZero_of_length_zero (by omega)) a

/-- A semistable object of phase in `(a, a+1]` is in the heart. -/
theorem Slicing.heartProp_of_semistable (s : Slicing C) {a φ : ℝ} {E : C} (hE : s.P φ E)
    (h₁ : a < φ) (h₂ : φ ≤ a + 1) : s.heartProp C a E :=
  ⟨s.gtProp_of_semistable C hE h₁, s.leProp_of_semistable C hE h₂⟩

/-- The open interval `P((a, a+1))` lies in the heart `P((a, a+1])`. -/
theorem Slicing.intervalProp_le_heartProp (s : Slicing C) (a : ℝ) :
    s.intervalProp C a (a + 1) ≤ s.heartProp C a :=
  fun _ hE => ⟨s.gtProp_of_intervalProp C hE,
    s.leProp_of_ltProp C _ (s.ltProp_of_intervalProp C hE)⟩

/-- Shifting by `n` moves the heart at `a` to the heart at `a + n`. -/
theorem Slicing.heartProp_shift (s : Slicing C) (a : ℝ) (E : C) (n : ℤ)
    (hE : s.heartProp C a E) : s.heartProp C (a + n) (E⟦n⟧) := by
  refine ⟨s.gtProp_shift C a E n hE.1, ?_⟩
  have h := s.leProp_shift C (a + 1) E n hE.2
  rwa [add_right_comm] at h

/-! ### Phase truncation -/

/-- **Phase truncation.** Every object `A` sits in a distinguished triangle `X → A → Y → X⟦1⟧`
with `X` of phases `> t` and `Y` of phases `≤ t`: the HN filtration of `A` cut at `t`. -/
theorem Slicing.exists_distTriang_gtProp_leProp [IsTriangulated C] (s : Slicing C) (t : ℝ)
    (A : C) : ∃ (X Y : C) (_ : s.gtProp C t X) (_ : s.leProp C t Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨F⟩ := s.hn_exists A
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, -, -⟩ := F.exists_split_at_cutoff C t
  have hX : s.gtProp C t X := by
    by_cases hn : 0 < GX.n
    · exact s.gtProp_of_hn C GX t hGX hn
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  have hY : s.leProp C t Y := by
    by_cases hn : 0 < GY.n
    · exact s.leProp_of_hn C GY t hGY hn
    · exact Or.inl (GY.isZero_of_length_zero (by omega))
  exact ⟨X, Y, hX, hY, f, g, h, hT⟩

/-! ### The t-structure -/

/-- **The t-structure of a slicing** at `a ∈ ℝ`, in Mathlib's cohomological convention: an
object is `≤ n` when its phases are `> a - n` and `≥ n` when its phases are `≤ a + 1 - n`. Its
heart is `P((a, a+1])` (`Slicing.toTStructure_heart`). -/
def Slicing.toTStructure [IsTriangulated C] (s : Slicing C) (a : ℝ) : TStructure C where
  le n := s.gtProp C (a - n)
  ge n := s.leProp C (a + 1 - n)
  le_isClosedUnderIsomorphisms _ := inferInstance
  ge_isClosedUnderIsomorphisms _ := inferInstance
  le_shift n k n' h X hX := by
    have phase : a - (n' : ℝ) = a - n + k := by
      have : (k : ℝ) + n' = n := by exact_mod_cast h
      linarith
    rw [phase]
    exact s.gtProp_shift C _ X k hX
  ge_shift n k n' h X hX := by
    have phase : a + 1 - (n' : ℝ) = a + 1 - n + k := by
      have : (k : ℝ) + n' = n := by exact_mod_cast h
      linarith
    rw [phase]
    exact s.leProp_shift C _ X k hX
  zero' {X Y} f hX hY :=
    Slicing.hom_eq_zero_of_gtProp_leProp s (t := a) (by simpa using hX)
      (by simpa [add_sub_cancel_right] using hY) f
  le_zero_le := by
    simpa using s.gtProp_anti C (show a - 1 ≤ a by linarith)
  ge_one_le := by
    simpa using s.leProp_mono C (show a ≤ a + 1 by linarith)
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := s.exists_distTriang_gtProp_leProp C a A
    exact ⟨X, Y, by simpa using hX, by simpa using hY, f, g, h, hT⟩

variable [IsTriangulated C]

@[simp]
theorem Slicing.toTStructure_le (s : Slicing C) (a : ℝ) (n : ℤ) :
    (s.toTStructure C a).le n = s.gtProp C (a - n) :=
  rfl

@[simp]
theorem Slicing.toTStructure_ge (s : Slicing C) (a : ℝ) (n : ℤ) :
    (s.toTStructure C a).ge n = s.leProp C (a + 1 - n) :=
  rfl

theorem Slicing.toTStructure_isLE_iff (s : Slicing C) (a : ℝ) (E : C) (n : ℤ) :
    (s.toTStructure C a).IsLE E n ↔ s.gtProp C (a - n) E :=
  ⟨fun h => h.le, fun h => ⟨h⟩⟩

theorem Slicing.toTStructure_isGE_iff (s : Slicing C) (a : ℝ) (E : C) (n : ℤ) :
    (s.toTStructure C a).IsGE E n ↔ s.leProp C (a + 1 - n) E :=
  ⟨fun h => h.ge, fun h => ⟨h⟩⟩

/-- The heart of the t-structure of a slicing at `a` is the half-open interval
`P((a, a+1])`. -/
theorem Slicing.toTStructure_heart (s : Slicing C) (a : ℝ) :
    (s.toTStructure C a).heart = s.heartProp C a := by
  simp [TStructure.heart, Slicing.heartProp]

theorem Slicing.toTStructure_mem_heart_iff (s : Slicing C) (a : ℝ) (E : C) :
    (s.toTStructure C a).heart E ↔ s.heartProp C a E := by
  rw [Slicing.toTStructure_heart]

/-- The full subcategory `P((a, a+1])` is the heart of `s.toTStructure a`. -/
instance Slicing.instHeartHeartCat (s : Slicing C) (a : ℝ) :
    (s.toTStructure C a).Heart (s.HeartCat C a) where
  ι := (s.heartProp C a).ι
  essImage_eq_heart := by
    rw [Slicing.toTStructure_heart]
    ext X
    exact ⟨fun ⟨⟨Y, hY⟩, ⟨e⟩⟩ => (s.heartProp C a).prop_of_iso e hY,
      fun hX => ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩⟩

@[simp]
theorem Slicing.toTStructure_ιHeart (s : Slicing C) (a : ℝ) :
    (s.toTStructure C a).ιHeart (H := s.HeartCat C a) = (s.heartProp C a).ι :=
  rfl

/-- **Boundedness.** The t-structure of a slicing is bounded: an object with HN phases in
`[φ⁻, φ⁺]` is `≤ n` for `n > a - φ⁻` and `≥ m` for `m ≤ a + 1 - φ⁺`. -/
theorem Slicing.toTStructure_bounded (s : Slicing C) (a : ℝ) (E : C) :
    (s.toTStructure C a).bounded E := by
  by_cases hE : IsZero E
  · exact ⟨⟨0, ⟨Or.inl hE⟩⟩, ⟨0, ⟨Or.inl hE⟩⟩⟩
  obtain ⟨F⟩ := s.hn_exists E
  have hn : 0 < F.n := by
    by_contra h
    exact hE (F.isZero_of_length_zero (by omega))
  refine ⟨⟨⌊a + 1 - F.phiPlus C hn⌋, ⟨Or.inr ⟨F, hn, ?_⟩⟩⟩,
    ⟨⌈a - F.phiMinus C hn⌉ + 1, ⟨Or.inr ⟨F, hn, ?_⟩⟩⟩⟩
  · linarith [Int.floor_le (a + 1 - F.phiPlus C hn)]
  · push_cast
    linarith [Int.le_ceil (a - F.phiMinus C hn)]

end CategoryTheory.Triangulated
