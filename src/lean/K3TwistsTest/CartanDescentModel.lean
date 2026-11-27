/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.TorsionTheory.CartanDescent
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# A consistency model for Cartan descent

The fields of `CategoryTheory.Abelian.CartanDescentHypotheses` hold together, with an integer
certificate, in finite-dimensional vector spaces over a field `k` (`FGModuleCat k`): one vertex,
`Q j = k` for every `j`, `κ = 0` and `A = (1)`.

* `Hom` spaces are finite dimensional. Every object is projective: it is a projective module, and
  the inclusion into `ModuleCat k` is fully faithful and preserves epimorphisms. So `Ext¹ = 0`.
* The identity embeds `Q j = k` in `Q 0 = k`.
* A nonzero morphism to the line `k` is onto, so it is an epimorphism and its image is `k`.
* `hom(k, k) - ext¹(k, k) ≥ 1 - 0 = A`.

The certificate `p = 1` then gives the torsion pair (`torsionTheory`). Here every nonzero space
maps onto `k`, so the torsion class is trivial; the model only shows that the fields can hold
together with a certificate. A geometric instance needs the derived category of a K3 surface
and its hearts, which the library does not have.

Built by `lake test`.
-/

namespace CartanDescentModel

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Module Matrix

universe u

variable (k : Type u) [Field k]

noncomputable instance : HasExt.{u + 1} (FGModuleCat.{u} k) :=
  HasExt.standard _

/-- The line `k`. -/
abbrev line : FGModuleCat.{u} k :=
  FGModuleCat.of k k

/-- Every finite-dimensional space is a projective object of `FGModuleCat k`. -/
instance projective (V : FGModuleCat.{u} k) : Projective V :=
  (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).projective_of_map_projective inferInstance

variable {k} in
/-- A nonzero morphism to the line is an epimorphism. -/
theorem epi_of_ne_zero {Y : FGModuleCat.{u} k} (f : Y ⟶ line k) (hf : f ≠ 0) : Epi f := by
  obtain ⟨y, hy⟩ : ∃ y, f.hom.hom y ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (by ext y; simpa using h y)
  apply (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).epi_of_epi_map
  rw [ModuleCat.epi_iff_surjective]
  intro c
  let c' : k := c
  let a : k := f.hom.hom y
  have ha : a ≠ 0 := hy
  refine ⟨(c' / a) • y, ?_⟩
  change f.hom.hom ((c' / a) • y) = c
  rw [map_smul]
  change c' / a * a = c'
  exact div_mul_cancel₀ c' ha

/-- **The fields hold**: one vertex, `Q j = k`, `κ = 0`, `A = (1)`. -/
theorem hypotheses :
    CartanDescentHypotheses k (fun (_ : Unit) (_ : ℤ) => line k) (fun _ => 0) 1 where
  finiteDimensional_hom _ _ := inferInstance
  finiteDimensional_ext _ _ _ _ := by
    have := Ext.subsingleton_of_projective (line k) (line k) 0
    infer_instance
  exists_mono _ _ _ := ⟨𝟙 _, inferInstance⟩
  exists_image_iso Y _ f hf := by
    have := epi_of_ne_zero f hf
    have := epi_image_of_epi f
    have := isIso_of_mono_of_epi (Limits.image.ι f)
    exact ⟨0, le_rfl, ⟨asIso (Limits.image.ι f)⟩⟩
  cartan_le_hom_sub_ext _ _ _ _ := by
    have := Ext.subsingleton_of_projective (line k) (line k) 0
    have hid : (𝟙 (line k) : line k ⟶ line k) ≠ 0 := by
      intro h
      have h1 := congrArg (fun g : line k ⟶ line k => g.hom.hom (1 : k)) h
      simp at h1
    have := nontrivial_of_ne _ _ hid
    have hpos : 0 < finrank k (line k ⟶ line k) := Module.finrank_pos
    simp only [Matrix.one_apply_eq, Module.finrank_zero_of_subsingleton, Nat.cast_zero, sub_zero]
    omega

/-- **The torsion pair of the model**, from the certificate `p = 1`. -/
theorem torsionTheory :
    TorsionTheory
      (CartanDescentHypotheses.torsionFreeClass (fun (_ : Unit) (_ : ℤ) => line k)
        (fun _ => 0)).leftOrthogonal
      (CartanDescentHypotheses.torsionFreeClass (fun (_ : Unit) (_ : ℤ) => line k)
        (fun _ => 0)) :=
  (hypotheses k).torsionTheory (p := fun _ => 1) (fun _ => zero_le_one) fun _ => by
    simp [Matrix.mulVec, dotProduct]

/-- **The model through positive definiteness**: `A = (1)` is a positive definite symmetric
Z-matrix. -/
example :
    TorsionTheory
      (CartanDescentHypotheses.torsionFreeClass (fun (_ : Unit) (_ : ℤ) => line k)
        (fun _ => 0)).leftOrthogonal
      (CartanDescentHypotheses.torsionFreeClass (fun (_ : Unit) (_ : ℤ) => line k)
        (fun _ => 0)) :=
  (hypotheses k).torsionTheory_of_posDef (fun i j hij => absurd (Subsingleton.elim i j) hij)
    Matrix.isSymm_one <| Matrix.isSymm_one.posDef_iff_dotProduct_mulVec_pos.2 fun x hx => by
      have h0 : x () ≠ 0 := fun h0 => hx (funext fun u => by cases u; exact h0)
      simpa [dotProduct] using mul_self_pos.2 h0

end CartanDescentModel
