/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import K3Twists.Algebra.PoincareParity
import K3Twists.CategoryTheory.MassProfile.Basic

/-!
# Fibre-functor profiles

For an exact functor `F` from a triangulated category to graded vector spaces, an object `E` has
the Poincaré polynomial `P_E(t) = Σ_j dim Hʲ(F E) tʲ`. Its value at `t = 1` is the profile
`μ_F(E) = Σ_j dim Hʲ(F E)`; its value at `t = -1` is the Euler characteristic, which is additive
on triangles and so factors through classes: in a lattice with a form `⟨-, -⟩` and Mukai's sign,
`χ_F(E) = -⟨w_F, v(E)⟩` for a class `w_F`. The parity lemma
(`Finsupp.abs_poincareNegOne_le`, `Finsupp.poincareNegOne_modEq`) then gives

  `μ_F(E) ≥ |⟨w_F, v(E)⟩|`, with `μ_F(E) ≡ ⟨w_F, v(E)⟩ mod 2`

(`FibreFunctorProfile.abs_le_mass`, `FibreFunctorProfile.modEq_mass`). For `F = RHom(A, -)`,
`w_F = v(A)` and `μ_F = h(A, -)` is the total `Ext` count; for the rank functional, `F` is the
derived fibre at a point and `w_F = v(𝒪_x)`.

`FibreFunctorProfile` records the graded dimensions, the class map, the class `w_F` and the
Euler identity. It adds no geometric field: the Euler identity is the only input, and it holds in
every instance where `χ_F` is computed by Riemann–Roch.

## The instance from real objects

`RepresentationTheory/Quiver/Kronecker/FibreFunctorProfile.lean` builds one for
`F = RHom(A, -)` on representations of the doubled Kronecker quiver with the preprojective
relations, from `dim Ext¹(A, E) = dim Hom(A, E) + dim Hom(E, A) - (a, e)` (Crawley-Boevey,
Amer. J. Math. 122 (2000), Lemma 1).
-/

open scoped NNReal

/-- A **fibre-functor profile** on `Obj` with classes in a lattice `Λ` with form `B`: the graded
dimensions `dims E = (dim Hʲ(F E))_j` of an exact functor `F` to graded vector spaces, a class map
`cls`, and a class `w` with `χ_F(E) = P_E(-1) = -B(w, cls E)`. -/
structure FibreFunctorProfile (Obj Λ : Type*) [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) where
  /-- The graded dimensions `j ↦ dim Hʲ(F E)`. -/
  dims : Obj → ℤ →₀ ℕ
  /-- The class map `E ↦ v(E)`. -/
  cls : Obj → Λ
  /-- The class `w_F` of the functor. -/
  w : Λ
  /-- The Euler characteristic of `F E` is `-⟨w_F, v(E)⟩` (Mukai's sign). -/
  poincareNegOne_dims : ∀ E, (dims E).poincareNegOne = -B w (cls E)

namespace FibreFunctorProfile

variable {Obj Λ : Type*} [AddCommGroup Λ] {B : LinearMap.BilinForm ℤ Λ}
  (F : FibreFunctorProfile Obj Λ B)

/-- The profile value `μ_F(E) = P_E(1) = Σ_j dim Hʲ(F E)`. -/
def mass (E : Obj) : ℕ := (F.dims E).poincareOne

/-- The fibre-functor profile as a `Profile`. -/
def toProfile : Profile Obj := Profile.ofFun fun E ↦ (F.mass E : ℝ≥0)

@[simp]
lemma toProfile_apply (E : Obj) : F.toProfile E = F.mass E := rfl

/-- **`μ_F ≥ |⟨w_F, v(-)⟩|`.** -/
theorem abs_le_mass (E : Obj) : |B F.w (F.cls E)| ≤ F.mass E := by
  have := (F.dims E).abs_poincareNegOne_le
  rwa [F.poincareNegOne_dims, abs_neg] at this

/-- **Parity**: `μ_F(E) ≡ ⟨w_F, v(E)⟩ mod 2`. -/
theorem modEq_mass (E : Obj) : B F.w (F.cls E) ≡ F.mass E [ZMOD 2] := by
  have := (F.dims E).poincareNegOne_modEq
  rw [F.poincareNegOne_dims] at this
  refine (Int.ModEq.trans ?_ this)
  exact Int.modEq_iff_dvd.2 ⟨-B F.w (F.cls E), by ring⟩

/-- `μ_F(E) - |⟨w_F, v(E)⟩|` is even. -/
theorem even_mass_sub_abs (E : Obj) : Even ((F.mass E : ℤ) - |B F.w (F.cls E)|) := by
  rw [even_iff_two_dvd]
  have h1 := Int.modEq_iff_dvd.1 (F.modEq_mass E)
  rcases abs_choice (B F.w (F.cls E)) with h | h <;> rw [h]
  · exact h1
  · rw [sub_neg_eq_add, show (F.mass E : ℤ) + B F.w (F.cls E) =
      ((F.mass E : ℤ) - B F.w (F.cls E)) + 2 * B F.w (F.cls E) by ring]
    exact dvd_add h1 (dvd_mul_right 2 _)

end FibreFunctorProfile
