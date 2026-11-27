/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.SeveralFibres.Index

/-!
# A model of two orthogonal fibres: two `A₁`'s

On `N = ℤ²` with the form `b(x, y) = -2x₀y₀ - 2x₁y₁`, the curves `e₀` and `e₁` are two orthogonal
fibres of type `A₁`, each with `Θ = C` (`a1Fibre`). So the hypotheses of
`AffineWeyl/SeveralFibres/Index.lean` are consistent: the index of `Λ` in `ℤ × ℤ` divides
`det A₁ · det A₁ = 4`, and here it is `4`, because every class is supported on the fibres, so
`Λ = Q^∨ = 2ℤ × 2ℤ`.

Built by `lake test`.
-/

namespace K3TwistsTest.SeveralFibresModel

open Mukai Mukai.FundamentalCycle

/-- The form `-2x₀y₀ - 2x₁y₁` on `ℤ²`. -/
def twoA1Form : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => -2 * x 0 * y 0 - 2 * x 1 * y 1)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)

@[simp]
theorem twoA1Form_apply (x y : Fin 2 → ℤ) : twoA1Form x y = -2 * x 0 * y 0 - 2 * x 1 * y 1 :=
  rfl

theorem twoA1Form_comm (x y : Fin 2 → ℤ) : twoA1Form x y = twoA1Form y x := by
  simp only [twoA1Form_apply]
  ring

/-- **The `A₁` fibre at `eⱼ`**, with `Θ = C = eⱼ`. -/
def a1Fibre (j : Fin 2) : FundamentalCycle twoA1Form Unit where
  curve _ := Pi.single j 1
  mult _ := 1
  curve_self _ := by fin_cases j <;> simp
  curve_nonneg i i' h := absurd (Subsingleton.elim i i') h
  negDef d hd := by
    have h0 : d () ≠ 0 := fun h0 => hd (funext fun u => by cases u; exact h0)
    have : 0 < d () ^ 2 := by positivity
    fin_cases j <;> simp <;> nlinarith
  connected := by
    rw [Matrix.isIndecomposable_iff_reflTransGen]
    intro i i'
    rw [Subsingleton.elim i i']
  mult_nonneg _ := zero_le_one
  cycle_self := by fin_cases j <;> simp
  cycle_curve_nonpos _ := by fin_cases j <;> simp

/-- The two fibres are orthogonal. -/
theorem a1Fibre_orthogonal (a a' : Fin 2) (h : a ≠ a') (i j : Unit) :
    twoA1Form ((a1Fibre a).curve i) ((a1Fibre a').curve j) = 0 := by
  fin_cases a <;> fin_cases a' <;> simp_all [a1Fibre]

theorem det_cartan_a1Fibre (j : Fin 2) : (a1Fibre j).cartan.det = 2 := by
  fin_cases j <;> simp [Matrix.det_unique, a1Fibre]

/-- **The index bound for two orthogonal `A₁` fibres is `4`.** -/
example : (sumDegreeLattice a1Fibre).toAddSubgroup.index ∣ 4 := by
  have h := index_sumDegreeLattice_dvd twoA1Form_comm a1Fibre a1Fibre_orthogonal
  rwa [Fin.prod_univ_two, det_cartan_a1Fibre, det_cartan_a1Fibre] at h

/-- Every degree lies in `Q^∨ = 2ℤ × 2ℤ`: the classes of `ℤ²` are supported on the fibres. -/
theorem sumDegreeLattice_eq : sumDegreeLattice a1Fibre = sumCorootLattice a1Fibre := by
  refine le_antisymm ?_ (sumCorootLattice_le_sumDegreeLattice twoA1Form_comm a1Fibre
    a1Fibre_orthogonal)
  rintro _ ⟨x, rfl⟩
  refine (mem_sumCorootLattice a1Fibre).mpr fun a => ⟨fun _ => -x a, ?_⟩
  ext u
  fin_cases a <;> simp [Matrix.mulVec, dotProduct, a1Fibre]

/-- **The bound is attained**: `[ℤ × ℤ : Λ] = 4`. -/
example : (sumDegreeLattice a1Fibre).toAddSubgroup.index = 4 := by
  rw [sumDegreeLattice_eq, index_sumCorootLattice, Fin.prod_univ_two, det_cartan_a1Fibre,
    det_cartan_a1Fibre]
  rfl

end K3TwistsTest.SeveralFibresModel
