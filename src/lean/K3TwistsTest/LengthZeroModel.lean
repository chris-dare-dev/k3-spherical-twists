/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.Coxeter
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.LengthZeroGroup
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WeylTilt.Slicing
import K3TwistsTest.AffineWeylModel

/-!
# Models for length-zero elements, the fibre Coxeter groups and the charge cone

* **An `A₂` fibre with every degree realized.** On `N = ℤ³` with Gram matrix
  `[[-2, 1, 1], [1, -2, 0], [1, 0, 0]]`, the curves `C₀ = e₀`, `C₁ = e₁` with `Θ = C₀ + C₁` form a
  fundamental cycle of type `A₂` (`a2Wide`), the lattice is even, and the classes
  `M₀ = e₂`, `M₁ = e₀ + 2e₂` have degrees `(1, 0)` and `(0, 1)`, so `Λ = ℤ²`. The length-zero
  permutations then form a group of order `3 = det A₂` (the theorem of
  `AffineWeyl/LengthZeroGroup.lean` at `P^∨/Q^∨ = ℤ/3`), and both nodes are minuscule, with
  length-zero elements `⊗𝒪(Mⱼ) ∘ w` sending `α₀` to `αⱼ`.
* **The `A₂` fibre of `AffineWeylModel`** is a chain, `finiteExt = extA 2`, so its longest word
  `[0, 1, 0]` is root-positive on the classes `αᵢ = (0, -Cᵢ, 0)` and sends `αᵢ` to `-α_{1-i}`.
* **The charge cone** of a central charge contains a class of positive imaginary part and not
  its negative.

Built by `lake test`.
-/

namespace K3TwistsTest.LengthZeroModel

open Mukai Mukai.FundamentalCycle

/-! ### An `A₂` fibre with `Λ = ℤ²` -/

/-- The form with Gram matrix `[[-2, 1, 1], [1, -2, 0], [1, 0, 0]]` on `ℤ³`. -/
def wideForm : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ
    (fun x y => -2 * x 0 * y 0 + x 0 * y 1 + x 1 * y 0 + x 0 * y 2 + x 2 * y 0 - 2 * x 1 * y 1)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)

@[simp]
theorem wideForm_apply (x y : Fin 3 → ℤ) :
    wideForm x y =
      -2 * x 0 * y 0 + x 0 * y 1 + x 1 * y 0 + x 0 * y 2 + x 2 * y 0 - 2 * x 1 * y 1 :=
  rfl

theorem wideForm_comm (x y : Fin 3 → ℤ) : wideForm x y = wideForm y x := by
  simp only [wideForm_apply]
  ring

theorem wideForm_even (x : Fin 3 → ℤ) : Even (wideForm x x) :=
  ⟨-x 0 * x 0 + x 0 * x 1 + x 0 * x 2 - x 1 * x 1, by simp only [wideForm_apply]; ring⟩

/-- The curves `C₀ = e₀`, `C₁ = e₁`. -/
def wideCurve : Fin 2 → Fin 3 → ℤ := ![![1, 0, 0], ![0, 1, 0]]

theorem sum_smul_wideCurve (d : Fin 2 → ℤ) :
    ∑ i, d i • wideCurve i = ![d 0, d 1, 0] := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_two, wideCurve]

theorem wideForm_comb (d : Fin 2 → ℤ) :
    wideForm (∑ i, d i • wideCurve i) (∑ i, d i • wideCurve i) =
      -2 * d 0 ^ 2 + 2 * d 0 * d 1 - 2 * d 1 ^ 2 := by
  rw [sum_smul_wideCurve]
  simp
  ring

/-- **An `A₂` fibre in `ℤ³`**, with `Θ = C₀ + C₁`. -/
def a2Wide : FundamentalCycle wideForm (Fin 2) where
  curve := wideCurve
  mult _ := 1
  curve_self i := by fin_cases i <;> simp [wideCurve]
  curve_nonneg i j h := by fin_cases i <;> fin_cases j <;> simp [wideCurve] at h ⊢
  negDef d hd := by
    rw [wideForm_comb]
    have : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
      by_contra h
      simp only [not_or, not_not] at h
      exact hd (funext fun j => by fin_cases j <;> simp [h.1, h.2])
    rcases this with h | h
    · have := mul_self_pos.mpr h
      nlinarith [sq_nonneg (d 0 - 2 * d 1), sq_nonneg (d 0)]
    · have := mul_self_pos.mpr h
      nlinarith [sq_nonneg (2 * d 0 - d 1), sq_nonneg (d 1)]
  connected := by
    rw [Matrix.isIndecomposable_iff_reflTransGen]
    have h01 : Relation.ReflTransGen (fun i j : Fin 2 =>
        Matrix.of (fun i j : Fin 2 => wideForm (wideCurve i) (wideCurve j)) i j ≠ 0) 0 1 :=
      Relation.ReflTransGen.single (by simp [wideCurve])
    have h10 : Relation.ReflTransGen (fun i j : Fin 2 =>
        Matrix.of (fun i j : Fin 2 => wideForm (wideCurve i) (wideCurve j)) i j ≠ 0) 1 0 :=
      Relation.ReflTransGen.single (by simp [wideCurve])
    intro i j
    fin_cases i <;> fin_cases j
    · exact Relation.ReflTransGen.refl
    · exact h01
    · exact h10
    · exact Relation.ReflTransGen.refl
  mult_nonneg _ := zero_le_one
  cycle_self := by simp [Fin.sum_univ_two, wideCurve]
  cycle_curve_nonpos i := by fin_cases i <;> simp [Fin.sum_univ_two, wideCurve]

/-- **Every degree is realized**: `M₀ = e₂` and `M₁ = e₀ + 2e₂` have degrees `(1, 0)`, `(0, 1)`. -/
theorem degreeLattice_a2Wide : a2Wide.degreeLattice = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ⟨![x 1, 0, x 0 + 2 * x 1], ?_⟩
  ext i
  fin_cases i <;> simp [a2Wide, wideCurve]

theorem det_cartan_a2Wide : a2Wide.cartan.det = 3 := by
  rw [Matrix.det_fin_two]
  simp [a2Wide, wideCurve]

/-- **The length-zero permutations of the `A₂` fibre form a group of order `3`**: `P^∨/Q^∨ = ℤ/3`
is realized because `Λ = ℤ²`. -/
example : Nat.card a2Wide.lengthZeroPerm.range = 3 := by
  rw [a2Wide.card_lengthZeroPerm_range wideForm_comm wideForm_even degreeLattice_a2Wide,
    det_cartan_a2Wide]
  rfl

/-- **The length-zero element at the node `0`**: `⊗𝒪(e₂) ∘ w` sends `α₀` to `α_{C₀}`. -/
example : ∃ w ∈ a2Wide.finiteWeyl,
    tensorLineEquiv wideForm_comm ![0, 0, 1] (q := 0) (by simp) * w ∈
        a2Wide.affineRootStabilizer ∧
      (tensorLineEquiv wideForm_comm ![0, 0, 1] (q := 0) (by simp) * w) (a2Wide.affineRoot none) =
        a2Wide.affineRoot (some 0) :=
  a2Wide.exists_lengthZero_of_minuscule wideForm_comm (j := 0) rfl
    (fun i => by fin_cases i <;> simp [a2Wide, wideCurve]) _

/-- **The length-zero element at the node `1`**: `⊗𝒪(e₀ + 2e₂) ∘ w` sends `α₀` to `α_{C₁}`. -/
example : ∃ w ∈ a2Wide.finiteWeyl,
    tensorLineEquiv wideForm_comm ![1, 0, 2] (q := 1) (by simp) * w ∈
        a2Wide.affineRootStabilizer ∧
      (tensorLineEquiv wideForm_comm ![1, 0, 2] (q := 1) (by simp) * w) (a2Wide.affineRoot none) =
        a2Wide.affineRoot (some 1) :=
  a2Wide.exists_lengthZero_of_minuscule wideForm_comm (j := 1) rfl
    (fun i => by fin_cases i <;> simp [a2Wide, wideCurve]) _

/-- The simple reflections generate the affine Weyl group of the fibre. -/
example : a2Wide.affineWeyl = Subgroup.closure (a2Wide.simpleReflection '' Set.univ) :=
  a2Wide.affineWeyl_eq_closure wideForm_comm

/-! ### The chain `A₂` of `AffineWeylModel` -/

open K3TwistsTest.AffineWeylModel CoxeterMatrix

theorem a2Fibre_finiteExt : a2Fibre.finiteExt = extA 2 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [finiteExt, affineExt, extA, a2Fibre]

/-- **The longest word `[0, 1, 0]` is root-positive on the classes of the `A₂` fibre.** -/
example : BilinearForm.IsRootPositive (mukaiForm a2Form) a2Fibre.finiteRoot [0, 1, 0] :=
  FundamentalCycle.isRootPositive_longestWordA a2Form_comm a2Fibre a2Fibre_finiteExt
    (by norm_num)

/-- **`w₀` sends `α₀` to `-α₁` on the classes of the `A₂` fibre.** -/
example : BilinearForm.reflectWord (mukaiForm a2Form) a2Fibre.finiteRoot [0, 1, 0]
    (a2Fibre.finiteRoot 0) = -a2Fibre.finiteRoot 1 :=
  FundamentalCycle.reflectWord_longestWordA a2Form_comm a2Fibre a2Fibre_finiteExt (by norm_num) 0

/-- At `β·Cᵢ = 1/4`, root-positivity of a word in the affine reflections of the `A₂` fibre is the
sign of the charge on its prefix roots. -/
example (ω : List (Option (Fin 2))) :
    BilinearForm.IsRootPositive (mukaiForm a2Form) a2Fibre.affineRoot ω ↔
      ∀ v ∈ BilinearForm.prefixRoots (mukaiForm a2Form) a2Fibre.affineRoot ω,
        fibreCharge betaIn v < 0 := by
  refine a2Fibre.isRootPositive_affineRoot_iff a2Form_comm ⟨fun i => ?_, ?_⟩ ω
  · fin_cases i <;> simp [a2Fibre, betaIn]
  · rw [a2Fibre_cycle]
    simp [betaIn]
    norm_num

/-! ### The charge cone of a central charge -/

open CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap in
/-- `Z(n) = n i`: the class `1` lies in the charge cone, and `-1` does not. -/
example : (1 : ℤ) ∈ chargeCone (zmultiplesHom ℂ Complex.I) ∧
    (-1 : ℤ) ∉ chargeCone (zmultiplesHom ℂ Complex.I) := by
  have h : (1 : ℤ) ∈ chargeCone (zmultiplesHom ℂ Complex.I) := Or.inl (by simp)
  exact ⟨h, neg_notMem_chargeCone _ h⟩

end K3TwistsTest.LengthZeroModel
