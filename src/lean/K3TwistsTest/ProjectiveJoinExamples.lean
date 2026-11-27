/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Convex.ProjectiveJoin

/-!
# The projective join: examples

* **A dependent family.** In `ℝ²` with `ℓ` the sum of the coordinates, the points `(1, 0)`,
  `(0, 1)` and `(1, 1)` are linearly dependent, and the join sends the midpoint of the first two
  vertices of the simplex and the third vertex to the same point `(1/2, 1/2)`; so the join is not
  injective on the simplex, as `injOn_projectiveJoin_iff` predicts.
* **Nonnegativity is not needed.** With `ℓ` the first coordinate, the points `(1, -1)` and
  `(1, 1)` both have `ℓ = 1 > 0` although the first has a negative coordinate. They are linearly
  independent, so the join, which runs along the segment from `(1, -1)` to `(1, 1)`, is injective
  on the simplex and a closed embedding of it.
* **The usual case.** For profiles `Ω → ℝ` with weights `c = (1, r₁, …, r_s)` and `ℓ` the value
  at one object, the pointwise error condition is enough for the normalized profiles to follow the
  join (`tendsto_inv_mul_apply_of_eq_sum` gives the condition on `ℓ`).
* **The Cantor instance.** For `g = 1`, reals that follow the centre ratios of words converge iff
  the words converge.

Built by `lake test`.
-/

namespace K3TwistsTest.ProjectiveJoinExamples

open Filter Topology Set

/-! ### A dependent family -/

/-- The sum of the two coordinates of `ℝ²`. -/
noncomputable def sumCoord : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) + (LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)

@[simp]
lemma sumCoord_apply (x : Fin 2 → ℝ) : sumCoord x = x 0 + x 1 := rfl

/-- The two coordinate vectors of `ℝ²` and their sum. -/
def dep : Fin 3 → Fin 2 → ℝ := ![![1, 0], ![0, 1], ![1, 1]]

lemma sumCoord_dep_pos (i : Fin 3) : 0 < sumCoord (dep i) := by
  fin_cases i <;> norm_num [dep]

lemma not_linearIndependent_dep : ¬ LinearIndependent ℝ dep := by
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨![1, 1, -1], ?_, 0, by simp⟩
  ext j
  fin_cases j <;> simp [dep, Fin.sum_univ_three]

/-- The midpoint of the first two vertices and the third vertex have the same join. -/
example :
    projectiveJoin sumCoord dep ![1 / 2, 1 / 2, 0] = projectiveJoin sumCoord dep ![0, 0, 1] := by
  ext j
  fin_cases j <;> norm_num [projectiveJoin, dep, Fin.sum_univ_three]

/-- So the join of the dependent family is not injective on the simplex. -/
example : ¬ InjOn (projectiveJoin sumCoord dep) {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} :=
  fun h ↦ not_linearIndependent_dep ((injOn_projectiveJoin_iff sumCoord_dep_pos).1 h)

/-! ### Nonnegativity is not needed -/

/-- The first coordinate of `ℝ²`. -/
noncomputable def firstCoord : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (0 : Fin 2)

/-- The points `(1, -1)` and `(1, 1)` of `ℝ²`. -/
def signed : Fin 2 → Fin 2 → ℝ := ![![1, -1], ![1, 1]]

/-- The first point takes a negative value. -/
example : signed 0 1 < 0 := by norm_num [signed]

lemma firstCoord_signed_pos (i : Fin 2) : 0 < firstCoord (signed i) := by
  fin_cases i <;> norm_num [firstCoord, signed]

lemma linearIndependent_signed : LinearIndependent ℝ signed := by
  rw [signed, LinearIndependent.pair_iff]
  intro s t h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  norm_num at h₀ h₁
  constructor <;> linarith

/-- The join runs along the segment from `(1, -1)` to `(1, 1)`. -/
example (s : ℝ) : projectiveJoin firstCoord signed ![1 - s, s] = ![1, 2 * s - 1] := by
  ext j
  fin_cases j
  · norm_num [projectiveJoin, firstCoord, signed]
  · norm_num [projectiveJoin, firstCoord, signed]
    ring

example : InjOn (projectiveJoin firstCoord signed) {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} :=
  (injOn_projectiveJoin_iff firstCoord_signed_pos).2 linearIndependent_signed

example : IsClosedEmbedding fun t : Convexity.StdSimplex ℝ (Fin 2) ↦
    projectiveJoin firstCoord signed t.weights :=
  isClosedEmbedding_projectiveJoin_weights firstCoord_signed_pos linearIndependent_signed

/-! ### The usual case -/

/-- The weights `(1, r₁, …, r_s)` on profiles `Ω → ℝ`, normalized by the value at `E₀`. -/
example {Ω : Type*} (E₀ : Ω) {s : ℕ} {f : Fin (s + 1) → Ω → ℝ} (hf : ∀ i, 0 < f i E₀)
    {l : Filter ℕ} {r : ℕ → Fin s → ℝ} (hr : ∀ n j, 0 ≤ r n j) {ε : ℕ → Ω → ℝ}
    (hε : Tendsto (fun n ↦ (1 + ∑ j, r n j)⁻¹ • ε n) l (𝓝 0)) :
    Tendsto (fun n ↦ (f 0 E₀ + ∑ j, r n j * f j.succ E₀ + ε n E₀)⁻¹ •
        (f 0 + ∑ j, r n j • f j.succ + ε n) -
      projectiveJoin (LinearMap.proj E₀) f
        ((1 + ∑ j, r n j)⁻¹ • (Fin.cons 1 (r n) : Fin (s + 1) → ℝ))) l (𝓝 0) := by
  have h := tendsto_inv_apply_smul_sub_projectiveJoin (ℓ := LinearMap.proj E₀) (f := f) hf
    (c := fun n ↦ (Fin.cons 1 (r n) : Fin (s + 1) → ℝ)) (S := fun n ↦ 1 + ∑ j, r n j)
    (t := fun _ ↦ 1) (μ := fun n ↦ f 0 + ∑ j, r n j • f j.succ + ε n)
    (.of_forall fun n i ↦ Fin.cases zero_le_one (hr n) i)
    (.of_forall fun n ↦ Fin.sum_cons _ _)
    (.of_forall fun n ↦ add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ ↦ hr n j))
    (.of_forall fun _ ↦ one_ne_zero)
    (.of_forall fun n ↦ by simp [Fin.sum_univ_succ])
    hε (tendsto_inv_mul_apply_of_eq_sum (T := {()}) (b := fun _ ↦ 1) (E := fun _ ↦ E₀)
      (fun x ↦ by simp) hε)
  simpa using h

/-! ### The Cantor instance -/

/-- For `g = 1`, reals that follow the centre ratios of words converge iff the words do. -/
example (ω : ℕ → ℕ → Bool) (x : ℕ → ℝ)
    (hx : Tendsto (fun n ↦ x n - IFS.centreRatio 1 (ω n)) atTop (𝓝 0)) :
    (∃ y, Tendsto x atTop (𝓝 y)) ↔ ∃ η, Tendsto ω atTop (𝓝 η) :=
  IFS.exists_tendsto_iff_of_tendsto_sub_centreRatio (by norm_num) hx

end K3TwistsTest.ProjectiveJoinExamples
