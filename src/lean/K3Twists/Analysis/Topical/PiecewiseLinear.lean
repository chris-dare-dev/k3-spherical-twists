/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Topical.CollatzWielandt
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Piecewise-linear integral models of monotone homogeneous maps

A **piecewise-linear integral model** of a map `f` of the orthant (`PLModel`) is a finite family of
cones `C_k` covering the orthant, with integer cell matrices `A_k ≥ 0` such that `f x = A_k x` for
`x ∈ C_k`. Agreement on common faces is automatic, since `f` is one function. With closed
full-dimensional cells, monotonicity of `f` forces the cell matrices to be nonnegative; here that
is a field.

`EigAtRate f` says that `f` has an eigenvector `0 ≤ v ≠ 0` with eigenvalue its cycle time. For a
continuous monotone homogeneous map of the closed orthant this is a consequence of Brouwer's fixed
point theorem on the simplex (Lemmens–Nussbaum, *Nonlinear Perron–Frobenius theory*, Cambridge
Tracts in Mathematics 189, Chapter 5). Mathlib has no Brouwer theorem, so it is a hypothesis.

Given a model and `EigAtRate f`:

* `PLModel.isIntegral_cycleTime`: the cycle time is an algebraic integer, a root of the
  characteristic polynomial of a cell matrix (no spectral radius is used).
* `PLModel.isGreatest_cycleTime`: `R(f) = max {t : v ∈ C_k, v ≥ 0, Σ v = 1, A_k v = t v}`, the
  largest solution of the finitely many cell eigenvalue problems. Each solution is a lower
  Collatz–Wielandt certificate; the maximum is attained by `EigAtRate`.
* `PLModel.gelfandRadius_submatrix_eq_cycleTime`: `R(f) = ρ(A_k[J, J])` for the support `J` of
  an eigenvector at the rate in `C_k`; its restriction to `J` is positive. This also covers an
  eigenvector on a proper face.

The polynomial envelope `‖fⁿ 𝟙‖ ≤ B n^{r−1} R(f)ⁿ` of a model with `R(f) ≥ 1` is not proved here.
-/

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- A **piecewise-linear integral model** of `f`: cones `cell k` covering the orthant, and
nonnegative integer matrices `mat k` with `f x = mat k x` on `cell k`. -/
structure PLModel (f : (ι → ℝ) → ι → ℝ) (κ : Type*) where
  /-- The cells. -/
  cell : κ → Set (ι → ℝ)
  /-- The cell matrices. -/
  mat : κ → Matrix ι ι ℤ
  mat_nonneg : ∀ k i j, 0 ≤ mat k i j
  smul_mem : ∀ k {c : ℝ} {x : ι → ℝ}, 0 < c → x ∈ cell k → c • x ∈ cell k
  exists_mem : ∀ x : ι → ℝ, 0 ≤ x → ∃ k, x ∈ cell k
  eq_mulVec : ∀ k x, x ∈ cell k → f x = ((mat k).map (Int.cast : ℤ → ℝ)).mulVec x

/-- `f` has a nonzero nonnegative eigenvector whose eigenvalue is its cycle time. -/
def EigAtRate (f : (ι → ℝ) → ι → ℝ) : Prop :=
  ∃ v : ι → ℝ, 0 ≤ v ∧ v ≠ 0 ∧ f v = cycleTime f • v

namespace PLModel

variable {f : (ι → ℝ) → ι → ℝ} {κ : Type*} (P : PLModel f κ)

/-- The real cell matrices. -/
def realMat (k : κ) : Matrix ι ι ℝ := (P.mat k).map (Int.cast : ℤ → ℝ)

lemma realMat_nonneg (k : κ) (i j : ι) : 0 ≤ P.realMat k i j := by
  simpa [realMat] using P.mat_nonneg k i j

/-- An eigenvector at the rate lies in a cell, where it is an eigenvector of the cell matrix. -/
theorem exists_cell_eigen (he : EigAtRate f) :
    ∃ k v, v ∈ P.cell k ∧ 0 ≤ v ∧ v ≠ 0 ∧ (P.realMat k).mulVec v = cycleTime f • v := by
  obtain ⟨v, hv0, hv, hfv⟩ := he
  obtain ⟨k, hk⟩ := P.exists_mem v hv0
  exact ⟨k, v, hk, hv0, hv, by rw [realMat, ← P.eq_mulVec k v hk, hfv]⟩

variable [DecidableEq ι]

/-- An eigenvalue of a real matrix with a nonzero eigenvector lies in its spectrum. -/
lemma mem_spectrum_of_mulVec_eq {B : Matrix ι ι ℝ} {v : ι → ℝ} (hv : v ≠ 0) {t : ℝ}
    (h : B.mulVec v = t • v) : t ∈ spectrum ℝ B := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  by_contra hdet
  apply hv
  refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
  rw [Matrix.sub_mulVec, h, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_self]

include P in
/-- **The cycle time of a piecewise-linear integral model is an algebraic integer**: it is a root
of the characteristic polynomial of an integer cell matrix. -/
theorem isIntegral_cycleTime (he : EigAtRate f) : IsIntegral ℤ (cycleTime f) := by
  obtain ⟨k, v, -, -, hv, hkv⟩ := P.exists_cell_eigen he
  have hspec := mem_spectrum_of_mulVec_eq hv hkv
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, realMat,
    show (P.mat k).map (Int.cast : ℤ → ℝ) = (P.mat k).map (Int.castRingHom ℝ) from rfl,
    Matrix.charpoly_map, Polynomial.IsRoot.def, Polynomial.eval_map, ← algebraMap_int_eq,
    ← Polynomial.aeval_def] at hspec
  exact ⟨(P.mat k).charpoly, (P.mat k).charpoly_monic, hspec⟩

omit [DecidableEq ι] in
/-- **The cycle time is the largest cell eigenvalue.** `R(f)` is the greatest `t` for which some
cell carries a vector `v ≥ 0` with `Σ v = 1` and `A_k v = t v`. -/
theorem isGreatest_cycleTime (hf : MonotoneHomogeneous f) (he : EigAtRate f) :
    IsGreatest {t : ℝ | ∃ k v, v ∈ P.cell k ∧ 0 ≤ v ∧ ∑ i, v i = 1 ∧
      (P.realMat k).mulVec v = t • v} (cycleTime f) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, v, hk, hv0, hv, hkv⟩ := P.exists_cell_eigen he
    have hsum : 0 < ∑ i, v i := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        push Not at h
        exact hv (funext h)
      exact lt_of_lt_of_le (lt_of_le_of_ne (hv0 i) (Ne.symm hi))
        (Finset.single_le_sum (fun j _ => hv0 j) (Finset.mem_univ i))
    refine ⟨k, (∑ i, v i)⁻¹ • v, P.smul_mem k (inv_pos.2 hsum) hk,
      smul_nonneg (inv_nonneg.2 hsum.le) hv0, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hsum.ne'
    · rw [Matrix.mulVec_smul, hkv, smul_comm]
  · rintro t ⟨k, v, hk, hv0, hsum, hkv⟩
    have hv : v ≠ 0 := by
      rintro rfl
      simp at hsum
    refine hf.le_cycleTime_of_smul_le hv0 hv ?_
    rw [P.eq_mulVec k v hk]
    exact le_of_eq (by rw [← realMat, hkv])

open scoped Matrix.Norms.Operator in
/-- **The rate is a spectral radius of a principal submatrix.** If `0 ≤ v ≠ 0` and
`A_k v = R(f) v`, then on the support `J = {i : v i > 0}` the submatrix `A_k[J, J]` has the
positive eigenvector `v|_J`, so its Gelfand radius is `R(f)`. -/
theorem gelfandRadius_submatrix_eq_cycleTime {k : κ} {v : ι → ℝ} (hv0 : 0 ≤ v) (hv : v ≠ 0)
    (hkv : (P.realMat k).mulVec v = cycleTime f • v) :
    gelfandRadius ((P.realMat k).submatrix (Subtype.val : {i // 0 < v i} → ι)
      (Subtype.val : {i // 0 < v i} → ι)) = cycleTime f := by
  set B := (P.realMat k).submatrix (Subtype.val : {i // 0 < v i} → ι)
    (Subtype.val : {i // 0 < v i} → ι) with hB
  set w : {i // 0 < v i} → ℝ := fun j => v j with hw
  have hJ : Nonempty {i // 0 < v i} := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    exact ⟨⟨i, lt_of_le_of_ne (hv0 i) (Ne.symm hi)⟩⟩
  have hBw : B.mulVec w = cycleTime f • w := by
    ext j
    have hsum : ∑ j' : {i // 0 < v i}, P.realMat k j j' * v j' =
        ∑ i, P.realMat k j i * v i := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i => 0 < v i)
        (fun i => P.realMat k j i * v i)]
      have hzero : ∑ i : {i // ¬ 0 < v i}, P.realMat k j i * v i = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [le_antisymm (not_lt.1 i.2) (hv0 i), mul_zero]
      rw [hzero, add_zero]
    have h1 := congrFun hkv j
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [← h1, ← hsum]
    rfl
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => P.realMat_nonneg k i j
  set m := Finset.univ.inf' Finset.univ_nonempty w with hm
  have hm0 : 0 < m := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty w
    rw [hm, hi]
    exact i.2
  have hwne : w ≠ 0 := by
    obtain ⟨j⟩ := hJ
    intro h
    have := congrFun h j
    simp only [hw, Pi.zero_apply] at this
    exact (ne_of_gt j.2) this
  exact le_antisymm
    (Matrix.gelfandRadius_le_of_mulVec_le hB0 hm0 (fun i => Finset.inf'_le _ (Finset.mem_univ i))
      hBw.le)
    (Matrix.le_gelfandRadius_of_smul_le_mulVec hB0 (fun j => le_of_lt j.2) hwne hBw.ge)

end PLModel
