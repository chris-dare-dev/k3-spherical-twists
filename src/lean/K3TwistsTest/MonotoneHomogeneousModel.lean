/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Topical.MaxOperator
import K3Twists.Analysis.Topical.Nonexpansive
import K3Twists.Analysis.Topical.PiecewiseLinear
import K3Twists.Order.Squeeze
import K3Twists.RingTheory.Polynomial.DoublePlaneCubics

/-!
# Models of monotone homogeneous maps

* **The linear certificates.** `Matrix.gelfandRadius_le_of_mulVec_le` and
  `Matrix.le_gelfandRadius_of_smul_le_mulVec` are the linear case of the Collatz–Wielandt bounds,
  through `MonotoneHomogeneous.cycleTime_mulVec`.
* **The ratio test on the block matrix.** For the integer matrix `M₂` of the word `T₀T₁T₃²` on
  the double plane, the ratios of `M₂ 𝟙` bracket the rate in `[101, 134]` and those of `M₂² 𝟙`
  in `[121, 123]` (the Perron root of `t³ - 122t² - 10t - 31` is `122.08…`).
* **Piecewise-linear models.** The forward operator of the letters at a wall of two spheres
  pairing to two is a one-cell model with an eigenvector at the rate (`EigAtRate`), from the count
  letters themselves. A two-cell model `x ↦ (max(x₀ + x₁, 2x₀), x₁)` has rate `2`, attained by the
  eigenvector `(1, 0)` on a face: `R = ρ(A[J, J])` for its support `J = {0}`.
* **The squeeze along one orbit.** The count map `P(x) = 2 max(x₀, x₁) 𝟙` is monotone homogeneous
  and not additive, so it never satisfies the intertwining of `Order.squeeze` for all `x` with an
  additive injective sign map (`Order.map_add_of_intertwine`). It satisfies it along the orbit
  `2ⁿ 𝟙`, and `Order.squeeze_orbit` applies.
-/

open Polynomial.DoublePlane MonotoneHomogeneous

/-! ### The linear certificates -/

open scoped Matrix.Norms.Operator in
/-- The upper certificate for the Gelfand radius is the upper Collatz–Wielandt bound for
`x ↦ L x`. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {L : Matrix ι ι ℝ}
    (hL : ∀ i j, 0 ≤ L i j) {v : ι → ℝ} {m ρ : ℝ} (hm : 0 < m) (hvm : ∀ i, m ≤ v i)
    (hv : L.mulVec v ≤ ρ • v) : gelfandRadius L ≤ ρ := by
  rw [← cycleTime_mulVec hL]
  exact (MonotoneHomogeneous.mulVec hL).cycleTime_le_of_le_smul hm hvm hv

open scoped Matrix.Norms.Operator in
/-- The lower certificate for the Gelfand radius is the lower Collatz–Wielandt bound. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] {L : Matrix ι ι ℝ} (hL : ∀ i j, 0 ≤ L i j)
    {v : ι → ℝ} (hv0 : 0 ≤ v) (hv : v ≠ 0) {t : ℝ} (ht : t • v ≤ L.mulVec v) :
    t ≤ gelfandRadius L := by
  rw [← cycleTime_mulVec hL]
  exact (MonotoneHomogeneous.mulVec hL).le_cycleTime_of_smul_le hv0 hv ht

/-! ### The ratio test on the block matrix -/

/-- The block matrix `M₂` over `ℝ`. -/
noncomputable def blockTwo : Matrix (Fin 3) (Fin 3) ℝ := (blockMatrix 2).map (Int.cast : ℤ → ℝ)

lemma blockTwo_eq : blockTwo = !![83, 44, 7; 63, 33, 5; 69, 38, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockTwo, blockMatrix]

lemma blockTwo_nonneg : ∀ i j, 0 ≤ blockTwo i j := by
  rw [blockTwo_eq]
  intro i j
  fin_cases i <;> fin_cases j <;> simp

open scoped Matrix.Norms.Operator in
/-- One step of the ratio test from `𝟙`: `101 ≤ ρ(M₂) ≤ 134`. -/
example : 101 ≤ gelfandRadius blockTwo ∧ gelfandRadius blockTwo ≤ 134 := by
  rw [← cycleTime_mulVec blockTwo_nonneg]
  refine (MonotoneHomogeneous.mulVec blockTwo_nonneg).cycleTime_mem_Icc_of_ratio
    (v := 1) one_pos (fun _ => le_rfl) (fun i => ?_) (fun i => ?_) <;>
    rw [blockTwo_eq] <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

open scoped Matrix.Norms.Operator in
/-- The second step, from `M₂ 𝟙 = (134, 101, 113)`: `121 ≤ ρ(M₂) ≤ 123`. -/
example : 121 ≤ gelfandRadius blockTwo ∧ gelfandRadius blockTwo ≤ 123 := by
  rw [← cycleTime_mulVec blockTwo_nonneg]
  refine (MonotoneHomogeneous.mulVec blockTwo_nonneg).cycleTime_mem_Icc_of_ratio
    (v := ![134, 101, 113]) (m := 101) (by norm_num) (fun i => ?_) (fun i => ?_) (fun i => ?_) <;>
    [skip; rw [blockTwo_eq]; rw [blockTwo_eq]] <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

/-! ### Piecewise-linear models -/

/-- The forward operator of the letters at a wall of two spheres pairing to two, as a one-cell
piecewise-linear integral model. -/
noncomputable def affineModel : PLModel (maxMulVec affineLetters) Unit where
  cell _ := {x | 0 ≤ x}
  mat _ := !![1, 2; 2, 1]
  mat_nonneg _ i j := by fin_cases i <;> fin_cases j <;> simp
  smul_mem _ {c} {x} hc hx := show 0 ≤ c • x from smul_nonneg hc.le hx
  exists_mem _ hx := ⟨(), hx⟩
  eq_mulVec _ x hx := by
    rw [maxMulVec_affine hx]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The forward operator has an eigenvector at its rate, `𝟙`. -/
lemma eigAtRate_affine : EigAtRate (maxMulVec affineLetters) := by
  refine ⟨1, zero_le_one, one_ne_zero, ?_⟩
  rw [cycleTime_maxMulVec_affine, maxMulVec_affine zero_le_one]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

example : IsIntegral ℤ (cycleTime (maxMulVec affineLetters)) :=
  affineModel.isIntegral_cycleTime eigAtRate_affine

/-- The two-cell map `x ↦ (max(x₀ + x₁, 2x₀), x₁)`. -/
noncomputable def twoCellLetters : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![1, 1; 0, 1], !![2, 0; 0, 1]]

lemma twoCellLetters_nonneg : ∀ a i j, 0 ≤ twoCellLetters a i j := by
  intro a i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [twoCellLetters]

lemma maxMulVec_twoCell (x : Fin 2 → ℝ) :
    maxMulVec twoCellLetters x 0 = max (x 0 + x 1) (2 * x 0) ∧
      maxMulVec twoCellLetters x 1 = x 1 := by
  constructor <;> rw [maxMulVec_apply] <;> apply le_antisymm
  · refine Finset.sup'_le _ _ fun a _ => ?_
    fin_cases a <;> simp [twoCellLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine max_le ?_ ?_
    · calc x 0 + x 1 = (twoCellLetters 0).mulVec x 0 := by
            simp [twoCellLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        _ ≤ _ := Finset.le_sup' (fun a => (twoCellLetters a).mulVec x 0) (Finset.mem_univ 0)
    · calc 2 * x 0 = (twoCellLetters 1).mulVec x 0 := by
            simp [twoCellLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        _ ≤ _ := Finset.le_sup' (fun a => (twoCellLetters a).mulVec x 0) (Finset.mem_univ 1)
  · refine Finset.sup'_le _ _ fun a _ => ?_
    fin_cases a <;> simp [twoCellLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · calc x 1 = (twoCellLetters 0).mulVec x 1 := by
          simp [twoCellLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      _ ≤ _ := Finset.le_sup' (fun a => (twoCellLetters a).mulVec x 1) (Finset.mem_univ 0)

/-- The two-cell map has rate `2`: `(1, 1/2)` is a supersolution and `(1, 0)` an eigenvector. -/
lemma cycleTime_twoCell : cycleTime (maxMulVec twoCellLetters) = 2 := by
  have hf := monotoneHomogeneous_maxMulVec twoCellLetters_nonneg
  apply le_antisymm
  · refine hf.cycleTime_le_of_le_smul (x := ![1, 1 / 2]) (m := 1 / 2) (by norm_num)
      (fun i => by fin_cases i <;> norm_num) fun i => ?_
    obtain ⟨h0, h1⟩ := maxMulVec_twoCell ![1, 1 / 2]
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      rw [h0]
      norm_num
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      rw [h1]
      norm_num
  · refine hf.le_cycleTime_of_smul_le (v := ![1, 0]) (fun i => by fin_cases i <;> norm_num)
      (fun h => by simpa using congrFun h 0) fun i => ?_
    obtain ⟨h0, h1⟩ := maxMulVec_twoCell ![1, 0]
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      rw [h0]
      norm_num
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      rw [h1]
      norm_num

/-- The two-cell map as a piecewise-linear integral model: the cells `x₀ ≤ x₁` and `x₁ ≤ x₀`. -/
noncomputable def twoCellModel : PLModel (maxMulVec twoCellLetters) Bool where
  cell b := {x | 0 ≤ x ∧ if b then x 1 ≤ x 0 else x 0 ≤ x 1}
  mat b := if b then !![2, 0; 0, 1] else !![1, 1; 0, 1]
  mat_nonneg b i j := by cases b <;> fin_cases i <;> fin_cases j <;> simp
  smul_mem b {c} {x} hc hx := by
    refine ⟨smul_nonneg hc.le hx.1, ?_⟩
    cases b <;> simp only [Bool.false_eq_true, ite_true, ite_false, Pi.smul_apply,
      smul_eq_mul] at hx ⊢ <;> exact mul_le_mul_of_nonneg_left hx.2 hc.le
  exists_mem x hx := by
    rcases le_total (x 1) (x 0) with h | h
    · exact ⟨true, hx, by simpa using h⟩
    · exact ⟨false, hx, by simpa using h⟩
  eq_mulVec b x hx := by
    obtain ⟨h0, h1⟩ := maxMulVec_twoCell x
    obtain ⟨-, hle⟩ := hx
    ext i
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hle ⊢
      fin_cases i
      · show maxMulVec twoCellLetters x 0 = _
        rw [h0, max_eq_left (by linarith)]
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · show maxMulVec twoCellLetters x 1 = _
        rw [h1]
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp only [ite_true] at hle ⊢
      fin_cases i
      · show maxMulVec twoCellLetters x 0 = _
        rw [h0, max_eq_right (by linarith)]
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · show maxMulVec twoCellLetters x 1 = _
        rw [h1]
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The eigenvector at the rate `(1, 0)` lies on a face; its support is `{0}`, where the cell
matrix restricts to `[2]`. -/
example : (twoCellModel.realMat true).mulVec ![1, 0] =
    cycleTime (maxMulVec twoCellLetters) • ![1, 0] := by
  rw [cycleTime_twoCell]
  ext i
  fin_cases i <;> simp [PLModel.realMat, twoCellModel, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-! ### The squeeze along one orbit -/

/-- The count map `P(x) = 2 max(x₀, x₁) 𝟙`, the forward operator of `2` and of `2` times the swap. -/
noncomputable def swapLetters : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![2, 0; 0, 2], !![0, 2; 2, 0]]

lemma swapLetters_nonneg : ∀ a i j, 0 ≤ swapLetters a i j := by
  intro a i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [swapLetters]

lemma maxMulVec_swap (x : Fin 2 → ℝ) (i : Fin 2) :
    maxMulVec swapLetters x i = 2 * max (x 0) (x 1) := by
  rw [maxMulVec_apply]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun a _ => ?_
    fin_cases a <;> fin_cases i <;>
      simp [swapLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rcases le_total (x 0) (x 1) with h | h
    · rw [max_eq_right h]
      fin_cases i
      · calc 2 * x 1 = (swapLetters 1).mulVec x 0 := by
              simp [swapLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          _ ≤ _ := Finset.le_sup' (fun a => (swapLetters a).mulVec x 0) (Finset.mem_univ 1)
      · calc 2 * x 1 = (swapLetters 0).mulVec x 1 := by
              simp [swapLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          _ ≤ _ := Finset.le_sup' (fun a => (swapLetters a).mulVec x 1) (Finset.mem_univ 0)
    · rw [max_eq_left h]
      fin_cases i
      · calc 2 * x 0 = (swapLetters 0).mulVec x 0 := by
              simp [swapLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          _ ≤ _ := Finset.le_sup' (fun a => (swapLetters a).mulVec x 0) (Finset.mem_univ 0)
      · calc 2 * x 0 = (swapLetters 1).mulVec x 1 := by
              simp [swapLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          _ ≤ _ := Finset.le_sup' (fun a => (swapLetters a).mulVec x 1) (Finset.mem_univ 1)

/-- The count map is monotone homogeneous and not additive. -/
example : MonotoneHomogeneous (maxMulVec swapLetters) ∧
    maxMulVec swapLetters (![1, 0] + ![0, 1]) ≠
      maxMulVec swapLetters ![1, 0] + maxMulVec swapLetters ![0, 1] := by
  refine ⟨monotoneHomogeneous_maxMulVec swapLetters_nonneg, fun h => ?_⟩
  have := congrFun h 0
  simp only [Pi.add_apply, maxMulVec_swap] at this
  norm_num at this

/-- Along the orbit `c_n = 2ⁿ 𝟙` the nonadditive count map agrees with the linear signed action
`E = 2`, and the squeeze applies with the sign map and modulus the identity. -/
example : ∀ n, (fun n : ℕ => (2 : ℝ) ^ n • (1 : Fin 2 → ℝ)) n =
      id ((fun n : ℕ => (2 : ℝ) ^ n • (1 : Fin 2 → ℝ)) n) ∧
    (fun n : ℕ => (2 : ℝ) ^ n • (1 : Fin 2 → ℝ)) (n + 1) =
      maxMulVec swapLetters ((fun n : ℕ => (2 : ℝ) ^ n • (1 : Fin 2 → ℝ)) n) := by
  have hP : ∀ n, maxMulVec swapLetters ((2 : ℝ) ^ n • (1 : Fin 2 → ℝ)) =
      (2 : ℝ) ^ (n + 1) • (1 : Fin 2 → ℝ) := fun n => by
    ext i
    rw [maxMulVec_swap]
    simp [pow_succ]
    ring
  refine Order.squeeze_orbit id id (fun _ => maxMulVec swapLetters) (fun _ x => (2 : ℝ) • x)
    (fun n => (2 : ℝ) ^ n • (1 : Fin 2 → ℝ)) (fun n => (2 : ℝ) ^ n • (1 : Fin 2 → ℝ))
    (fun _ => le_rfl) (fun n => ?_) (fun n => (hP n).ge) (fun n => ?_) (fun _ => le_rfl) rfl
  · simp only [id_eq]
    rw [hP n, smul_smul]
    congr 1
    ring
  · rw [smul_smul]
    congr 1
    ring
