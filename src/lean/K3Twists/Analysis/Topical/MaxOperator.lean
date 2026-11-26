/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.JointSpectralRadius
import K3Twists.Analysis.Topical.CollatzWielandt

/-!
# Maximum operators over an alphabet

**The dual operator.** For finitely many self-maps `f_a` of any type `X`, the operator
`(Fμ)(x) = max_a μ(f_a x)` on functions `μ : X → ℝ` (`maxOperator`) has iterates
`Fⁿμ(x) = max_{|w| = n} μ(f_w x)`, the maximum over the words of length `n`
(`iterate_maxOperator_apply`). No order, linearity or monotonicity is used: `X` can be the set of
objects of a category and `μ` a mass.

**The forward operator.** For nonnegative matrices `A_a`, the coordinatewise maximum
`Φ(x) = max_a A_a x` (`maxMulVec`) is monotone homogeneous, and `Φⁿ 𝟙 ≥ A_w 𝟙` for every word of
length `n`. So its cycle time bounds the joint spectral radius from above
(`jointSpectralRadius_le_cycleTime_maxMulVec`). The bound can be strict. The letters
`P₁ = [[1, 2], [0, 1]]` and `P₂ = [[1, 0], [2, 1]]` of a wall of two spheres pairing to two have
`Φ = I + G` on the orthant, `G = [[0, 2], [2, 0]]`, with cycle time `1 + ρ(G) = 3`
(`cycleTime_maxMulVec_affine`), while their joint spectral radius is `1 + √2`
(`jointSpectralRadius_lt_cycleTime_affine`). The exponent of the alphabet comes from
submultiplicativity of the word maxima, not from this operator.

## Main results

* `iterate_maxOperator_apply`: `Fⁿμ(x) = max_{|w| = n} μ(f_w x)`.
* `monotoneHomogeneous_maxMulVec`, `jointSpectralRadius_le_cycleTime_maxMulVec`.
* `maxMulVec_affine`, `cycleTime_maxMulVec_affine`, `jointSpectralRadius_lt_cycleTime_affine`.
-/

open Filter Topology

variable {α : Type*} [Fintype α] [Nonempty α]

/-! ### The dual operator -/

section Dual

variable {X : Type*}

/-- The maximum operator `(F μ)(x) = max_a μ(f_a x)` of finitely many self-maps `f_a` of `X`. -/
noncomputable def maxOperator (f : α → X → X) (μ : X → ℝ) : X → ℝ :=
  fun x => Finset.univ.sup' Finset.univ_nonempty fun a => μ (f a x)

lemma maxOperator_apply (f : α → X → X) (μ : X → ℝ) (x : X) :
    maxOperator f μ x = Finset.univ.sup' Finset.univ_nonempty fun a => μ (f a x) :=
  rfl

omit [Fintype α] [Nonempty α] in
/-- A word applied to `x`, last letter first: `f_w x = f_{w 0} (f_{w 1} (⋯ f_{w (n - 1)} x))`. -/
def applyWord (f : α → X → X) {n : ℕ} (w : Fin n → α) (x : X) : X :=
  (List.ofFn w).foldr (fun a y => f a y) x

omit [Fintype α] [Nonempty α] in
lemma applyWord_cons (f : α → X → X) {n : ℕ} (a : α) (w : Fin n → α) (x : X) :
    applyWord f (Fin.cons a w) x = f a (applyWord f w x) := by
  simp [applyWord, List.ofFn_succ]

omit [Fintype α] [Nonempty α] in
lemma applyWord_zero (f : α → X → X) (w : Fin 0 → α) (x : X) : applyWord f w x = x := by
  simp [applyWord]

/-- **Iterates of the maximum operator are maxima over words.**
`Fⁿμ(x) = max_{|w| = n} μ(f_w x)`. -/
theorem iterate_maxOperator_apply (f : α → X → X) (n : ℕ) (μ : X → ℝ) (x : X) :
    (maxOperator f)^[n] μ x =
      Finset.univ.sup' Finset.univ_nonempty fun w : Fin n → α => μ (applyWord f w x) := by
  induction n generalizing μ x with
  | zero =>
    simp only [Function.iterate_zero, id_eq, applyWord_zero]
    rw [Finset.sup'_const]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun w _ => ?_
      rw [maxOperator_apply]
      refine Finset.sup'_le _ _ fun a _ => ?_
      rw [← applyWord_cons f a w x]
      exact Finset.le_sup' (fun w : Fin (n + 1) → α => μ (applyWord f w x)) (Finset.mem_univ _)
    · refine Finset.sup'_le _ _ fun w _ => ?_
      have hw : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
      rw [hw, applyWord_cons]
      refine le_trans ?_ (Finset.le_sup' (fun v : Fin n → α => maxOperator f μ (applyWord f v x))
        (Finset.mem_univ (Fin.tail w)))
      rw [maxOperator_apply]
      exact Finset.le_sup' (fun a => μ (f a (applyWord f (Fin.tail w) x))) (Finset.mem_univ (w 0))

end Dual

/-! ### The forward operator of nonnegative matrices -/

section Forward

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Operator

/-- The coordinatewise maximum `Φ(x) = max_a A_a x` of finitely many matrices. -/
noncomputable def maxMulVec (A : α → Matrix ι ι ℝ) : (ι → ℝ) → ι → ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a => (A a).mulVec

omit [DecidableEq ι] in
lemma maxMulVec_apply (A : α → Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    maxMulVec A x i = Finset.univ.sup' Finset.univ_nonempty fun a => (A a).mulVec x i := by
  simp only [maxMulVec, Finset.sup'_apply]

omit [DecidableEq ι] in
/-- The maximum of finitely many nonnegative matrices is monotone homogeneous. -/
theorem monotoneHomogeneous_maxMulVec {A : α → Matrix ι ι ℝ} (hA : ∀ a i j, 0 ≤ A a i j) :
    MonotoneHomogeneous (maxMulVec A) :=
  Finset.sup'_induction _ _ (fun _ h₁ _ h₂ => h₁.sup h₂)
    fun a _ => MonotoneHomogeneous.mulVec (hA a)

omit [DecidableEq ι] in
lemma mulVec_le_maxMulVec (A : α → Matrix ι ι ℝ) (a : α) (x : ι → ℝ) :
    (A a).mulVec x ≤ maxMulVec A x := fun i => by
  rw [maxMulVec_apply]
  exact Finset.le_sup' (fun a => (A a).mulVec x i) (Finset.mem_univ a)

/-- Every word of length `n` is dominated by `Φⁿ` on `𝟙`: `A_w 𝟙 ≤ Φⁿ 𝟙`. -/
lemma list_prod_mulVec_le_iterate {A : α → Matrix ι ι ℝ} (hA : ∀ a i j, 0 ≤ A a i j)
    {n : ℕ} (w : Fin n → α) :
    (List.ofFn (A ∘ w)).prod.mulVec 1 ≤ (maxMulVec A)^[n] 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
    rw [hw, List.ofFn_succ, List.prod_cons, Function.iterate_succ_apply']
    simp only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
    rw [← Matrix.mulVec_mulVec]
    calc (A (w 0)).mulVec ((List.ofFn fun i => A (Fin.tail w i)).prod.mulVec 1)
        ≤ (A (w 0)).mulVec ((maxMulVec A)^[n] 1) := Matrix.mulVec_mono (hA _) (ih _)
      _ ≤ maxMulVec A ((maxMulVec A)^[n] 1) := mulVec_le_maxMulVec A _ _

/-- **The forward operator bounds the joint spectral radius.** For nonnegative letters,
`JSR(A) ≤ R(Φ)`. -/
theorem jointSpectralRadius_le_cycleTime_maxMulVec {A : α → Matrix ι ι ℝ}
    (hA : ∀ a i j, 0 ≤ A a i j) : Matrix.jointSpectralRadius A ≤ cycleTime (maxMulVec A) := by
  have hΦ := monotoneHomogeneous_maxMulVec hA
  have hle : ∀ n, Monoid.sphereMax A (‖·‖) n ≤ ‖(maxMulVec A)^[n] 1‖ := by
    intro n
    refine Monoid.sphereMax_le _ _ fun w => ?_
    have hw0 : ∀ i j, 0 ≤ (List.ofFn (A ∘ w)).prod i j :=
      Matrix.list_prod_apply_nonneg _ (fun B hB i j => by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hB
        exact hA _ i j)
    have h1 := Matrix.mul_norm_le_norm_mulVec hw0 one_pos (c := 1) fun _ => le_rfl
    rw [one_mul] at h1
    exact h1.trans (Matrix.norm_le_norm_of_nonneg_of_le (Matrix.mulVec_nonneg hw0 zero_le_one)
      (list_prod_mulVec_le_iterate hA w))
  refine le_of_tendsto_of_tendsto (Matrix.tendsto_jointSpectralRadius A) hΦ.tendsto_cycleTime
    (Eventually.of_forall fun n => ?_)
  exact Real.rpow_le_rpow (Monoid.sphereMax_nonneg _ (fun _ => norm_nonneg _) n) (hle n)
    (by positivity)

/-- The single-row letters `[[1, 2], [0, 1]]`, `[[1, 0], [2, 1]]` of a wall of two spheres pairing
to two. -/
noncomputable def affineLetters : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![1, 2; 0, 1], !![1, 0; 2, 1]]

/-- On the orthant the forward operator of `affineLetters` is `I + G`, `G = [[0, 2], [2, 0]]`. -/
theorem maxMulVec_affine {x : Fin 2 → ℝ} (hx : 0 ≤ x) :
    maxMulVec affineLetters x = (!![1, 2; 2, 1] : Matrix (Fin 2) (Fin 2) ℝ).mulVec x := by
  have h0 : 0 ≤ x 0 := hx 0
  have h1 : 0 ≤ x 1 := hx 1
  ext i
  rw [maxMulVec_apply]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun a _ => ?_
    fin_cases a <;> fin_cases i <;>
      simp [affineLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> linarith
  · fin_cases i
    · calc _ = (affineLetters 0).mulVec x 0 := by
            simp [affineLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        _ ≤ _ := Finset.le_sup' (fun a => (affineLetters a).mulVec x 0) (Finset.mem_univ 0)
    · calc _ = (affineLetters 1).mulVec x 1 := by
            simp [affineLetters, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        _ ≤ _ := Finset.le_sup' (fun a => (affineLetters a).mulVec x 1) (Finset.mem_univ 1)

lemma affineLetters_nonneg : ∀ a i j, 0 ≤ affineLetters a i j := by
  intro a i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [affineLetters]

/-- **The forward operator of `affineLetters` has cycle time `3`**: `𝟙` is an eigenvector of
`I + G` with eigenvalue `1 + ρ(G) = 3`. -/
theorem cycleTime_maxMulVec_affine : cycleTime (maxMulVec affineLetters) = 3 := by
  refine (monotoneHomogeneous_maxMulVec affineLetters_nonneg).cycleTime_eq_of_eigenvector
    (x := 1) one_pos (fun _ => le_rfl) ?_
  rw [maxMulVec_affine zero_le_one]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- The joint spectral radius of `affineLetters` is `1 + √2`. -/
theorem jointSpectralRadius_affine : Matrix.jointSpectralRadius affineLetters = 1 + √2 := by
  have h := Matrix.jointSpectralRadius_unipotent_pair (s := 2) (by norm_num)
  have hsq : √((2 : ℝ) ^ 2 + 4) = 2 * √2 := by
    rw [show (2 : ℝ) ^ 2 + 4 = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num) 2,
      Real.sqrt_sq (by norm_num)]
  rw [hsq] at h
  rw [show affineLetters = ![!![1, (2 : ℝ); 0, 1], !![1, 0; (2 : ℝ), 1]] from rfl, h]
  ring

/-- **The forward operator overestimates the alphabet**: for `affineLetters`,
`JSR = 1 + √2 < 3 = R(Φ)`. -/
theorem jointSpectralRadius_lt_cycleTime_affine :
    Matrix.jointSpectralRadius affineLetters < cycleTime (maxMulVec affineLetters) := by
  rw [jointSpectralRadius_affine, cycleTime_maxMulVec_affine]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

end Forward
