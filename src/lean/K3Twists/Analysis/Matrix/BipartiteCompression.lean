/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.GelfandRadius

/-!
# Compression of bipartite multitwists to Thurston matrices

Let `G` be a real `α × β` matrix, the intersection matrix between the two parts of a bipartite
configuration. Two multitwists act on pairs `z = (x, y)`, `x : α → ℝ`, `y : β → ℝ`, by the block
letters

* `A a : (x, y) ↦ (x + a G y, y)`,
* `B b : (x, y) ↦ (x, y + b Gᵀ x)`.

If `u : α → ℝ`, `v : β → ℝ` and `μ` satisfy `uᵀ G = μ vᵀ` and `G v = μ u`, the compression
`κ(x, y) = (u ⬝ x, v ⬝ y)` carries the letter `A a` to the Thurston matrix `[[1, aμ], [0, 1]]`
and `B b` to `[[1, 0], [bμ, 1]]`. This is Thurston's construction of pseudo-Anosov maps from two
multicurves (W. Thurston, *On the geometry and dynamics of diffeomorphisms of surfaces*,
Bull. Amer. Math. Soc. 19 (1988)): the compression is a semiconjugacy from the block action onto
the action of the corresponding product in `SL₂(ℝ)`.

## Main results

* `Matrix.BipartiteCompression.compress_act`, `compress_word`, `compress_iterate`: the
  semiconjugacy for one letter, a word and its iterates. Only the two relations `uᵀ G = μ vᵀ`
  and `G v = μ u` are used: no positivity, connectedness or Perron–Frobenius.
* `Matrix.BipartiteCompression.tendsto_rate_of_compress_pos`: if `G ≥ 0`, `u` and `v` take
  values between `m > 0` and `M`, the letters have nonnegative exponents and the seed `z ≥ 0`
  has compression at least `c > 0` in both coordinates, then the total mass `∑ x + ∑ y` of
  `Wⁿ z` grows at the rate `gelfandRadius` of the Thurston product of `W`.

## Conventions

A word `w : List Letter` acts by `List.foldr`, so its first letter acts last, as the first
factor of the matrix product `(w.map (thurston μ)).prod` does.
-/

open Filter Topology

namespace Matrix.BipartiteCompression

open scoped Matrix.Norms.Operator

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The block letters: `A a` adds `a G y` to `x`, `B b` adds `b Gᵀ x` to `y`. -/
inductive Letter
  | A (a : ℝ)
  | B (b : ℝ)

/-- The action of a block letter on pairs `(x, y)`. -/
def act (G : Matrix α β ℝ) : Letter → (α → ℝ) × (β → ℝ) → (α → ℝ) × (β → ℝ)
  | .A a, z => (z.1 + a • (G *ᵥ z.2), z.2)
  | .B b, z => (z.1, z.2 + b • (Gᵀ *ᵥ z.1))

/-- The Thurston matrix of a block letter. -/
def thurston (μ : ℝ) : Letter → Matrix (Fin 2) (Fin 2) ℝ
  | .A a => thurstonA a μ
  | .B b => thurstonB b μ

/-- The compression `(x, y) ↦ (u ⬝ x, v ⬝ y)`. -/
def compress (u : α → ℝ) (v : β → ℝ) (z : (α → ℝ) × (β → ℝ)) : Fin 2 → ℝ :=
  ![u ⬝ᵥ z.1, v ⬝ᵥ z.2]

/-- **Compression of one letter**, from `uᵀ G = μ vᵀ` and `G v = μ u` only. -/
theorem compress_act (G : Matrix α β ℝ) {u : α → ℝ} {v : β → ℝ} {μ : ℝ}
    (hu : u ᵥ* G = μ • v) (hv : G *ᵥ v = μ • u) (ℓ : Letter) (z : (α → ℝ) × (β → ℝ)) :
    compress u v (act G ℓ z) = thurston μ ℓ *ᵥ compress u v z := by
  have hv' : v ᵥ* Gᵀ = μ • u := by rw [vecMul_transpose, hv]
  cases ℓ with
  | A a =>
    funext k
    fin_cases k
    · simp [compress, act, thurston, thurstonA, mulVec, dotProduct_add, dotProduct_smul,
        dotProduct_mulVec, hu]
      ring
    · simp [compress, act, thurston, thurstonA, mulVec]
  | B b =>
    funext k
    fin_cases k
    · simp [compress, act, thurston, thurstonB, mulVec]
    · simp [compress, act, thurston, thurstonB, mulVec, dotProduct_add, dotProduct_smul,
        dotProduct_mulVec, hv']
      ring

/-- **Compression of a word**: the block action is semiconjugate to the `SL₂(ℝ)` product. -/
theorem compress_word (G : Matrix α β ℝ) {u : α → ℝ} {v : β → ℝ} {μ : ℝ}
    (hu : u ᵥ* G = μ • v) (hv : G *ᵥ v = μ • u) (w : List Letter) (z : (α → ℝ) × (β → ℝ)) :
    compress u v (w.foldr (act G) z) = (w.map (thurston μ)).prod *ᵥ compress u v z := by
  induction w with
  | nil => simp
  | cons ℓ w ih =>
    rw [List.foldr_cons, compress_act G hu hv, ih, List.map_cons, List.prod_cons, mulVec_mulVec]

/-- Compression of the iterates of a word. -/
theorem compress_iterate (G : Matrix α β ℝ) {u : α → ℝ} {v : β → ℝ} {μ : ℝ}
    (hu : u ᵥ* G = μ • v) (hv : G *ᵥ v = μ • u) (w : List Letter) (z : (α → ℝ) × (β → ℝ))
    (n : ℕ) :
    compress u v ((fun z => w.foldr (act G) z)^[n] z) =
      ((w.map (thurston μ)).prod ^ n) *ᵥ compress u v z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', compress_word G hu hv, ih, mulVec_mulVec, ← pow_succ']

/-! ### Nonnegative letters -/

/-- A letter with a nonnegative exponent. -/
def Letter.Nonneg : Letter → Prop
  | .A a => 0 ≤ a
  | .B b => 0 ≤ b

lemma act_nonneg (G : Matrix α β ℝ) (hG : ∀ i j, 0 ≤ G i j) (ℓ : Letter) (hℓ : ℓ.Nonneg)
    (z : (α → ℝ) × (β → ℝ)) (hz : 0 ≤ z.1 ∧ 0 ≤ z.2) :
    0 ≤ (act G ℓ z).1 ∧ 0 ≤ (act G ℓ z).2 := by
  cases ℓ with
  | A a =>
    refine ⟨fun i => ?_, hz.2⟩
    simp only [act, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact add_nonneg (hz.1 i) (mul_nonneg hℓ (mulVec_nonneg hG hz.2 i))
  | B b =>
    refine ⟨hz.1, fun i => ?_⟩
    simp only [act, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact add_nonneg (hz.2 i) (mul_nonneg hℓ (mulVec_nonneg (fun i j => hG j i) hz.1 i))

lemma foldr_act_nonneg (G : Matrix α β ℝ) (hG : ∀ i j, 0 ≤ G i j) (w : List Letter)
    (hw : ∀ ℓ ∈ w, ℓ.Nonneg) (z : (α → ℝ) × (β → ℝ)) (hz : 0 ≤ z.1 ∧ 0 ≤ z.2) :
    0 ≤ (w.foldr (act G) z).1 ∧ 0 ≤ (w.foldr (act G) z).2 := by
  induction w with
  | nil => simpa using hz
  | cons ℓ w ih =>
    rw [List.foldr_cons]
    exact act_nonneg G hG ℓ (hw ℓ (by simp)) _ (ih fun ℓ' h => hw ℓ' (by simp [h]))

lemma iterate_nonneg (G : Matrix α β ℝ) (hG : ∀ i j, 0 ≤ G i j) (w : List Letter)
    (hw : ∀ ℓ ∈ w, ℓ.Nonneg) (z : (α → ℝ) × (β → ℝ)) (hz : 0 ≤ z.1 ∧ 0 ≤ z.2) (n : ℕ) :
    0 ≤ ((fun z => w.foldr (act G) z)^[n] z).1 ∧
      0 ≤ ((fun z => w.foldr (act G) z)^[n] z).2 := by
  induction n with
  | zero => simpa using hz
  | succ n ih => rw [Function.iterate_succ_apply']; exact foldr_act_nonneg G hG w hw _ ih

omit [Fintype α] [Fintype β] in
lemma thurston_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (ℓ : Letter) (hℓ : ℓ.Nonneg) :
    ∀ i j, 0 ≤ thurston μ ℓ i j := by
  intro i j
  cases ℓ with
  | A a =>
    fin_cases i <;> fin_cases j <;> simp [thurston, thurstonA]
    exact mul_nonneg hℓ hμ
  | B b =>
    fin_cases i <;> fin_cases j <;> simp [thurston, thurstonB]
    exact mul_nonneg hℓ hμ

omit [Fintype α] [Fintype β] in
private lemma dotProduct_bounds {γ : Type*} [Fintype γ] {u x : γ → ℝ} {m M : ℝ} (hx : 0 ≤ x)
    (hlo : ∀ i, m ≤ u i) (hhi : ∀ i, u i ≤ M) :
    m * ∑ i, x i ≤ u ⬝ᵥ x ∧ u ⬝ᵥ x ≤ M * ∑ i, x i := by
  simp only [dotProduct, Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlo i) (hx i),
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hhi i) (hx i)⟩

/-- **Rate of a bipartite multitwist word.** Let `G ≥ 0` with `uᵀ G = μ vᵀ`, `G v = μ u`,
`μ ≥ 0`, and `u`, `v` taking values between `m > 0` and `M`. For a word `W` in letters with
nonnegative exponents and a seed `z ≥ 0` whose compression is at least `c > 0` in both
coordinates, the total mass `∑ x + ∑ y` of `Wⁿ z` grows at exactly the Gelfand radius of the
Thurston product of `W`. -/
theorem tendsto_rate_of_compress_pos (G : Matrix α β ℝ) (hG : ∀ i j, 0 ≤ G i j) {u : α → ℝ}
    {v : β → ℝ} {μ m M : ℝ} (hμ : 0 ≤ μ) (hm : 0 < m)
    (hu_lo : ∀ i, m ≤ u i) (hu_hi : ∀ i, u i ≤ M) (hv_lo : ∀ j, m ≤ v j) (hv_hi : ∀ j, v j ≤ M)
    (hu : u ᵥ* G = μ • v) (hv : G *ᵥ v = μ • u) (w : List Letter) (hw : ∀ ℓ ∈ w, ℓ.Nonneg)
    (z : (α → ℝ) × (β → ℝ)) (hz : 0 ≤ z.1 ∧ 0 ≤ z.2) {c : ℝ} (hc : 0 < c)
    (hκ : ∀ k, c ≤ compress u v z k) :
    Tendsto (fun n : ℕ => (∑ i, ((fun z => w.foldr (act G) z)^[n] z).1 i +
        ∑ j, ((fun z => w.foldr (act G) z)^[n] z).2 j) ^ (n : ℝ)⁻¹)
      atTop (𝓝 (gelfandRadius (w.map (thurston μ)).prod)) := by
  -- `m ≤ M` follows from the other hypotheses
  have hmM : m ≤ M := by
    rcases isEmpty_or_nonempty α with hα | ⟨⟨i⟩⟩
    · have := hκ 0
      simp [compress, dotProduct] at this
      linarith
    · exact (hu_lo i).trans (hu_hi i)
  set T := (w.map (thurston μ)).prod with hTdef
  have hT : ∀ i j, 0 ≤ T i j := list_prod_apply_nonneg _ (fun A hA => by
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hA
    exact thurston_nonneg hμ ℓ (hw ℓ hℓ))
  have hlim := tendsto_rate_of_pos T hT (compress u v z) hc hκ
  have hM : 0 < M := hm.trans_le hmM
  refine Real.tendsto_rpow_inv_of_bounds (H := fun n => ‖(T ^ n) *ᵥ compress u v z‖)
    (c := 1 / M) (C := 2 / m) (by positivity) (by positivity) (fun n => norm_nonneg _)
    (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_) hlim
  all_goals
    obtain ⟨hx, hy⟩ := iterate_nonneg G hG w hw z hz n
    set Z := (fun z => w.foldr (act G) z)^[n] z
    have hk : (T ^ n) *ᵥ compress u v z = compress u v Z :=
      (compress_iterate G hu hv w z n).symm
    have hx' := dotProduct_bounds hx hu_lo hu_hi
    have hy' := dotProduct_bounds hy hv_lo hv_hi
    have sx : 0 ≤ ∑ i, Z.1 i := Finset.sum_nonneg fun i _ => hx i
    have sy : 0 ≤ ∑ j, Z.2 j := Finset.sum_nonneg fun j _ => hy j
    have k0 : compress u v Z 0 = u ⬝ᵥ Z.1 := rfl
    have k1 : compress u v Z 1 = v ⬝ᵥ Z.2 := rfl
    simp only [hk]
  · -- lower bound: `‖κ‖ ≤ M · mass`
    have hnorm : ‖compress u v Z‖ ≤ M * (∑ i, Z.1 i + ∑ j, Z.2 j) := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      rw [Real.norm_eq_abs]
      fin_cases k
      · simp only [Fin.zero_eta, k0]
        rw [abs_of_nonneg (by nlinarith)]; nlinarith
      · simp only [Fin.mk_one, k1]
        rw [abs_of_nonneg (by nlinarith)]; nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM]
    linarith
  · -- upper bound: `m · mass ≤ 2 ‖κ‖`
    have h0 := norm_le_pi_norm (compress u v Z) 0
    have h1 := norm_le_pi_norm (compress u v Z) 1
    rw [Real.norm_eq_abs, k0] at h0
    rw [Real.norm_eq_abs, k1] at h1
    have a0 := le_abs_self (u ⬝ᵥ Z.1)
    have a1 := le_abs_self (v ⬝ᵥ Z.2)
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    nlinarith

end Matrix.BipartiteCompression
