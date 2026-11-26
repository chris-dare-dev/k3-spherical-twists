/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.JointSpectralRadius

/-!
# The joint spectral radius of the single twists of a bipartite graph

Let `G ≥ 0` be a real square matrix, the weighted graph of a configuration of spherical
objects, and let `P_k = 1 + e_k G_{k*}` (`Matrix.graphTransvection G k`) be the single twist at
the vertex `k` acting on count vectors: row `k` of `G` is added to row `k` of the identity. This
is the letter matrix of the domination recursion of a twist system. Suppose `G` is **bipartite**
for a two-colouring `p` (`G i j = 0` whenever `p i = p j`, so in particular the diagonal vanishes)
and its entries are at most `s ≥ 1`. Then

* `Matrix.jointSpectralRadius_graphTransvection_le`: `JSR(P_k) ≤ ρ_s = (s + √(s² + 4))/2`;
* `Matrix.jointSpectralRadius_graphTransvection_bipartite`: equality holds as soon as some edge
  has `G i₀ j₀ = G j₀ i₀ = s`.

The upper bound is the compression to two counts: for `v ≥ 0` let `X`, `Y` be the sums of `v` over
the two colours. A twist at a vertex of the first colour changes only that vertex, by at most
`s Y`, so `(X, Y) ↦ (X + sY, Y)` dominates it; a twist of the second colour is dominated by
`(X, Y) ↦ (X, Y + sX)` (`Matrix.partSums_graphTransvection_mulVec_le`). The words of `P` are
thus dominated by the words of the pair `[[1, s], [0, 1]]`, `[[1, 0], [s, 1]]`, whose joint
spectral radius is `ρ_s` (`Matrix.jointSpectralRadius_unipotent_pair`), independently of the
valence of the vertices. For the lower bound, `P_{i₀} P_{j₀}` has the eigenvector
`ρ_s e_{i₀} + e_{j₀}` with eigenvalue `ρ_s²` on a heaviest edge.

For an odd cycle the bound fails: the triangle has joint spectral radius at least the tribonacci
constant (`Matrix.exists_tribonacci_le_jointSpectralRadius_triangle`), above the golden ratio
`ρ_1`.
-/

open Filter Topology

namespace Matrix

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Comparing joint spectral radii -/

/-- If every word maximum of `A` is at most `C` times the corresponding word maximum of `B`, then
`JSR(A) ≤ JSR(B)`. -/
theorem jointSpectralRadius_le_of_sphereMax_le {κ α β : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (A : α → Matrix ι ι ℝ)
    (B : β → Matrix κ κ ℝ) {C : ℝ} (hC : 0 < C)
    (h : ∀ n, Monoid.sphereMax A (‖·‖) n ≤ C * Monoid.sphereMax B (‖·‖) n) :
    jointSpectralRadius A ≤ jointSpectralRadius B := by
  have hlim : Tendsto (fun n : ℕ => C ^ (n : ℝ)⁻¹ * Monoid.sphereMax B (‖·‖) n ^ (n : ℝ)⁻¹)
      atTop (𝓝 (jointSpectralRadius B)) := by
    simpa using (Real.tendsto_const_rpow_inv hC).mul (tendsto_jointSpectralRadius B)
  refine le_of_tendsto_of_tendsto (tendsto_jointSpectralRadius A) hlim
    (Eventually.of_forall fun n => ?_)
  dsimp only
  rw [← Real.mul_rpow hC.le (Monoid.sphereMax_nonneg B (fun _ => norm_nonneg _) n)]
  exact Real.rpow_le_rpow (Monoid.sphereMax_nonneg A (fun _ => norm_nonneg _) n) (h n)
    (by positivity)

/-- **Exponential bound below the joint spectral radius.** If `JSR(A) < R`, then every word
maximum satisfies `max_{|w| = n} ‖A_w‖ ≤ C Rⁿ` for one constant `C`. -/
theorem exists_sphereMax_le_mul_pow {α : Type*} [Fintype α] [Nonempty α] (A : α → Matrix ι ι ℝ)
    {R : ℝ} (hR : jointSpectralRadius A < R) :
    ∃ C, ∀ n, Monoid.sphereMax A (‖·‖) n ≤ C * R ^ n := by
  have hR0 : 0 < R := (jointSpectralRadius_nonneg A).trans_lt hR
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((tendsto_jointSpectralRadius A).eventually (gt_mem_nhds hR)).and (eventually_ne_atTop 0))
  have hS : ∀ n, 0 ≤ Monoid.sphereMax A (‖·‖) n := Monoid.sphereMax_nonneg A fun _ => norm_nonneg _
  set C₀ := ∑ k ∈ Finset.range N, Monoid.sphereMax A (‖·‖) k / R ^ k with hC₀
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun k _ => div_nonneg (hS k) (by positivity)
  refine ⟨1 + C₀, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · have h1 : Monoid.sphereMax A (‖·‖) n / R ^ n ≤ C₀ :=
      Finset.single_le_sum (f := fun k => Monoid.sphereMax A (‖·‖) k / R ^ k)
        (fun k _ => div_nonneg (hS k) (by positivity)) (Finset.mem_range.2 hn)
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith [pow_pos hR0 n]
  · obtain ⟨h1, h2⟩ := hN n hn
    have := (Real.rpow_inv_le_iff_of_pos (hS n) hR0.le
      (by exact_mod_cast Nat.pos_of_ne_zero h2)).1 h1.le
    rw [Real.rpow_natCast] at this
    nlinarith [pow_pos hR0 n]

/-! ### Single twists on count vectors -/

/-- The single twist at the vertex `k` of a weighted graph `G` on count vectors:
`P_k = 1 + e_k G_{k*}`, the identity with row `k` of `G` added to row `k`. -/
def graphTransvection (G : Matrix ι ι ℝ) (k : ι) : Matrix ι ι ℝ :=
  1 + of fun a b => if a = k then G k b else 0

lemma graphTransvection_mulVec_apply (G : Matrix ι ι ℝ) (k : ι) (v : ι → ℝ) (a : ι) :
    (graphTransvection G k *ᵥ v) a = v a + if a = k then (G *ᵥ v) k else 0 := by
  simp only [graphTransvection, add_mulVec, one_mulVec, Pi.add_apply]
  congr 1
  by_cases ha : a = k
  · subst ha
    simp [mulVec, dotProduct]
  · simp [mulVec, dotProduct, ha]

omit [Fintype ι] in
lemma graphTransvection_nonneg {G : Matrix ι ι ℝ} (hG : ∀ i j, 0 ≤ G i j) (k : ι) :
    ∀ i j, 0 ≤ graphTransvection G k i j := by
  intro i j
  show 0 ≤ (1 + of fun a b => if a = k then G k b else 0 : Matrix ι ι ℝ) i j
  rw [Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> linarith [hG k j]

/-! ### The compression to two counts -/

/-- The sums of a vector over the two colours of `p`: first over `p i = true`, then over
`p i = false`. -/
def partSums (p : ι → Bool) (v : ι → ℝ) : Fin 2 → ℝ :=
  ![∑ i ∈ Finset.univ.filter (fun i => p i = true), v i,
    ∑ i ∈ Finset.univ.filter (fun i => p i = false), v i]

/-- The pair of unipotent matrices `[[1, s], [0, 1]]`, `[[1, 0], [s, 1]]`. -/
def unipotentPair (s : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ := ![!![1, s; 0, 1], !![1, 0; s, 1]]

/-- The letter of the pair that dominates a twist at a vertex of colour `b`. -/
def colourIndex (b : Bool) : Fin 2 := if b then 0 else 1

lemma unipotentPair_nonneg {s : ℝ} (hs : 0 ≤ s) (a : Fin 2) : ∀ i j, 0 ≤ unipotentPair s a i j := by
  intro i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [unipotentPair, hs]

omit [DecidableEq ι] in
lemma partSums_nonneg (p : ι → Bool) {v : ι → ℝ} (hv : 0 ≤ v) : 0 ≤ partSums p v := by
  intro k
  fin_cases k <;> simp only [partSums, Fin.zero_eta, Fin.mk_one, cons_val_zero, cons_val_one,
    Pi.zero_apply] <;> exact Finset.sum_nonneg fun i _ => hv i

variable {G : Matrix ι ι ℝ} (hG : ∀ i j, 0 ≤ G i j) (p : ι → Bool)
  (hbip : ∀ i j, p i = p j → G i j = 0) {s : ℝ} (hle : ∀ i j, G i j ≤ s)

omit [DecidableEq ι] in
include hbip hle in
/-- At a vertex `k`, `(G v)_k ≤ s · (the sum of v over the other colour)` for `v ≥ 0`. -/
lemma mulVec_apply_le_of_bipartite {v : ι → ℝ} (hv : 0 ≤ v) (k : ι) :
    (G *ᵥ v) k ≤ s * ∑ j ∈ Finset.univ.filter (fun j => p j = !p k), v j := by
  simp only [mulVec, dotProduct]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => p j = !p k)]
  have h0 : ∑ j ∈ Finset.univ.filter (fun j => ¬p j = !p k), G k j * v j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := (Finset.mem_filter.1 hj).2
    have : p k = p j := by cases hk : p k <;> cases hpj : p j <;> simp_all
    rw [hbip k j this, zero_mul]
  rw [h0, add_zero, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle k j) (hv j)

include hG hbip hle in
/-- **One twist is dominated by one unipotent letter on the two counts.** For `v ≥ 0`, the two
colour sums of `P_k v` are at most the image of the two colour sums of `v` under
`[[1, s], [0, 1]]` (when `p k = true`) or `[[1, 0], [s, 1]]` (when `p k = false`). -/
theorem partSums_graphTransvection_mulVec_le {v : ι → ℝ} (hv : 0 ≤ v) (k : ι) :
    partSums p (graphTransvection G k *ᵥ v) ≤
      unipotentPair s (colourIndex (p k)) *ᵥ partSums p v := by
  have hsplit : ∀ b : Bool, ∑ i ∈ Finset.univ.filter (fun i => p i = b),
      (graphTransvection G k *ᵥ v) i =
        ∑ i ∈ Finset.univ.filter (fun i => p i = b), v i + if p k = b then (G *ᵥ v) k else 0 := by
    intro b
    simp only [graphTransvection_mulVec_apply, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_filter, Finset.mem_univ, true_and]
  have hGk := mulVec_apply_le_of_bipartite p hbip hle hv k
  have hX : partSums p (graphTransvection G k *ᵥ v) 0 =
      partSums p v 0 + if p k = true then (G *ᵥ v) k else 0 := hsplit true
  have hY : partSums p (graphTransvection G k *ᵥ v) 1 =
      partSums p v 1 + if p k = false then (G *ᵥ v) k else 0 := hsplit false
  have e0 : ∑ j ∈ Finset.univ.filter (fun j => p j = true), v j = partSums p v 0 := rfl
  have e1 : ∑ j ∈ Finset.univ.filter (fun j => p j = false), v j = partSums p v 1 := rfl
  have hs : 0 ≤ s := (hG k k).trans (hle k k)
  intro c
  cases hk : p k
  · simp only [hk, Bool.not_false, e0] at hGk
    have hU : unipotentPair s (colourIndex false) *ᵥ partSums p v =
        ![partSums p v 0, s * partSums p v 0 + partSums p v 1] := by
      ext i
      fin_cases i <;> simp [unipotentPair, colourIndex, mulVec, dotProduct, Fin.sum_univ_two]
    rw [hU]
    fin_cases c
    · simp only [Fin.zero_eta, cons_val_zero, hX, hk, Bool.false_eq_true, ↓reduceIte, add_zero,
        le_refl]
    · simp only [Fin.mk_one, cons_val_one, cons_val_zero, hY, hk, ↓reduceIte]
      linarith
  · simp only [hk, Bool.not_true, e1] at hGk
    have hU : unipotentPair s (colourIndex true) *ᵥ partSums p v =
        ![partSums p v 0 + s * partSums p v 1, partSums p v 1] := by
      ext i
      fin_cases i <;> simp [unipotentPair, colourIndex, mulVec, dotProduct, Fin.sum_univ_two]
    rw [hU]
    fin_cases c
    · simp only [Fin.zero_eta, cons_val_zero, hX, hk, ↓reduceIte]
      linarith
    · simp only [Fin.mk_one, cons_val_one, cons_val_zero, hY, hk, Bool.true_eq_false,
        ↓reduceIte, add_zero, le_refl]

include hG hbip hle in
/-- **A word of twists is dominated by the word of unipotent letters** on the two counts. -/
theorem partSums_prod_mulVec_le (hs : 0 ≤ s) (l : List ι) {v : ι → ℝ} (hv : 0 ≤ v) :
    0 ≤ (l.map (graphTransvection G)).prod *ᵥ v ∧
      partSums p ((l.map (graphTransvection G)).prod *ᵥ v) ≤
        (l.map (unipotentPair s ∘ colourIndex ∘ p)).prod *ᵥ partSums p v := by
  induction l with
  | nil => simpa using hv
  | cons k l ih =>
    obtain ⟨h0, h1⟩ := ih
    simp only [List.map_cons, List.prod_cons, ← mulVec_mulVec, Function.comp_apply]
    refine ⟨mulVec_nonneg (graphTransvection_nonneg hG k) h0, ?_⟩
    exact (partSums_graphTransvection_mulVec_le hG p hbip hle h0 k).trans
      (mulVec_mono (unipotentPair_nonneg hs _) h1)

omit [DecidableEq ι] in
lemma norm_partSums_one_le (p : ι → Bool) : ‖partSums p 1‖ ≤ Fintype.card ι := by
  refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).2 fun k => ?_
  have hle : ∀ b : Bool, ∑ i ∈ Finset.univ.filter (fun i => p i = b), (1 : ι → ℝ) i ≤
      Fintype.card ι := fun b => by
    simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_filter_le _ _
  rw [Real.norm_of_nonneg (partSums_nonneg p (v := (1 : ι → ℝ)) (fun _ => zero_le_one) k)]
  fin_cases k
  · exact hle true
  · exact hle false

include hG hbip hle in
/-- `‖P_w‖ ≤ 2 |ι| ‖Q_w‖` for a word `w` of twists and its unipotent shadow `Q_w`. -/
theorem norm_prod_graphTransvection_le (hs : 0 ≤ s) (l : List ι) :
    ‖(l.map (graphTransvection G)).prod‖ ≤
      2 * Fintype.card ι * ‖(l.map (unipotentPair s ∘ colourIndex ∘ p)).prod‖ := by
  set P := (l.map (graphTransvection G)).prod
  set Q := (l.map (unipotentPair s ∘ colourIndex ∘ p)).prod
  have h1 : (0 : ι → ℝ) ≤ 1 := fun _ => zero_le_one
  obtain ⟨hP0, hPQ⟩ := partSums_prod_mulVec_le hG p hbip hle hs l h1
  have hPnn : ∀ i j, 0 ≤ P i j := list_prod_apply_nonneg _ fun A hA i j => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hA
    exact graphTransvection_nonneg hG k i j
  -- `‖P‖ ≤ ‖P 𝟙‖`
  have hn1 : ‖P‖ ≤ ‖P *ᵥ 1‖ := by
    simpa using mul_norm_le_norm_mulVec hPnn one_pos (c := 1) fun _ => le_rfl
  -- `‖P 𝟙‖ ≤ X + Y ≤ 2 ‖(X, Y)‖`
  set w := P *ᵥ 1
  have hsum : ‖w‖ ≤ partSums p w 0 + partSums p w 1 := by
    refine (pi_norm_le_iff_of_nonneg (add_nonneg (partSums_nonneg p hP0 0)
      (partSums_nonneg p hP0 1))).2 fun i => ?_
    rw [Real.norm_of_nonneg (hP0 i)]
    simp only [partSums, cons_val_zero, cons_val_one]
    cases hi : p i
    · have h1 := Finset.single_le_sum (s := Finset.univ.filter (fun i => p i = false)) (f := w)
        (fun j _ => hP0 j) (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
      have h2 := Finset.sum_nonneg (s := Finset.univ.filter (fun i => p i = true)) (f := w)
        (fun j _ => hP0 j)
      linarith
    · have h1 := Finset.single_le_sum (s := Finset.univ.filter (fun i => p i = true)) (f := w)
        (fun j _ => hP0 j) (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
      have h2 := Finset.sum_nonneg (s := Finset.univ.filter (fun i => p i = false)) (f := w)
        (fun j _ => hP0 j)
      linarith
  have hXY : partSums p w 0 + partSums p w 1 ≤ 2 * ‖partSums p w‖ := by
    have h0 := norm_le_pi_norm (partSums p w) 0
    have h1 := norm_le_pi_norm (partSums p w) 1
    rw [Real.norm_of_nonneg (partSums_nonneg p hP0 0)] at h0
    rw [Real.norm_of_nonneg (partSums_nonneg p hP0 1)] at h1
    linarith
  -- `‖(X, Y)‖ ≤ ‖Q (X₀, Y₀)‖ ≤ ‖Q‖ |ι|`
  have hQ : ‖partSums p w‖ ≤ ‖Q‖ * Fintype.card ι :=
    (norm_le_norm_of_nonneg_of_le (partSums_nonneg p hP0) hPQ).trans
      ((linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_left (norm_partSums_one_le p) (norm_nonneg _)))
  calc ‖P‖ ≤ ‖w‖ := hn1
    _ ≤ 2 * ‖partSums p w‖ := hsum.trans hXY
    _ ≤ 2 * (‖Q‖ * Fintype.card ι) := by gcongr
    _ = 2 * Fintype.card ι * ‖Q‖ := by ring

variable [Nonempty ι]

include hG hbip hle in
/-- **The upper bound** `JSR(P_k) ≤ ρ_s = (s + √(s² + 4))/2` for the single twists of a bipartite
graph with weights at most `s ≥ 1`, at every valence. -/
theorem jointSpectralRadius_graphTransvection_le (hs : 1 ≤ s) :
    jointSpectralRadius (graphTransvection G) ≤ (s + √(s ^ 2 + 4)) / 2 := by
  rw [← jointSpectralRadius_unipotent_pair hs]
  have hcard : (0 : ℝ) < 2 * Fintype.card ι := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    positivity
  refine jointSpectralRadius_le_of_sphereMax_le (graphTransvection G)
    ![!![1, s; 0, 1], !![1, 0; s, 1]] hcard fun n => ?_
  refine Monoid.sphereMax_le _ _ fun w => ?_
  have h := norm_prod_graphTransvection_le hG p hbip hle (by linarith) (List.ofFn w)
  rw [List.map_ofFn, List.map_ofFn] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hcard.le)
  have := Monoid.le_sphereMax ![!![1, s; 0, 1], !![1, 0; s, 1]] (‖·‖)
    (fun i => colourIndex (p (w i)))
  exact le_of_eq_of_le (by rfl) this

include hG hbip hle in
/-- **The joint spectral radius of the single twists of a bipartite graph.** If `G ≥ 0` is
bipartite for `p`, its weights are at most `s ≥ 1`, and some edge has `G i₀ j₀ = G j₀ i₀ = s`,
then the twists `P_k = 1 + e_k G_{k*}` have joint spectral radius `ρ_s = (s + √(s² + 4))/2`. -/
theorem jointSpectralRadius_graphTransvection_bipartite (hs : 1 ≤ s) {i₀ j₀ : ι}
    (hij : G i₀ j₀ = s) (hji : G j₀ i₀ = s) :
    jointSpectralRadius (graphTransvection G) = (s + √(s ^ 2 + 4)) / 2 := by
  refine le_antisymm (jointSpectralRadius_graphTransvection_le hG p hbip hle hs) ?_
  set ρ := (s + √(s ^ 2 + 4)) / 2 with hρdef
  have hsq : √(s ^ 2 + 4) ^ 2 = s ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hρ0 : 0 < ρ := by
    have := Real.sqrt_nonneg (s ^ 2 + 4)
    rw [hρdef]
    linarith
  have hρsq : ρ ^ 2 = s * ρ + 1 := by rw [hρdef]; nlinarith [hsq]
  have hne : i₀ ≠ j₀ := by
    rintro rfl
    have := hbip i₀ i₀ rfl
    linarith
  -- the eigenvector `ρ e_{i₀} + e_{j₀}` of `P_{i₀} P_{j₀}`
  set v : ι → ℝ := fun a => if a = i₀ then ρ else if a = j₀ then 1 else 0 with hv
  have hv0 : 0 ≤ v := fun a => by simp only [hv, Pi.zero_apply]; split_ifs <;> linarith
  have hvne : v ≠ 0 := fun h => by
    have := congrFun h j₀
    simp [hv, hne.symm] at this
  set M := (List.ofFn (graphTransvection G ∘ ![i₀, j₀])).prod with hM
  have hMeq : M = graphTransvection G i₀ * graphTransvection G j₀ := by
    simp [hM, List.ofFn_succ]
  have hMnn : ∀ i j, 0 ≤ M i j := by
    intro i j
    rw [hMeq, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ =>
      mul_nonneg (graphTransvection_nonneg hG i₀ i l) (graphTransvection_nonneg hG j₀ l j)
  -- `(G v)_{j₀} ≥ s ρ` and `(G w)_{i₀} ≥ s w_{j₀}`
  have hGv : s * ρ ≤ (G *ᵥ v) j₀ := by
    have := Finset.single_le_sum (f := fun l => G j₀ l * v l)
      (fun l _ => mul_nonneg (hG j₀ l) (hv0 l)) (Finset.mem_univ i₀)
    simpa [mulVec, dotProduct, hv, hji] using this
  set w := graphTransvection G j₀ *ᵥ v with hw
  have hw0 : 0 ≤ w := mulVec_nonneg (graphTransvection_nonneg hG j₀) hv0
  have hwj : ρ ^ 2 ≤ w j₀ := by
    rw [hw, graphTransvection_mulVec_apply]
    simp only [↓reduceIte]
    have : v j₀ = 1 := by simp [hv, hne.symm]
    rw [this, hρsq]
    linarith
  have hwi : w i₀ = ρ := by
    rw [hw, graphTransvection_mulVec_apply]
    simp [hv, hne]
  have hGw : s * w j₀ ≤ (G *ᵥ w) i₀ := by
    have := Finset.single_le_sum (f := fun l => G i₀ l * w l)
      (fun l _ => mul_nonneg (hG i₀ l) (hw0 l)) (Finset.mem_univ j₀)
    simpa [mulVec, dotProduct, hij] using this
  have hMv : ρ ^ 2 • v ≤ M *ᵥ v := by
    rw [hMeq, ← mulVec_mulVec]
    intro a
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [graphTransvection_mulVec_apply]
    by_cases hai : a = i₀
    · subst hai
      simp only [↓reduceIte, hv]
      have : ρ ^ 2 * ρ = ρ + s * ρ ^ 2 := by nlinarith [hρsq]
      nlinarith [hGw, hwj]
    · by_cases haj : a = j₀
      · subst haj
        simp only [hai, ↓reduceIte, add_zero, hv]
        nlinarith [hwj]
      · simp only [hai, ↓reduceIte, add_zero, hv, haj, mul_zero]
        exact hw0 a
  have hgr : ρ ^ 2 ≤ gelfandRadius M := le_gelfandRadius_of_smul_le_mulVec hMnn hv0 hvne hMv
  have hJ := gelfandRadius_rpow_le_jointSpectralRadius (graphTransvection G) two_ne_zero
    ![i₀, j₀]
  refine le_trans ?_ hJ
  calc ρ = (ρ ^ 2) ^ ((2 : ℕ) : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast hρ0.le two_ne_zero).symm
    _ ≤ gelfandRadius M ^ ((2 : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow (by positivity) hgr (by positivity)

end Matrix
