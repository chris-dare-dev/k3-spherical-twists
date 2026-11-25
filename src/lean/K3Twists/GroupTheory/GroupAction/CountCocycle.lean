/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.GelfandRadius
import K3Twists.LinearAlgebra.Matrix.SignRule
import K3Twists.Order.Squeeze

/-!
# Count cocycles: the growth sandwich and exact rates on tight seeds

A *count cocycle* records, for objects `Y` acted on by letters `T_a` of a monoid, a nonnegative
count vector `c(Y) ∈ ℝ^ι` (for instance the multiplicities of the centres in a tower presenting
`Y`) and a signed vector `v(Y)` (for instance the class of `Y` in the basis of the centres) with
`|v(Y)| ≤ c(Y)` entrywise. The letters act on counts by nonnegative matrices, up to domination,
and on signed vectors by matrices:

  `c(T_a Y) ≤ P_a c(Y)`,  `v(T_a Y) = E_a v(Y)`.

For a word `W` with matrices `P_W` and `E_W`:

* **Upper bound.** `‖c(Wⁿ Y)‖ ≤ C rⁿ` for every `r > ρ(P_W)`
  (`CountCocycleHypotheses.norm_count_pow_le`).
* **Lower bound.** If the seed meets the top of the spectrum of `E_W`, in the sense that
  `‖E_Wⁿ v(Y)‖^{1/n} → ρ(E_W)` (a hypothesis), then `‖c(Wⁿ Y)‖ ≥ rⁿ` eventually for every
  `r < ρ(E_W)` (`CountCocycleHypotheses.eventually_pow_le_norm_count`).
* **Domination.** If `|E_a| ≤ P_a` entrywise for every letter then `ρ(E_W) ≤ ρ(P_W)`
  (`CountCocycleHypotheses.gelfandRadius_signedWord_le`).

Here `ρ` is the Gelfand radius `lim ‖Aⁿ‖^{1/n}`, which equals the complex spectral radius of the
complexified matrix (`Matrix.spectralRadius_map_ofReal`).

**Sign coherence** (`CountCocycleHypotheses.SignCoherent`) is a diagonal of signs `D` with
`D E_a D = P_a` for every letter (the sign rule `Matrix.signRule_letter` with the parity-graded
form). A *tight* object has `v(Y) = D c(Y)`. Then the order-theoretic squeeze
(`Order.squeeze_orbit`) makes every domination along a word an equality and keeps the orbit
tight (`CountCocycleHypotheses.tight_word`); for a tight seed with counts bounded below,
`‖c(Wⁿ Y)‖^{1/n} → ρ(P_W) = ρ(E_W)` (`CountCocycleHypotheses.tendsto_tight`), with no
irreducibility, primitivity or Perron vector.

## Main definitions

* `CountCocycleHypotheses`: counts, signed vectors, letter matrices, domination and linearity;
* `CountCocycleHypotheses.SignCoherent`, `CountCocycleHypotheses.IsTight`.

## Main results

* `CountCocycleHypotheses.count_word_le`, `signed_word`: the cocycle along words;
* `norm_count_pow_le`, `eventually_pow_le_norm_count`, `gelfandRadius_signedWord_le`: the
  growth sandwich `ρ(E_W) ≤ λ ≤ ρ(P_W)`;
* `tight_word`, `tendsto_tight`: exact counts and the exact rate on tight seeds;
* `Matrix.gelfandRadius_conj_sign`: conjugation by signs preserves the Gelfand radius.
-/

open Filter Topology Matrix
open scoped Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation by a diagonal of signs preserves the Gelfand radius. -/
theorem gelfandRadius_conj_sign {d : ι → ℝ} (hd : IsSign d) (P : Matrix ι ι ℝ) :
    gelfandRadius (diagonal d * P * diagonal d) = gelfandRadius P := by
  rw [mul_assoc, gelfandRadius_mul_comm, mul_assoc, hd.diagonal_mul_self, mul_one]

end Matrix

/-- **Count cocycle hypotheses.** A monoid `M` acting on objects, letters `T_a ∈ M`, nonnegative
count vectors and signed vectors indexed by `ι`, with `|v| ≤ c`, letter matrices `P_a ≥ 0`
dominating the counts and matrices `E_a` carrying the signed vectors. -/
structure CountCocycleHypotheses (M Obj ι α : Type*) [Monoid M] [MulAction M Obj] [Fintype ι]
    where
  /-- The letters. -/
  T : α → M
  /-- The count vector of an object. -/
  count : Obj → ι → ℝ
  /-- The signed vector of an object. -/
  signed : Obj → ι → ℝ
  /-- The count matrix of a letter. -/
  P : α → Matrix ι ι ℝ
  /-- The signed matrix of a letter. -/
  E : α → Matrix ι ι ℝ
  count_nonneg : ∀ Y i, 0 ≤ count Y i
  abs_signed_le : ∀ Y i, |signed Y i| ≤ count Y i
  P_nonneg : ∀ a i j, 0 ≤ P a i j
  /-- Domination of counts by the count matrix of a letter. -/
  count_smul_le : ∀ a Y, count (T a • Y) ≤ P a *ᵥ count Y
  /-- The signed vectors move linearly. -/
  signed_smul : ∀ a Y, signed (T a • Y) = E a *ᵥ signed Y

namespace CountCocycleHypotheses

variable {M Obj ι α : Type*} [Monoid M] [MulAction M Obj] [Fintype ι] [DecidableEq ι]
variable (C : CountCocycleHypotheses M Obj ι α)

/-- The monoid element of a word; the head letter acts last. -/
def word (w : List α) : M := (w.map C.T).prod

/-- The count matrix `P_W` of a word. -/
def countWord (w : List α) : Matrix ι ι ℝ := (w.map C.P).prod

/-- The signed matrix `E_W` of a word. -/
def signedWord (w : List α) : Matrix ι ι ℝ := (w.map C.E).prod

lemma countWord_nonneg (w : List α) (i j : ι) : 0 ≤ C.countWord w i j :=
  list_prod_apply_nonneg _ (fun A hA => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hA
    exact C.P_nonneg a) i j

lemma countWord_pow_nonneg (w : List α) (n : ℕ) (i j : ι) : 0 ≤ (C.countWord w ^ n) i j := by
  rw [← List.prod_replicate]
  exact list_prod_apply_nonneg _ (fun A hA => by
    rw [List.eq_of_mem_replicate hA]; exact C.countWord_nonneg w) i j

/-- Domination along a word: `c(W Y) ≤ P_W c(Y)`. -/
theorem count_word_le (w : List α) (Y : Obj) :
    C.count (C.word w • Y) ≤ C.countWord w *ᵥ C.count Y := by
  induction w with
  | nil => simp [word, countWord]
  | cons a w ih =>
    simp only [word, countWord, List.map_cons, List.prod_cons, mul_smul] at ih ⊢
    refine (C.count_smul_le a _).trans ?_
    rw [← Matrix.mulVec_mulVec]
    exact mulVec_mono (C.P_nonneg a) ih

/-- The signed vectors along a word: `v(W Y) = E_W v(Y)`. -/
theorem signed_word (w : List α) (Y : Obj) :
    C.signed (C.word w • Y) = C.signedWord w *ᵥ C.signed Y := by
  induction w with
  | nil => simp [word, signedWord]
  | cons a w ih =>
    simp only [word, signedWord, List.map_cons, List.prod_cons, mul_smul] at ih ⊢
    rw [C.signed_smul, ih, Matrix.mulVec_mulVec]

lemma count_pow_le (w : List α) (Y : Obj) (n : ℕ) :
    C.count (C.word w ^ n • Y) ≤ C.countWord w ^ n *ᵥ C.count Y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, pow_succ', ← Matrix.mulVec_mulVec]
    exact (C.count_word_le w _).trans
      (mulVec_mono (C.countWord_nonneg w) ih)

lemma signed_pow (w : List α) (Y : Obj) (n : ℕ) :
    C.signed (C.word w ^ n • Y) = C.signedWord w ^ n *ᵥ C.signed Y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, pow_succ', ← Matrix.mulVec_mulVec, C.signed_word, ih]

omit [DecidableEq ι] in
lemma norm_signed_le_norm_count (Y : Obj) : ‖C.signed Y‖ ≤ ‖C.count Y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  refine (C.abs_signed_le Y i).trans ?_
  have := norm_le_pi_norm (C.count Y) i
  rwa [Real.norm_eq_abs, abs_of_nonneg (C.count_nonneg Y i)] at this

/-- **The upper half of the sandwich.** For every `r` above the Gelfand radius of `P_W` there is a
constant `K` with `‖c(Wⁿ Y)‖ ≤ K rⁿ`. -/
theorem norm_count_pow_le (w : List α) (Y : Obj) {r : ℝ}
    (hr : gelfandRadius (C.countWord w) < r) :
    ∃ K, ∀ n : ℕ, ‖C.count (C.word w ^ n • Y)‖ ≤ K * r ^ n := by
  obtain ⟨K, -, hK⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt (C.countWord w) hr
  refine ⟨K * ‖C.count Y‖, fun n => ?_⟩
  have h1 : ‖C.count (C.word w ^ n • Y)‖ ≤ ‖C.countWord w ^ n *ᵥ C.count Y‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (C.count_nonneg _ i)]
    refine (C.count_pow_le w Y n i).trans ?_
    exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i)
  calc ‖C.count (C.word w ^ n • Y)‖ ≤ ‖C.countWord w ^ n *ᵥ C.count Y‖ := h1
    _ ≤ ‖C.countWord w ^ n‖ * ‖C.count Y‖ := linfty_opNorm_mulVec _ _
    _ ≤ K * r ^ n * ‖C.count Y‖ := by gcongr; exact hK n
    _ = K * ‖C.count Y‖ * r ^ n := by ring

/-- **The lower half of the sandwich.** If the seed meets the top of the spectrum of `E_W`,
`‖E_Wⁿ v(Y)‖^{1/n} → ρ(E_W)`, then `rⁿ ≤ ‖c(Wⁿ Y)‖` eventually for every `r < ρ(E_W)`. -/
theorem eventually_pow_le_norm_count (w : List α) (Y : Obj)
    (hseed : Tendsto (fun n : ℕ => ‖C.signedWord w ^ n *ᵥ C.signed Y‖ ^ (n : ℝ)⁻¹) atTop
      (𝓝 (gelfandRadius (C.signedWord w))))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < gelfandRadius (C.signedWord w)) :
    ∀ᶠ n : ℕ in atTop, r ^ n ≤ ‖C.count (C.word w ^ n • Y)‖ := by
  filter_upwards [hseed.eventually (lt_mem_nhds hr), eventually_gt_atTop 0] with n hn hn0
  have hpos : 0 ≤ ‖C.signedWord w ^ n *ᵥ C.signed Y‖ := norm_nonneg _
  have h1 : r ^ n ≤ ‖C.signedWord w ^ n *ᵥ C.signed Y‖ := by
    have := pow_le_pow_left₀ hr0 hn.le n
    rwa [Real.rpow_inv_natCast_pow hpos hn0.ne'] at this
  rw [← C.signed_pow] at h1
  exact h1.trans (C.norm_signed_le_norm_count _)

/-- **Domination of spectral radii.** If `|E_a| ≤ P_a` entrywise for every letter, then
`ρ(E_W) ≤ ρ(P_W)` for every word. -/
theorem gelfandRadius_signedWord_le (hEP : ∀ a i j, |C.E a i j| ≤ C.P a i j) (w : List α) :
    gelfandRadius (C.signedWord w) ≤ gelfandRadius (C.countWord w) := by
  refine gelfandRadius_le_of_abs_le fun i j => ?_
  have := abs_list_prod_le (w.map fun a => (C.E a, C.P a))
    (by
      intro p hp
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hp
      exact hEP a) i j
  simpa [signedWord, countWord, List.map_map, Function.comp_def] using this

/-! ### Sign coherence and tight seeds -/

/-- **Sign coherence**: a diagonal of signs conjugating every signed letter matrix into the count
matrix, `D E_a D = P_a` (the sign rule, with the parity-graded form). -/
def SignCoherent (d : ι → ℝ) : Prop :=
  IsSign d ∧ ∀ a, diagonal d * C.E a * diagonal d = C.P a

/-- An object is **tight** for the signs `d` if `v(Y) = d c(Y)`. -/
def IsTight (d : ι → ℝ) (Y : Obj) : Prop := C.signed Y = d * C.count Y

lemma signCoherent_conj {d : ι → ℝ} (hd : C.SignCoherent d) (a : α) (x : ι → ℝ) :
    C.E a *ᵥ (d * x) = d * (C.P a *ᵥ x) := by
  have hdx : ∀ x : ι → ℝ, d * x = diagonal d *ᵥ x := fun x => by
    funext i; simp [mulVec_diagonal]
  have hEm : C.E a = diagonal d * C.P a * diagonal d := by
    rw [← hd.2 a]; simp only [← mul_assoc]
    rw [hd.1.diagonal_mul_self, one_mul, mul_assoc, hd.1.diagonal_mul_self, mul_one]
  rw [hdx, hdx, mulVec_mulVec, mulVec_mulVec, hEm, mul_assoc, hd.1.diagonal_mul_self, mul_one]

/-- **The squeeze for one letter.** Under sign coherence, a tight object stays tight under every
letter and its count is exactly `P_a c(Y)`. -/
theorem tight_smul {d : ι → ℝ} (hd : C.SignCoherent d) {Y : Obj} (hY : C.IsTight d Y) (a : α) :
    C.IsTight d (C.T a • Y) ∧ C.count (C.T a • Y) = C.P a *ᵥ C.count Y := by
  have hφ : ∀ x : ι → ℝ, x ≤ (fun i => |(d * x) i|) := fun x i => by
    simp only [Pi.mul_apply, abs_mul, hd.1.abs_eq, one_mul]; exact le_abs_self _
  have hvc : (fun i => |C.signed (C.T a • Y) i|) ≤ C.count (C.T a • Y) :=
    fun i => C.abs_signed_le _ i
  obtain ⟨h1, h2⟩ := Order.squeeze_step (fun x i => |x i|) (fun x => d * x)
    (fun x => C.P a *ᵥ x) (fun x => C.E a *ᵥ x) hφ (C.signCoherent_conj hd a _)
    (C.count_smul_le a Y) (C.signed_smul a Y) hvc hY
  exact ⟨h2, h1⟩

/-- **The squeeze along a word.** Under sign coherence, the orbit of a tight object stays tight
and every domination is an equality: `c(W Y) = P_W c(Y)`. -/
theorem tight_word {d : ι → ℝ} (hd : C.SignCoherent d) {Y : Obj} (hY : C.IsTight d Y)
    (w : List α) :
    C.IsTight d (C.word w • Y) ∧ C.count (C.word w • Y) = C.countWord w *ᵥ C.count Y := by
  induction w with
  | nil => simpa [word, countWord] using hY
  | cons a w ih =>
    have := C.tight_smul hd ih.1 a
    simp only [word, countWord, List.map_cons, List.prod_cons, mul_smul] at ih this ⊢
    refine ⟨this.1, ?_⟩
    rw [this.2, ih.2, Matrix.mulVec_mulVec]

lemma tight_pow {d : ι → ℝ} (hd : C.SignCoherent d) {Y : Obj} (hY : C.IsTight d Y)
    (w : List α) (n : ℕ) :
    C.IsTight d (C.word w ^ n • Y) ∧
      C.count (C.word w ^ n • Y) = C.countWord w ^ n *ᵥ C.count Y := by
  induction n with
  | zero => simpa using hY
  | succ n ih =>
    have := C.tight_word hd ih.1 w
    rw [pow_succ', mul_smul, pow_succ', ← Matrix.mulVec_mulVec, ← ih.2]
    exact this

/-- **The exact rate on tight seeds.** Under sign coherence, for a tight seed whose counts are
bounded below by `m > 0`, `‖c(Wⁿ Y)‖^{1/n} → ρ(P_W)`, and `ρ(P_W) = ρ(E_W)`, which is the complex
spectral radius of `P_W`. No irreducibility, primitivity or Perron vector is used. -/
theorem tendsto_tight {d : ι → ℝ} (hd : C.SignCoherent d) {Y : Obj} (hY : C.IsTight d Y)
    {m : ℝ} (hm : 0 < m) (hc : ∀ i, m ≤ C.count Y i) (w : List α) :
    Tendsto (fun n : ℕ => ‖C.count (C.word w ^ n • Y)‖ ^ (n : ℝ)⁻¹) atTop
        (𝓝 (gelfandRadius (C.countWord w))) ∧
      gelfandRadius (C.signedWord w) = gelfandRadius (C.countWord w) ∧
      spectralRadius ℂ ((C.countWord w).map Complex.ofReal) =
        ENNReal.ofReal (gelfandRadius (C.countWord w)) := by
  refine ⟨?_, ?_, spectralRadius_map_ofReal _⟩
  · have hf : (fun n : ℕ => ‖C.count (C.word w ^ n • Y)‖ ^ (n : ℝ)⁻¹) =
        fun n : ℕ => ‖(C.countWord w ^ n) *ᵥ C.count Y‖ ^ (n : ℝ)⁻¹ :=
      funext fun n => by rw [(C.tight_pow hd hY w n).2]
    rw [hf]
    exact tendsto_rate_of_pos _ (C.countWord_nonneg w) _ hm hc
  · have hconj : diagonal d * C.signedWord w * diagonal d = C.countWord w := by
      have := hd.1.conj_list_prod (w.map fun a => (C.E a, C.P a))
      simpa [signedWord, countWord, List.map_map, Function.comp_def] using
        this (by
          intro p hp
          obtain ⟨a, -, rfl⟩ := List.mem_map.1 hp
          exact hd.2 a)
    rw [← hconj, gelfandRadius_conj_sign hd.1]

end CountCocycleHypotheses
