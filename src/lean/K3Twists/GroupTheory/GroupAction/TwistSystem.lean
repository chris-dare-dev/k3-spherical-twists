/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.SpecificLimits.GrowthRate
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Mul

/-!
# Twist systems and the exponent of the centre counts

A *twist system* is a group acting on a set of objects, finitely many marked *centres* `S_i`, an
alphabet of group elements `T_a` (the *letters*), each with a centre `S_{c(a)}`, and a count
`h(U, V) ∈ ℕ`. The intended example is a finite set of spherical objects of a triangulated
category, their spherical twists, and the total dimension `h(U, V) = dim Ext^*(U, V)`; no
category, stability condition or K3 surface is needed for what is proved here.

The axioms used are:

* (A1) invariance, `h(gU, gV) = h(U, V)` (`HomTwistSystem₀.h_smul`);
* (U) the one-letter upper bound `h(U, T_a V) ≤ h(U, V) + h(U, S) h(S, V)`, `S = S_{c(a)}`
  (`HomTwistSystem₀.upper`): the long exact sequence of the twist triangle
  `Ext^*(S, V) ⊗ S → V → T_S V` (Seidel–Thomas, arXiv:math/0001043);
* (L) the one-letter lower bound `h(U, S) h(S, V) ≤ h(U, V) + h(U, T_a V)`
  (`HomTwistSystem₀.LowerBound`), from the same sequence;
* sphericity `h(S_i, S_i) = 2` (`HomTwistSystem₀.IsSpherical`), which makes the counts positive;
* directed connectivity: any two centres are joined by a chain of at most `d + 1` letters whose
  consecutive centres have `h ≥ 1` (`HomTwistSystem₀.DirectedConnected`).

The identity `T_S S = S[-1]`, read through `h` as `h(U, T_a S_{c(a)}) = h(U, S_{c(a)})`, is the
extra field of `HomTwistSystem`; it only zeroes the diagonal of the domination recursion
(`HomTwistSystem.toDomination`) and the exponent theorem does not use it. Sphericity is an input
of its own: the zero count satisfies every other axiom. Symmetry `h(U, V) = h(V, U)` (Serre
duality in a 2-Calabi–Yau category) is not assumed; it supplies the bound (U) for inverse letters
(`HomTwistSystem₀.upper_inv`, `HomTwistSystem₀.withInverses`), and it is needed there: (U) for
`T_a⁻¹` does not follow from (A1), (U) for `T_a` and the identity `T_S S = S[-1]`.

## Main definitions

* `DominationSystem`: a monoid action with centres, letters and a family of tests closed under
  pulling back along letters, with the upper bound (U) when the second argument is a centre;
* `HomTwistSystem₀`, `HomTwistSystem`: the axioms above, without and with `T_S S = S[-1]`;
* `HomTwistSystem₀.maxCount H q`: `P_q = max h(S_i, W S_j)` over centres and words `|W| ≤ q`;
* `HomTwistSystem₀.homExponent H`: `η = lim log P_N / N`.

## Main results

* `DominationSystem.test_word_le`: the domination recursion with constant one, every test of
  `W S_j` is bounded by the tests of the centres weighted by the column `P_W e_j` of the product
  of the transvections `1 + e_{c(a)} G_a` (`DominationSystem.step_eq_mulVec`);
* `HomTwistSystem₀.tendsto_homExponent`, `homExponent_lower`, `homExponent_upper`: **the exponent
  of the centre counts.** `log P_N / N` converges to `η`, and for every `q`
  `log(P_q / 2^{d+1})/(q + d + 1) ≤ η ≤ log(1 + q P_q)/q` (the upper bound for `q > 0`);
* `HomTwistSystem₀.homExponent_nonneg`, `maxCount_succ_le`, `homExponent_width`: `η ≥ 0`,
  `P_{q+1} ≤ (1 + g) P_q` with `g = max h(S_i, S_k)`, and the two certificates differ by at most
  `log(q + 1)/q + (d + 1)/(q + d + 1) (log(1 + g) + log g / q + log 2)`, so the depth `q` that
  reaches a given accuracy is known before any word is computed;
* `HomTwistSystem₀.maxCount_eq_of_map`, `homExponent_eq_of_map`: a map of twist systems that
  matches centres and letters and preserves counts preserves every `P_q`, hence `η`: the exponent
  depends only on the centres, the letters and the counts between their translates.

## Implementation notes

`η` is the exponent of the counts between centres. The exponent of the masses of `⊕ S_i` under a
stability condition agrees with it once `h(S_i, Y)` and the mass of `Y` are comparable, which is
an input not treated here. The certificates follow from Fekete's lemma with a gap
(`Real.fekete_sandwich`): (L) and connectivity give `P_m P_n ≤ 2^{d+1} P_{m+n+d+1}`, and (U)
iterated letter by letter gives `P_{q'+q} ≤ (1 + q P_q) P_{q'}`.
-/

open Filter Topology Real

/-! ### Paths and subwords over a monoid -/

section Path

variable {M Obj α : Type*} [Monoid M] [MulAction M Obj]

/-- The weight `p(U, S_{a₀}) p(S_{a₀}, S_{a₁}) ⋯ p(S_{a_l}, V)` of a path through centres. -/
def pathWeight (p : Obj → Obj → ℝ) (S : α → Obj) : Obj → List α → Obj → ℝ
  | U, [], V => p U V
  | U, a :: as, V => p U (S a) * pathWeight p S (S a) as V

/-- The `2^l` subwords of a word of length `l`, with repetitions. -/
def subwords : List α → List (List α)
  | [] => [[]]
  | a :: as => subwords as ++ (subwords as).map (a :: ·)

lemma length_subwords (l : List α) : (subwords l).length = 2 ^ l.length := by
  induction l with
  | nil => simp [subwords]
  | cons a l ih => simp [subwords, ih, pow_succ]; ring

lemma length_le_of_mem_subwords {l w : List α} (hw : w ∈ subwords l) : w.length ≤ l.length := by
  induction l generalizing w with
  | nil => simp [subwords] at hw; simp [hw]
  | cons a l ih =>
    simp only [subwords, List.mem_append, List.mem_map] at hw
    rcases hw with hw | ⟨v, hv, rfl⟩
    · exact (ih hw).trans (Nat.le_succ _)
    · simpa using ih hv

/-- **The path lemma.** If `p ≥ 0` satisfies the lower one-letter bound
`p(U, S_a) p(S_a, Y) ≤ p(U, Y) + p(U, T_a Y)`, the weight of a path through the centres of a word
is at most the sum of `p(U, W' V)` over its `2^l` subwords `W'`. -/
theorem pathWeight_le (p : Obj → Obj → ℝ) (S : α → Obj) (T : α → M)
    (hp : ∀ U V, 0 ≤ p U V)
    (hL : ∀ a U Y, p U (S a) * p (S a) Y ≤ p U Y + p U (T a • Y)) :
    ∀ (l : List α) (U V : Obj),
      pathWeight p S U l V ≤ ((subwords l).map fun w => p U ((w.map T).prod • V)).sum
  | [], U, V => by simp [pathWeight, subwords]
  | a :: as, U, V => by
    have ih := pathWeight_le p S T hp hL as (S a) V
    calc pathWeight p S U (a :: as) V = p U (S a) * pathWeight p S (S a) as V := rfl
      _ ≤ p U (S a) * ((subwords as).map fun w => p (S a) ((w.map T).prod • V)).sum :=
          mul_le_mul_of_nonneg_left ih (hp _ _)
      _ = ((subwords as).map fun w => p U (S a) * p (S a) ((w.map T).prod • V)).sum := by
          rw [List.sum_map_mul_left]
      _ ≤ ((subwords as).map fun w =>
            p U ((w.map T).prod • V) + p U (T a • (w.map T).prod • V)).sum :=
          List.sum_le_sum fun w _ => hL a U _
      _ = ((subwords (a :: as)).map fun w => p U ((w.map T).prod • V)).sum := by
          simp [subwords, List.sum_map_add, Function.comp_def, mul_smul]

/-- A path whose consecutive centres have weight at least one weighs at least its two ends. -/
theorem le_pathWeight (p : Obj → Obj → ℝ) (S : α → Obj) (hp : ∀ U V, 0 ≤ p U V) :
    ∀ (a : α) (as : List α) (U V : Obj),
      List.IsChain (fun a b => 1 ≤ p (S a) (S b)) (a :: as) →
      p U (S a) * p (S ((a :: as).getLast (List.cons_ne_nil _ _))) V ≤
        pathWeight p S U (a :: as) V
  | a, [], U, V, _ => by simp [pathWeight]
  | a, b :: bs, U, V, hc => by
    rw [List.isChain_cons_cons] at hc
    have ih := le_pathWeight p S hp b bs (S a) V hc.2
    have hlast : (a :: b :: bs).getLast (List.cons_ne_nil _ _) =
        (b :: bs).getLast (List.cons_ne_nil _ _) := List.getLast_cons _
    rw [hlast]
    simp only [pathWeight]
    refine mul_le_mul_of_nonneg_left ?_ (hp _ _)
    refine le_trans ?_ ih
    simp only [pathWeight] at *
    have := hp (S ((b :: bs).getLast (List.cons_ne_nil _ _))) V
    nlinarith [hc.1, hp (S a) (S b)]

end Path

/-! ### The domination recursion -/

/-- A **domination system**: a monoid `M` acting on objects, centres `S_i`, letters `T_a` with
centres `c(a)`, a coupling `G_a(k) ∈ ℕ`, and a family of real-valued tests closed under pulling
back along letters, with the one-letter upper bound with constant one when the second argument
is a centre: `test(T_a S_k) ≤ test(S_k) + G_a(k) test(S_{c(a)})`. -/
structure DominationSystem (M Obj ι α Φ : Type*) [Monoid M] [MulAction M Obj] where
  /-- The centres. -/
  S : ι → Obj
  /-- The letters. -/
  T : α → M
  /-- The centre of a letter. -/
  c : α → ι
  /-- The coupling: how many copies of the letter's centre a centre picks up. -/
  G : α → ι → ℕ
  /-- The tests. -/
  test : Φ → Obj → ℝ
  /-- Pulling a test back along a letter. -/
  pull : α → Φ → Φ
  test_pull : ∀ a φ Y, test (pull a φ) Y = test φ (T a • Y)
  /-- The upper bound with constant one, on centres. -/
  centre_le : ∀ a φ k, test φ (T a • S k) ≤ test φ (S k) + G a k * test φ (S (c a))

namespace DominationSystem

variable {M Obj ι α Φ : Type*} [Monoid M] [MulAction M Obj] [Fintype ι] [DecidableEq ι]
variable (D : DominationSystem M Obj ι α Φ)

/-- One letter acting on count vectors: the nonnegative transvection `1 + e_{c(a)} G_a`. -/
def step (a : α) (n : ι → ℕ) : ι → ℕ :=
  fun k => n k + if k = D.c a then ∑ j, D.G a j * n j else 0

/-- `Y` is dominated by the count vector `n`: every test of `Y` is at most `∑ n_k test(S_k)`. -/
def Dominated (Y : Obj) (n : ι → ℕ) : Prop :=
  ∀ φ, D.test φ Y ≤ ∑ k, (n k : ℝ) * D.test φ (D.S k)

/-- The monoid element of a word; the head letter acts last. -/
def word (w : List α) : M := (w.map D.T).prod

/-- A word acting on count vectors. -/
def dom (w : List α) (n : ι → ℕ) : ι → ℕ := w.foldr D.step n

theorem dominated_step {Y : Obj} {n : ι → ℕ} (a : α) (hY : D.Dominated Y n) :
    D.Dominated (D.T a • Y) (D.step a n) := by
  intro φ
  rw [← D.test_pull]
  refine (hY (D.pull a φ)).trans ?_
  simp_rw [D.test_pull]
  calc ∑ k, (n k : ℝ) * D.test φ (D.T a • D.S k)
      ≤ ∑ k, (n k : ℝ) * (D.test φ (D.S k) + D.G a k * D.test φ (D.S (D.c a))) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (D.centre_le a φ k) (Nat.cast_nonneg _)
    _ = ∑ k, (D.step a n k : ℝ) * D.test φ (D.S k) := by
        simp only [step, Nat.cast_add, Nat.cast_ite, Nat.cast_sum, Nat.cast_mul, Nat.cast_zero,
          add_mul, mul_add, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        congr 1
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring

theorem dominated_word {Y : Obj} {n : ι → ℕ} (hY : D.Dominated Y n) (w : List α) :
    D.Dominated (D.word w • Y) (D.dom w n) := by
  induction w with
  | nil => simpa [word, dom] using hY
  | cons a w ih =>
    have := D.dominated_step a ih
    simpa [word, dom, mul_smul] using this

theorem dominated_centre (j : ι) : D.Dominated (D.S j) (Pi.single j 1) := by
  intro φ
  simp [Pi.single_apply]

/-- **The domination recursion with constant one.** Every test of `W S_j` is bounded by the
tests of the centres weighted by the column `P_W e_j` of the product of transvections. -/
theorem test_word_le (w : List α) (j : ι) (φ : Φ) :
    D.test φ (D.word w • D.S j) ≤ ∑ k, (D.dom w (Pi.single j 1) k : ℝ) * D.test φ (D.S k) :=
  D.dominated_word (D.dominated_centre j) w φ

/-- The transvection matrix `1 + e_{c(a)} G_a` of a letter. -/
def transvection (a : α) : Matrix ι ι ℕ :=
  1 + Matrix.of fun k j => if k = D.c a then D.G a j else 0

theorem step_eq_mulVec (a : α) (n : ι → ℕ) : D.step a n = (D.transvection a).mulVec n := by
  ext k
  simp only [step, transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  congr 1
  by_cases hk : k = D.c a
  · simp [hk, Matrix.mulVec, dotProduct]
  · simp [hk, Matrix.mulVec, dotProduct]

end DominationSystem

/-! ### Twist systems -/

/-- A **twist system** without the identity `T_S S = S[-1]`: a group `G` acting on objects,
centres `S_i`, letters `T_a ∈ G` with centres `S_{c(a)}`, and a count `h` that is invariant
under the group and satisfies the one-letter upper bound with constant one. -/
structure HomTwistSystem₀ (G Obj ι α : Type*) [Group G] [MulAction G Obj] where
  /-- The centres. -/
  S : ι → Obj
  /-- The letters. -/
  T : α → G
  /-- The centre of a letter. -/
  c : α → ι
  /-- The count, for instance the total dimension of `Ext^*(U, V)`. -/
  h : Obj → Obj → ℕ
  /-- (A1) Invariance: autoequivalences preserve `Ext`. -/
  h_smul : ∀ (g : G) U V, h (g • U) (g • V) = h U V
  /-- (U) The one-letter upper bound, from the long exact sequence of the twist triangle
  `Ext^*(S, V) ⊗ S → V → T_S V` (Seidel–Thomas, arXiv:math/0001043). -/
  upper : ∀ a U V, h U (T a • V) ≤ h U V + h U (S (c a)) * h (S (c a)) V

/-- A **twist system**: `HomTwistSystem₀` with the identity `T_S S = S[-1]` read through `h`
(for an `n`-spherical object `T_S S ≅ S[1 - n]`, Seidel–Thomas, arXiv:math/0001043; the shift is
invisible to the total count). -/
structure HomTwistSystem (G Obj ι α : Type*) [Group G] [MulAction G Obj]
    extends HomTwistSystem₀ G Obj ι α where
  /-- (A2) `T_S S = S[-1]`, read through `h`. -/
  h_twist_centre : ∀ a U, h U (T a • S (c a)) = h U (S (c a))

namespace HomTwistSystem₀

variable {G Obj ι α : Type*} [Group G] [MulAction G Obj] (H : HomTwistSystem₀ G Obj ι α)

/-- The group element of a word; the head letter acts last. -/
def word (w : List α) : G := (w.map H.T).prod

@[simp] lemma word_nil : H.word [] = 1 := rfl

lemma word_cons (a : α) (w : List α) : H.word (a :: w) = H.T a * H.word w := rfl

lemma word_append (w w' : List α) : H.word (w ++ w') = H.word w * H.word w' := by
  simp [word]

lemma h_smul_inv (g : G) (U V : Obj) : H.h U (g⁻¹ • V) = H.h (g • U) V := by
  have := H.h_smul g U (g⁻¹ • V)
  rw [smul_inv_smul] at this
  exact this.symm

lemma h_inv_smul (g : G) (U V : Obj) : H.h (g⁻¹ • U) V = H.h U (g • V) := by
  have := H.h_smul g (g⁻¹ • U) V
  rw [smul_inv_smul] at this
  exact this.symm

/-- The **lower one-letter bound** (L): `h(U, S) h(S, V) ≤ h(U, V) + h(U, T_a V)` with
`S = S_{c(a)}`, from the long exact sequence of the twist triangle. -/
def LowerBound : Prop :=
  ∀ a U Y, H.h U (H.S (H.c a)) * H.h (H.S (H.c a)) Y ≤ H.h U Y + H.h U (H.T a • Y)

/-- **Sphericity** of the centres, read through the count: `h(S_i, S_i) = 2`, the total
dimension of `Ext^*(S, S) = k ⊕ k[-2]` for a spherical object of a 2-Calabi–Yau category. -/
def IsSpherical : Prop := ∀ i, H.h (H.S i) (H.S i) = 2

/-- **Directed connectivity**: for every ordered pair of centres `(i, j)` there is a chain of at
most `d + 1` letters, the first with centre `j` and the last with centre `i`, whose consecutive
centres have count at least one. Without symmetry of `h` this is stronger than an undirected
diameter bound. -/
def DirectedConnected (d : ℕ) : Prop :=
  ∀ i j : ι, ∃ a : α, ∃ as : List α, H.c a = j ∧
    H.c ((a :: as).getLast (List.cons_ne_nil _ _)) = i ∧ as.length ≤ d ∧
    List.IsChain (fun a b => 1 ≤ H.h (H.S (H.c a)) (H.S (H.c b))) (a :: as)

/-- The bound (U) for the inverse of a letter, from symmetry of `h`. -/
theorem upper_inv (hsym : ∀ U V, H.h U V = H.h V U) (a : α) (U V : Obj) :
    H.h U ((H.T a)⁻¹ • V) ≤ H.h U V + H.h U (H.S (H.c a)) * H.h (H.S (H.c a)) V := by
  calc H.h U ((H.T a)⁻¹ • V) = H.h V (H.T a • U) := by rw [H.h_smul_inv, hsym]
    _ ≤ H.h V U + H.h V (H.S (H.c a)) * H.h (H.S (H.c a)) U := H.upper a V U
    _ = H.h U V + H.h U (H.S (H.c a)) * H.h (H.S (H.c a)) V := by
        rw [hsym V U, hsym V (H.S (H.c a)), hsym (H.S (H.c a)) U, mul_comm]

/-- The bound (L) for the inverse of a letter, from symmetry of `h`. -/
theorem lower_inv (hsym : ∀ U V, H.h U V = H.h V U) (hL : H.LowerBound) (a : α) (U Y : Obj) :
    H.h U (H.S (H.c a)) * H.h (H.S (H.c a)) Y ≤ H.h U Y + H.h U ((H.T a)⁻¹ • Y) := by
  have := hL a Y U
  rw [H.h_smul_inv, hsym (H.T a • U) Y]
  rw [hsym Y (H.S (H.c a)), hsym (H.S (H.c a)) U, hsym Y U] at this
  linarith

/-- The **inverse-closed alphabet** `α × Bool` (`true` for `T_a`, `false` for `T_a⁻¹`); only the
bound (U) for inverses needs symmetry. -/
def withInverses (hsym : ∀ U V, H.h U V = H.h V U) : HomTwistSystem₀ G Obj ι (α × Bool) where
  S := H.S
  T p := if p.2 then H.T p.1 else (H.T p.1)⁻¹
  c p := H.c p.1
  h := H.h
  h_smul := H.h_smul
  upper p U V := by
    rcases p with ⟨a, _ | _⟩
    · simpa using H.upper_inv hsym a U V
    · simpa using H.upper a U V

lemma lowerBound_withInverses (hsym : ∀ U V, H.h U V = H.h V U) (hL : H.LowerBound) :
    (H.withInverses hsym).LowerBound := by
  rintro ⟨a, _ | _⟩ U Y
  · simpa [withInverses] using H.lower_inv hsym hL a U Y
  · simpa [withInverses] using hL a U Y

/-- The **leaf count** of a word: `∑_t h(X, S_{a_t}) h(S_{a_t}, W_{>t} Y)`. -/
def leafSum (X Y : Obj) : List α → ℕ
  | [] => 0
  | a :: w => leafSum X Y w + H.h X (H.S (H.c a)) * H.h (H.S (H.c a)) (H.word w • Y)

/-- **The bound (U) iterated letter by letter**: `h(X, W Y) ≤ h(X, Y) + leafSum`. -/
theorem h_word_le (X Y : Obj) (w : List α) :
    H.h X (H.word w • Y) ≤ H.h X Y + H.leafSum X Y w := by
  induction w with
  | nil => simp [word, leafSum]
  | cons a w ih =>
    have h1 := H.upper a X (H.word w • Y)
    have e : H.word (a :: w) • Y = H.T a • H.word w • Y := by simp [word, mul_smul]
    rw [e, leafSum]
    omega

/-- Without `T_S S = S[-1]`, counts are still a domination system, with tests `h(X, -)` pulled
back by `T_a⁻¹` and coupling `h(S_{c(a)}, S_k)` (the diagonal `h(S, S)` included). -/
def toDomination0 : DominationSystem G Obj ι α Obj where
  S := H.S
  T := H.T
  c := H.c
  G a k := H.h (H.S (H.c a)) (H.S k)
  test X Y := H.h X Y
  pull a X := (H.T a)⁻¹ • X
  test_pull a X Y := by
    show ((H.h ((H.T a)⁻¹ • X) Y : ℕ) : ℝ) = H.h X (H.T a • Y)
    rw [H.h_inv_smul]
  centre_le a X k := by
    show ((H.h X (H.T a • H.S k) : ℕ) : ℝ) ≤ (H.h X (H.S k) : ℝ) +
      ((H.h (H.S (H.c a)) (H.S k) : ℕ) : ℝ) * (H.h X (H.S (H.c a)) : ℝ)
    rw [mul_comm]
    exact_mod_cast H.upper a X (H.S k)

/-! #### The maximal centre count `P_q` -/

section MaxCount

variable [Fintype ι] [Fintype α]

/-- The group element of a word `Fin n → α`. -/
def wordOf {n : ℕ} (w : Fin n → α) : G := H.word (List.ofFn w)

/-- `P_q = max h(S_i, W S_j)` over centres `i, j` and words `W` of length at most `q`. -/
noncomputable def maxCount (q : ℕ) : ℕ :=
  Finset.univ.sup fun x : ι × ι × (Σ n : Fin (q + 1), Fin n → α) =>
    H.h (H.S x.1) (H.wordOf x.2.2.2 • H.S x.2.1)

theorem le_maxCount {q : ℕ} (i j : ι) (w : List α) (hw : w.length ≤ q) :
    H.h (H.S i) (H.word w • H.S j) ≤ H.maxCount q := by
  have h := Finset.le_sup (f := fun x : ι × ι × (Σ n : Fin (q + 1), Fin n → α) =>
    H.h (H.S x.1) (H.wordOf x.2.2.2 • H.S x.2.1))
    (Finset.mem_univ (i, j, ⟨⟨w.length, by omega⟩, w.get⟩))
  have e : H.wordOf w.get = H.word w := by simp [wordOf, List.ofFn_get]
  simp only at h
  rw [e] at h
  exact h

theorem exists_maxCount_eq [Nonempty ι] (q : ℕ) :
    ∃ i j, ∃ w : List α, w.length ≤ q ∧ H.maxCount q = H.h (H.S i) (H.word w • H.S j) := by
  obtain ⟨⟨i, j, ⟨n, w⟩⟩, -, hx⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (ι × ι × (Σ n : Fin (q + 1), Fin n → α)))
    ⟨(Classical.arbitrary ι, Classical.arbitrary ι, ⟨0, Fin.elim0⟩), Finset.mem_univ _⟩
    (fun x => H.h (H.S x.1) (H.wordOf x.2.2.2 • H.S x.2.1))
  exact ⟨i, j, List.ofFn w, by simpa using Nat.lt_succ_iff.1 n.2, hx⟩

/-- Sphericity makes `P_q ≥ 2`. -/
theorem two_le_maxCount [Nonempty ι] (hsph : H.IsSpherical) (q : ℕ) : 2 ≤ H.maxCount q := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := H.le_maxCount (q := q) i i [] (Nat.zero_le _)
  simpa [hsph i] using this

/-- **The gap inequality** `P_m P_n ≤ 2^{d+1} P_{m+n+d+1}`, from (L) and connectivity. -/
theorem maxCount_mul_le [Nonempty ι] (hL : H.LowerBound) {d : ℕ} (hconn : H.DirectedConnected d)
    (m n : ℕ) :
    (H.maxCount m : ℝ) * H.maxCount n ≤ 2 ^ (d + 1) * H.maxCount (m + n + (d + 1)) := by
  obtain ⟨i', j', w', hw', hm⟩ := H.exists_maxCount_eq m
  obtain ⟨i, j, w, hw, hn⟩ := H.exists_maxCount_eq n
  obtain ⟨a, as, ha, hlast, hlen, hchain⟩ := hconn i j'
  set p : Obj → Obj → ℝ := fun U V => (H.h U V : ℝ)
  set U := (H.word w')⁻¹ • H.S i'
  set V := H.word w • H.S j
  have hp : ∀ U V, 0 ≤ p U V := fun _ _ => Nat.cast_nonneg _
  have hL' : ∀ a U Y, p U (H.S (H.c a)) * p (H.S (H.c a)) Y ≤ p U Y + p U (H.T a • Y) :=
    fun a U Y => by simp only [p]; exact_mod_cast hL a U Y
  have e1 : (H.maxCount m : ℝ) = p U (H.S (H.c a)) := by
    rw [hm, ha]; simp only [p, U]; rw [H.h_inv_smul]
  have e2 : (H.maxCount n : ℝ) = p (H.S (H.c ((a :: as).getLast (List.cons_ne_nil _ _)))) V := by
    rw [hn, hlast]
  have hchain' : List.IsChain (fun a b => (1 : ℝ) ≤ p (H.S (H.c a)) (H.S (H.c b))) (a :: as) :=
    hchain.imp fun a b hab => by simp only [p]; exact_mod_cast hab
  have step1 := le_pathWeight p (fun a => H.S (H.c a)) hp a as U V hchain'
  have step2 := pathWeight_le p (fun a => H.S (H.c a)) H.T hp hL' (a :: as) U V
  have step3 : ((subwords (a :: as)).map fun e => p U ((e.map H.T).prod • V)).sum ≤
      ((subwords (a :: as)).map fun _ => (H.maxCount (m + n + (d + 1)) : ℝ)).sum := by
    refine List.sum_le_sum fun e he => ?_
    have hle := length_le_of_mem_subwords he
    simp only [List.length_cons] at hle
    have := H.le_maxCount (q := m + n + (d + 1)) i' j (w' ++ e ++ w) (by simp; omega)
    simp only [p, U, V]
    rw [H.h_inv_smul]
    have e' : H.word (w' ++ e ++ w) = H.word w' * ((e.map H.T).prod * H.word w) := by
      simp [word, List.map_append, List.prod_append]
    rw [e', mul_smul, mul_smul] at this
    exact_mod_cast this
  have hcount : ((subwords (a :: as)).map fun _ => (H.maxCount (m + n + (d + 1)) : ℝ)).sum =
      2 ^ (as.length + 1) * H.maxCount (m + n + (d + 1)) := by
    simp [List.sum_replicate, length_subwords]
  have h2 : (2 : ℝ) ^ (as.length + 1) ≤ 2 ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [e1, e2]
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := step3
    _ = _ := hcount
    _ ≤ 2 ^ (d + 1) * H.maxCount (m + n + (d + 1)) := by gcongr

/-- **The block bound** `P_{q'+q} ≤ (1 + q P_q) P_{q'}`, from (U) iterated letter by letter. -/
theorem maxCount_add_le [Nonempty ι] (q q' : ℕ) :
    (H.maxCount (q' + q) : ℝ) ≤ (1 + q * H.maxCount q) * H.maxCount q' := by
  obtain ⟨i, j, w, hw, hP⟩ := H.exists_maxCount_eq (q' + q)
  set wo := w.take q'
  set wi := w.drop q'
  have hwi : wi.length ≤ q := by simp [wi]; omega
  have hwo : wo.length ≤ q' := by simp [wo]
  have hsplit : H.word w = H.word wo * H.word wi := by
    rw [← word_append, List.take_append_drop]
  set X := (H.word wo)⁻¹ • H.S i
  have hX : ∀ Y, H.h (H.S i) (H.word wo • Y) = H.h X Y := fun Y => by
    simp only [X]; rw [H.h_inv_smul]
  have hleaf : ∀ v : List α, v.length ≤ q →
      (H.leafSum X (H.S j) v : ℝ) ≤ v.length * H.maxCount q * H.maxCount q' := by
    intro v
    induction v with
    | nil => simp [leafSum]
    | cons a v ih =>
      intro hv
      simp only [List.length_cons] at hv
      have ih' := ih (by omega)
      have e1 : (H.h X (H.S (H.c a)) : ℝ) ≤ H.maxCount q' := by
        rw [← hX]; exact_mod_cast H.le_maxCount i (H.c a) wo hwo
      have e2 : (H.h (H.S (H.c a)) (H.word v • H.S j) : ℝ) ≤ H.maxCount q := by
        exact_mod_cast H.le_maxCount (H.c a) j v (by omega)
      have hPq' : (0 : ℝ) ≤ H.maxCount q' := Nat.cast_nonneg _
      simp only [leafSum, Nat.cast_add, Nat.cast_mul, List.length_cons, Nat.cast_succ]
      have := mul_le_mul e1 e2 (Nat.cast_nonneg _) hPq'
      nlinarith
  have hbase : (H.h X (H.S j) : ℝ) ≤ H.maxCount q' := by
    rw [← hX]; exact_mod_cast H.le_maxCount (q := q') i j wo hwo |>.trans' (by simp)
  have hmain := H.h_word_le X (H.S j) wi
  have hPq' : (0 : ℝ) ≤ H.maxCount q' := Nat.cast_nonneg _
  have hPq : (0 : ℝ) ≤ H.maxCount q := Nat.cast_nonneg _
  rw [hP, hsplit, mul_smul, hX]
  have h1 : (H.h X (H.word wi • H.S j) : ℝ) ≤ H.h X (H.S j) + H.leafSum X (H.S j) wi := by
    exact_mod_cast hmain
  have h2 := hleaf wi hwi
  have h3 : (wi.length : ℝ) * H.maxCount q * H.maxCount q' ≤
      q * H.maxCount q * H.maxCount q' := by
    have : (wi.length : ℝ) ≤ q := by exact_mod_cast hwi
    have := mul_nonneg hPq hPq'
    nlinarith
  nlinarith

omit [Fintype α] in
/-- `g = max h(S_i, S_k)`, the largest count between centres. -/
noncomputable def centreMax : ℕ :=
  Finset.univ.sup fun x : ι × ι => H.h (H.S x.1) (H.S x.2)

omit [Fintype α] in
lemma le_centreMax (i k : ι) : H.h (H.S i) (H.S k) ≤ H.centreMax :=
  Finset.le_sup (f := fun x : ι × ι => H.h (H.S x.1) (H.S x.2)) (Finset.mem_univ (i, k))

/-- The **exponent of the centre counts**, `η = lim log P_N / N` (the limit exists by
`tendsto_homExponent` under the hypotheses there; otherwise this is junk). -/
noncomputable def homExponent : ℝ :=
  limUnder atTop fun N : ℕ => log (H.maxCount N) / N

variable [Nonempty ι]

/-- **The exponent of the centre counts, with certificates.** Under (L), sphericity and directed
connectivity within `d + 1` letters, `log P_N / N` converges to some `η` and
`log(P_q / 2^{d+1})/(q + d + 1) ≤ η` for every `q`, `η ≤ log(1 + q P_q)/q` for `q > 0`. -/
theorem exists_tendsto_log_maxCount (hL : H.LowerBound) (hsph : H.IsSpherical) {d : ℕ}
    (hconn : H.DirectedConnected d) :
    ∃ η : ℝ, Tendsto (fun N : ℕ => log (H.maxCount N) / N) atTop (𝓝 η) ∧
      (∀ q : ℕ, log (H.maxCount q / 2 ^ (d + 1)) / ((q : ℝ) + (d + 1 : ℕ)) ≤ η) ∧
      (∀ q : ℕ, 0 < q → η ≤ log (1 + q * H.maxCount q) / q) := by
  have hc : (0 : ℝ) < 1 / 2 ^ (d + 1) := by positivity
  have hpos : ∀ q, (0 : ℝ) < H.maxCount q := fun q => by
    have := H.two_le_maxCount hsph q
    exact_mod_cast (by omega : 0 < H.maxCount q)
  obtain ⟨η, h1, h2, h3⟩ := fekete_sandwich (P := fun q => (H.maxCount q : ℝ))
    (c := 1 / 2 ^ (d + 1)) (D := d + 1) hc hpos
    (fun m n => by
      have := H.maxCount_mul_le hL hconn m n
      have h2pos : (0 : ℝ) < 2 ^ (d + 1) := by positivity
      have key : (H.maxCount m : ℝ) * H.maxCount n / 2 ^ (d + 1) ≤
          H.maxCount (m + n + (d + 1)) := by
        rw [div_le_iff₀ h2pos]; linarith
      calc 1 / 2 ^ (d + 1) * (H.maxCount m : ℝ) * (1 / 2 ^ (d + 1) * H.maxCount n)
          = 1 / 2 ^ (d + 1) * (H.maxCount m * H.maxCount n / 2 ^ (d + 1)) := by ring
        _ ≤ 1 / 2 ^ (d + 1) * H.maxCount (m + n + (d + 1)) := by gcongr)
    (fun q => 1 + q * H.maxCount q) (fun q n => H.maxCount_add_le q n)
  refine ⟨η, h1, fun q => ?_, h3⟩
  have := h2 q (by omega)
  rwa [one_div_mul_eq_div] at this

theorem tendsto_homExponent (hL : H.LowerBound) (hsph : H.IsSpherical) {d : ℕ}
    (hconn : H.DirectedConnected d) :
    Tendsto (fun N : ℕ => log (H.maxCount N) / N) atTop (𝓝 H.homExponent) := by
  obtain ⟨η, h1, -⟩ := H.exists_tendsto_log_maxCount hL hsph hconn
  rwa [homExponent, h1.limUnder_eq]

/-- The lower certificate `log(P_q / 2^{d+1})/(q + d + 1) ≤ η`. -/
theorem homExponent_lower (hL : H.LowerBound) (hsph : H.IsSpherical) {d : ℕ}
    (hconn : H.DirectedConnected d) (q : ℕ) :
    log (H.maxCount q / 2 ^ (d + 1)) / ((q : ℝ) + (d + 1 : ℕ)) ≤ H.homExponent := by
  obtain ⟨η, h1, h2, -⟩ := H.exists_tendsto_log_maxCount hL hsph hconn
  rw [homExponent, h1.limUnder_eq]
  exact h2 q

/-- The upper certificate `η ≤ log(1 + q P_q)/q` for `q > 0`. -/
theorem homExponent_upper (hL : H.LowerBound) (hsph : H.IsSpherical) {d : ℕ}
    (hconn : H.DirectedConnected d) {q : ℕ} (hq : 0 < q) :
    H.homExponent ≤ log (1 + q * H.maxCount q) / q := by
  obtain ⟨η, h1, -, h3⟩ := H.exists_tendsto_log_maxCount hL hsph hconn
  rw [homExponent, h1.limUnder_eq]
  exact h3 q hq

/-- `η ≥ 0`: sphericity keeps `P_N ≥ 2`. -/
theorem homExponent_nonneg (hL : H.LowerBound) (hsph : H.IsSpherical) {d : ℕ}
    (hconn : H.DirectedConnected d) : 0 ≤ H.homExponent := by
  refine ge_of_tendsto (H.tendsto_homExponent hL hsph hconn) (Eventually.of_forall fun N => ?_)
  have h2 : (2 : ℝ) ≤ H.maxCount N := by exact_mod_cast H.two_le_maxCount hsph N
  exact div_nonneg (log_nonneg (by linarith)) (Nat.cast_nonneg _)

/-! #### The width of the certificates -/

lemma maxCount_zero : H.maxCount 0 = H.centreMax := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, j, w, hw, h⟩ := H.exists_maxCount_eq 0
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hw)] at h
    simpa [h] using H.le_centreMax i j
  · refine Finset.sup_le fun x _ => ?_
    simpa using H.le_maxCount (q := 0) x.1 x.2 [] le_rfl

/-- **One more letter costs at most `1 + g`**: `P_{q+1} ≤ (1 + g) P_q`. -/
theorem maxCount_succ_le (q : ℕ) : H.maxCount (q + 1) ≤ (1 + H.centreMax) * H.maxCount q := by
  obtain ⟨i, j, w, hw, hP⟩ := H.exists_maxCount_eq (q + 1)
  rw [hP]
  rcases w with _ | ⟨a, w⟩
  · have := H.le_maxCount (q := q) i j [] (Nat.zero_le _)
    simp only [word_nil, one_smul] at this ⊢
    nlinarith
  · simp only [List.length_cons] at hw
    rw [word_cons, mul_smul]
    have h1 := H.upper a (H.S i) (H.word w • H.S j)
    have h2 := H.le_maxCount (q := q) i j w (by omega)
    have h3 := H.le_maxCount (q := q) (H.c a) j w (by omega)
    have h4 := H.le_centreMax i (H.c a)
    calc H.h (H.S i) (H.T a • H.word w • H.S j)
        ≤ H.h (H.S i) (H.word w • H.S j) +
            H.h (H.S i) (H.S (H.c a)) * H.h (H.S (H.c a)) (H.word w • H.S j) := h1
      _ ≤ H.maxCount q + H.centreMax * H.maxCount q := by gcongr
      _ = (1 + H.centreMax) * H.maxCount q := by ring

theorem maxCount_le_pow (q : ℕ) : H.maxCount q ≤ H.centreMax * (1 + H.centreMax) ^ q := by
  induction q with
  | zero => simp [maxCount_zero]
  | succ q ih =>
    calc H.maxCount (q + 1) ≤ (1 + H.centreMax) * H.maxCount q := H.maxCount_succ_le q
      _ ≤ (1 + H.centreMax) * (H.centreMax * (1 + H.centreMax) ^ q) := by gcongr
      _ = H.centreMax * (1 + H.centreMax) ^ (q + 1) := by ring

/-- **The width of the certificates.** With `g = max h(S_i, S_k)` and `D = d + 1`, for `q > 0`
the upper and lower certificates differ by at most
`log(q + 1)/q + D/(q + D) (log(1 + g) + log g / q + log 2)`, a bound that does not depend on the
words. -/
theorem homExponent_width (hsph : H.IsSpherical) (d : ℕ) {q : ℕ} (hq : 0 < q) :
    log (1 + q * H.maxCount q) / q - log (H.maxCount q / 2 ^ (d + 1)) / ((q : ℝ) + (d + 1 : ℕ)) ≤
      log (q + 1) / q + ((d + 1 : ℕ) : ℝ) / ((q : ℝ) + (d + 1 : ℕ)) *
        (log (1 + H.centreMax) + log H.centreMax / q + log 2) := by
  have hP2 : (2 : ℝ) ≤ H.maxCount q := by exact_mod_cast H.two_le_maxCount hsph q
  have hg2 : (2 : ℝ) ≤ H.centreMax := by
    have := H.two_le_maxCount hsph 0
    rw [maxCount_zero] at this
    exact_mod_cast this
  have hPg : (H.maxCount q : ℝ) ≤ H.centreMax * (1 + H.centreMax) ^ q := by
    exact_mod_cast H.maxCount_le_pow q
  set P : ℝ := (H.maxCount q : ℝ)
  set g : ℝ := (H.centreMax : ℝ)
  set D : ℝ := ((d + 1 : ℕ) : ℝ)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hD : (0 : ℝ) < D := by positivity
  -- `log(1 + qP) ≤ log(q + 1) + log P`
  have hup : log (1 + q * P) ≤ log (q + 1) + log P := by
    rw [← log_mul (by positivity) (by positivity)]
    exact log_le_log (by positivity) (by nlinarith)
  -- `log P ≤ log g + q log(1 + g)`
  have hlogP : log P ≤ log g + q * log (1 + g) := by
    calc log P ≤ log (g * (1 + g) ^ q) := log_le_log (by positivity) hPg
      _ = log g + q * log (1 + g) := by
          rw [log_mul (by positivity) (by positivity), log_pow]
  have hlow : log (P / 2 ^ (d + 1)) = log P - D * log 2 := by
    rw [log_div (by positivity) (by positivity), log_pow]
  rw [hlow]
  have hqD : (0 : ℝ) < q + D := by positivity
  have hlP : 0 ≤ log P := log_nonneg (by linarith)
  have key : log P / q - (log P - D * log 2) / (q + D) =
      D / (q + D) * (log P / q + log 2) := by
    field_simp
    ring
  calc log (1 + q * P) / q - (log P - D * log 2) / (q + D)
      ≤ (log (q + 1) + log P) / q - (log P - D * log 2) / (q + D) := by gcongr
    _ = log (q + 1) / q + (log P / q - (log P - D * log 2) / (q + D)) := by ring
    _ = log (q + 1) / q + D / (q + D) * (log P / q + log 2) := by rw [key]
    _ ≤ log (q + 1) / q + D / (q + D) * ((log g + q * log (1 + g)) / q + log 2) := by
        gcongr
    _ = log (q + 1) / q + D / (q + D) * (log (1 + g) + log g / q + log 2) := by
        congr 2
        field_simp
        ring

end MaxCount

/-! #### Maps of twist systems -/

section Map

variable {G' Obj' : Type*} [Group G'] [MulAction G' Obj'] (H' : HomTwistSystem₀ G' Obj' ι α)

/-- A map of objects that sends centres to centres, intertwines every letter and preserves the
count carries the counts of words between centres to the same counts. -/
theorem h_word_map (f : Obj → Obj') (hS : ∀ i, f (H.S i) = H'.S i)
    (hT : ∀ a V, f (H.T a • V) = H'.T a • f V) (hh : ∀ U V, H'.h (f U) (f V) = H.h U V)
    (i j : ι) (w : List α) :
    H'.h (H'.S i) (H'.word w • H'.S j) = H.h (H.S i) (H.word w • H.S j) := by
  have hw : ∀ w : List α, f (H.word w • H.S j) = H'.word w • H'.S j := by
    intro w
    induction w with
    | nil => simp [hS]
    | cons a w ih => rw [word_cons, word_cons, mul_smul, mul_smul, hT, ih]
  rw [← hw, ← hS, hh]

variable [Fintype ι] [Fintype α]

/-- **Invariance of `P_q`**: a map of twist systems that matches centres and letters and
preserves counts has `P'_q = P_q` for every `q`. -/
theorem maxCount_eq_of_map (f : Obj → Obj') (hS : ∀ i, f (H.S i) = H'.S i)
    (hT : ∀ a V, f (H.T a • V) = H'.T a • f V) (hh : ∀ U V, H'.h (f U) (f V) = H.h U V)
    (q : ℕ) : H'.maxCount q = H.maxCount q := by
  unfold maxCount
  congr 1
  funext x
  exact H.h_word_map H' f hS hT hh x.1 x.2.1 (List.ofFn x.2.2.2)

/-- **Invariance of the exponent** under maps of twist systems. -/
theorem homExponent_eq_of_map (f : Obj → Obj') (hS : ∀ i, f (H.S i) = H'.S i)
    (hT : ∀ a V, f (H.T a • V) = H'.T a • f V) (hh : ∀ U V, H'.h (f U) (f V) = H.h U V) :
    H'.homExponent = H.homExponent := by
  unfold homExponent
  simp_rw [H.maxCount_eq_of_map H' f hS hT hh]

end Map

end HomTwistSystem₀

namespace HomTwistSystem

variable {G Obj ι α : Type*} [Group G] [MulAction G Obj] (H : HomTwistSystem G Obj ι α)

/-- `T_S S = S[-1]` for the inverse letter, read through `h`: no symmetry needed. -/
theorem twist_centre_inv (a : α) (U : Obj) :
    H.h U ((H.T a)⁻¹ • H.S (H.c a)) = H.h U (H.S (H.c a)) := by
  rw [H.h_smul_inv, ← H.h_twist_centre a (H.T a • U), H.h_smul]

/-- The coupling with zero diagonal, where `T_S S = S[-1]` enters. -/
def coupling [DecidableEq ι] (a : α) (k : ι) : ℕ :=
  if k = H.c a then 0 else H.h (H.S (H.c a)) (H.S k)

/-- Counts are a domination system with tests `h(X, -)`, pulled back by `T_a⁻¹`, and the coupling
`h(S_{c(a)}, S_k)` off the diagonal. -/
def toDomination [DecidableEq ι] : DominationSystem G Obj ι α Obj where
  S := H.S
  T := H.T
  c := H.c
  G := H.coupling
  test X Y := H.h X Y
  pull a X := (H.T a)⁻¹ • X
  test_pull a X Y := by
    show ((H.h ((H.T a)⁻¹ • X) Y : ℕ) : ℝ) = H.h X (H.T a • Y)
    rw [H.h_inv_smul]
  centre_le a X k := by
    unfold coupling
    split_ifs with hk
    · subst hk
      simp [H.h_twist_centre]
    · have h1 : ((H.h X (H.T a • H.S k) : ℕ) : ℝ) ≤
          H.h X (H.S k) + H.h X (H.S (H.c a)) * H.h (H.S (H.c a)) (H.S k) := by
        exact_mod_cast H.upper a X (H.S k)
      linarith

/-- The inverse-closed alphabet of a twist system: `T_S S = S[-1]` for inverses needs no
symmetry, the bound (U) for inverses does. -/
def withInverses (hsym : ∀ U V, H.h U V = H.h V U) : HomTwistSystem G Obj ι (α × Bool) where
  toHomTwistSystem₀ := H.toHomTwistSystem₀.withInverses hsym
  h_twist_centre p U := by
    rcases p with ⟨a, _ | _⟩
    · simpa [HomTwistSystem₀.withInverses] using H.twist_centre_inv a U
    · simpa [HomTwistSystem₀.withInverses] using H.h_twist_centre a U

end HomTwistSystem
