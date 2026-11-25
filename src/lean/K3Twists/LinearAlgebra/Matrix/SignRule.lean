/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

/-!
# Count letters, signed letters and the sign rule

Fix a finite set of centres `ι`, a nonnegative coupling matrix `G` and a signed form `K`. A
letter at the centre `i` with exponent `e ∈ ℤ` acts on count vectors by the nonnegative
transvection and on signed vectors by the signed one,

  `P_i(e) = 1 + |e| e_i G_{i*}`  (`Matrix.countLetter`),
  `E_i(e) = 1 - e e_i K_{i*}`    (`Matrix.signedLetter`).

The **sign rule** asks when a diagonal of signs `D` conjugates every signed letter into the count
letter, `D E_i(e) D = P_i(e)`: exactly when `-e d_i d_b K_{ib} = |e| G_{ib}` for every `b`
(`Matrix.signRule_letter`), and then for every word (`Matrix.signRule_word`).

The form must be the **parity-graded** one: `K` skew with zero diagonal, `K_{ab} = -ε_a G_{ab}`
for a 2-colouring `ε` of the support of `G` (an auxiliary `ℤ/2`-grading on the `Ext`-algebra of
the centres). Then adjacent centres used by the word carry letters of opposite signs
(`Matrix.signRule_opposite`), and the canonical orientation makes every letter of the right sign
a count letter with `D = 1` (`Matrix.signRule_canonical`). With the symmetric Euler form of a
2-Calabi–Yau category (`K_ii = 2`, `G_ii = 0`) no sign diagonal works for any nonzero exponent,
and a symmetric form forces adjacent letters to have the same sign; both are checked in
`K3TwistsTest/SignRuleModel.lean`. With `K_ii = 0` the signed letter is the action of `T^e` on
parity-graded classes; with `K_ii = 2` it is the Mukai reflection only at `e = 1`.

Without any sign rule, `|K| ≤ G` entrywise gives `|E_W| ≤ P_W` entrywise for every word
(`Matrix.abs_signedWord_le`).

## Main results

* `Matrix.signRule_letter`, `Matrix.signRule_word`: the sign rule for letters and words;
* `Matrix.signRule_opposite`, `Matrix.signRule_canonical`: the parity-graded form;
* `Matrix.abs_list_prod_le`, `Matrix.abs_signedWord_le`: word-level domination from `|K| ≤ G`.
-/

namespace Matrix

variable {ι : Type*}

/-- A vector of signs `±1`. -/
def IsSign (d : ι → ℝ) : Prop := ∀ a, d a = 1 ∨ d a = -1

lemma IsSign.mul_self {d : ι → ℝ} (hd : IsSign d) (a : ι) : d a * d a = 1 := by
  rcases hd a with h | h <;> rw [h] <;> norm_num

lemma IsSign.abs_eq {d : ι → ℝ} (hd : IsSign d) (a : ι) : |d a| = 1 := by
  rcases hd a with h | h <;> rw [h] <;> norm_num

lemma IsSign.mul_injective {d : ι → ℝ} (hd : IsSign d) :
    Function.Injective (fun x : ι → ℝ => d * x) := by
  intro x y h
  funext a
  have := congrFun h a
  simp only [Pi.mul_apply] at this
  rcases hd a with h' | h' <;> rw [h'] at this <;> linarith

variable [Fintype ι] [DecidableEq ι]

/-- The matrix `e_i r`: row `i` equal to `r`, zero elsewhere. -/
def rowAt (i : ι) (r : ι → ℝ) : Matrix ι ι ℝ := of fun a b => if a = i then r b else 0

/-- The count letter `P_i(e) = 1 + |e| e_i G_{i*}`. -/
def countLetter (G : Matrix ι ι ℝ) (i : ι) (e : ℤ) : Matrix ι ι ℝ :=
  1 + |(e : ℝ)| • rowAt i (G i)

/-- The signed letter `E_i(e) = 1 - e e_i K_{i*}`. -/
def signedLetter (K : Matrix ι ι ℝ) (i : ι) (e : ℤ) : Matrix ι ι ℝ :=
  1 - (e : ℝ) • rowAt i (K i)

lemma IsSign.diagonal_mul_self {d : ι → ℝ} (hd : IsSign d) :
    diagonal d * diagonal d = (1 : Matrix ι ι ℝ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  exact hd.mul_self a

lemma diagonal_conj_apply (d : ι → ℝ) (X : Matrix ι ι ℝ) (a b : ι) :
    (diagonal d * X * diagonal d) a b = d a * X a b * d b := by
  simp [diagonal_mul, mul_diagonal]

omit [Fintype ι] in
lemma countLetter_apply (G : Matrix ι ι ℝ) (i : ι) (e : ℤ) (a b : ι) :
    countLetter G i e a b = (1 : Matrix ι ι ℝ) a b + if a = i then |(e : ℝ)| * G i b else 0 := by
  unfold countLetter rowAt
  by_cases h : a = i
  · subst h; simp
  · simp [h]

omit [Fintype ι] in
lemma signedLetter_apply (K : Matrix ι ι ℝ) (i : ι) (e : ℤ) (a b : ι) :
    signedLetter K i e a b = (1 : Matrix ι ι ℝ) a b - if a = i then (e : ℝ) * K i b else 0 := by
  unfold signedLetter rowAt
  by_cases h : a = i
  · subst h; simp
  · simp [h]

lemma conj_signedLetter_apply {d : ι → ℝ} (hd : IsSign d) (K : Matrix ι ι ℝ) (i : ι) (e : ℤ)
    (a b : ι) :
    (diagonal d * signedLetter K i e * diagonal d) a b =
      (1 : Matrix ι ι ℝ) a b + if a = i then -((e : ℝ) * (d i * d b) * K i b) else 0 := by
  rw [diagonal_conj_apply, signedLetter_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i
    · subst hai; simp only [Matrix.one_apply_eq, ite_true]; linear_combination hd.mul_self a
    · simp only [Matrix.one_apply_eq, hai, ite_false]; linear_combination hd.mul_self a
  · by_cases hai : a = i
    · subst hai; simp only [Matrix.one_apply_ne hab, ite_true]; ring
    · simp [Matrix.one_apply_ne hab, hai]

/-- **The sign rule for one letter.** `D E_i(e) D = P_i(e)` iff `-e d_i d_b K_{ib} = |e| G_{ib}`
for every `b`. No zero diagonal, symmetry or connectedness is assumed. -/
theorem signRule_letter {d : ι → ℝ} (hd : IsSign d) (G K : Matrix ι ι ℝ) (i : ι) (e : ℤ) :
    diagonal d * signedLetter K i e * diagonal d = countLetter G i e ↔
      ∀ b, -((e : ℝ) * (d i * d b) * K i b) = |(e : ℝ)| * G i b := by
  constructor
  · intro h b
    have := congrFun (congrFun h i) b
    rw [conj_signedLetter_apply hd, countLetter_apply] at this
    simpa using this
  · intro h
    ext a b
    rw [conj_signedLetter_apply hd, countLetter_apply]
    split_ifs with hai
    · subst hai; rw [h b]
    · rfl

/-- Factorwise conjugacy by a diagonal of signs gives conjugacy of the products. -/
theorem IsSign.conj_list_prod {d : ι → ℝ} (hd : IsSign d)
    (L : List (Matrix ι ι ℝ × Matrix ι ι ℝ)) (h : ∀ p ∈ L, diagonal d * p.1 * diagonal d = p.2) :
    diagonal d * (L.map Prod.fst).prod * diagonal d = (L.map Prod.snd).prod := by
  induction L with
  | nil => simpa using hd.diagonal_mul_self
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← h p (by simp), ← ih (fun q hq => h q (by simp [hq]))]
    simp only [mul_assoc]
    rw [← mul_assoc (diagonal d) (diagonal d), hd.diagonal_mul_self, one_mul]

/-- **The sign rule for words**: letterwise conjugacy gives conjugacy of the products. -/
theorem signRule_word {d : ι → ℝ} (hd : IsSign d) (G K : Matrix ι ι ℝ) (w : List (ι × ℤ))
    (h : ∀ l ∈ w, diagonal d * signedLetter K l.1 l.2 * diagonal d = countLetter G l.1 l.2) :
    diagonal d * (w.map fun l => signedLetter K l.1 l.2).prod * diagonal d =
      (w.map fun l => countLetter G l.1 l.2).prod := by
  have := hd.conj_list_prod (w.map fun l => (signedLetter K l.1 l.2, countLetter G l.1 l.2))
    (by
      intro p hp
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
      exact h l hl)
  simpa [List.map_map, Function.comp_def] using this

/-- **Adjacent centres carry letters of opposite signs** for a skew `K` whose pattern `G` is
symmetric: if letters at `i` and `j` with `G_{ij} ≠ 0` both satisfy the sign rule, their
exponents have opposite signs. -/
theorem signRule_opposite {d : ι → ℝ} (hd : IsSign d) {G K : Matrix ι ι ℝ}
    (hK : ∀ a b, K b a = -K a b) (hG : ∀ a b, G b a = G a b) {i j : ι} {e e' : ℤ}
    (he : e ≠ 0) (he' : e' ≠ 0) (hij : G i j ≠ 0)
    (h1 : diagonal d * signedLetter K i e * diagonal d = countLetter G i e)
    (h2 : diagonal d * signedLetter K j e' * diagonal d = countLetter G j e') :
    e * e' < 0 := by
  have c1 := (signRule_letter hd G K i e).1 h1 j
  have c2 := (signRule_letter hd G K j e').1 h2 i
  rw [hK, hG] at c2
  have key : ((e' : ℝ) * |(e : ℝ)| + (e : ℝ) * |(e' : ℝ)|) * G i j = 0 := by
    linear_combination (-(e' : ℝ)) * c1 - (e : ℝ) * c2
  have k2 : (e' : ℝ) * |(e : ℝ)| + (e : ℝ) * |(e' : ℝ)| = 0 :=
    (mul_eq_zero.1 key).resolve_right hij
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have he0' : (e' : ℝ) ≠ 0 := by exact_mod_cast he'
  have : (e : ℝ) * e' < 0 := by
    rcases lt_or_gt_of_ne he0 with h | h <;> rcases lt_or_gt_of_ne he0' with h' | h'
    · rw [abs_of_neg h, abs_of_neg h'] at k2; nlinarith
    · nlinarith
    · nlinarith
    · rw [abs_of_pos h, abs_of_pos h'] at k2; nlinarith
  exact_mod_cast this

omit [Fintype ι] in
/-- **The canonical orientation.** For a symmetric `G` and a 2-colouring `ε` (signs `±1` with
`ε_b = -ε_a` whenever `G_{ab} ≠ 0`), the parity-graded form `K_{ab} = -ε_a G_{ab}` is skew, and
every letter at `i` whose exponent has the sign of `ε_i` (`e ε_i ≥ 0`) is a count letter: the
sign rule holds with `D = 1`. -/
theorem signRule_canonical {G : Matrix ι ι ℝ} {ε : ι → ℝ} (hε : IsSign ε)
    (hG : ∀ a b, G b a = G a b) (hbip : ∀ a b, G a b ≠ 0 → ε b = -ε a) :
    let K : Matrix ι ι ℝ := of fun a b => -(ε a * G a b)
    (∀ a b, K b a = -K a b) ∧
      ∀ i (e : ℤ), 0 ≤ (e : ℝ) * ε i → signedLetter K i e = countLetter G i e := by
  intro K
  refine ⟨fun a b => ?_, fun i e he => ?_⟩
  · simp only [K, of_apply, hG a b]
    by_cases h : G a b = 0
    · simp [h]
    · rw [hbip a b h]; ring
  · have he' : (e : ℝ) * ε i = |(e : ℝ)| := by
      rw [← abs_of_nonneg he, abs_mul, hε.abs_eq, mul_one]
    ext a b
    rw [signedLetter_apply, countLetter_apply]
    split_ifs with hai
    · subst hai; simp only [K, of_apply]; rw [← he']; ring
    · simp

/-- **Entrywise domination of products.** If `|E_k| ≤ P_k` entrywise for each factor, then
`|∏ E_k| ≤ ∏ P_k` entrywise. -/
lemma abs_list_prod_le (L : List (Matrix ι ι ℝ × Matrix ι ι ℝ))
    (hL : ∀ p ∈ L, ∀ a b, |p.1 a b| ≤ p.2 a b) (a b : ι) :
    |(L.map Prod.fst).prod a b| ≤ (L.map Prod.snd).prod a b := by
  induction L generalizing a b with
  | nil => simp only [List.map_nil, List.prod_nil, Matrix.one_apply]; split_ifs <;> simp
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    have hP : ∀ i j, 0 ≤ p.2 i j := fun i j => (abs_nonneg _).trans (hL p (by simp) i j)
    have hrest : ∀ q ∈ L, ∀ a b, |q.1 a b| ≤ q.2 a b := fun q hq => hL q (by simp [hq])
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hL p (by simp) a k) (ih hrest k b) (abs_nonneg _) (hP a k)

omit [Fintype ι] in
/-- `|K| ≤ G` entrywise gives `|E_i(e)| ≤ P_i(e)` entrywise. -/
lemma abs_signedLetter_le {G K : Matrix ι ι ℝ} (hKG : ∀ a b, |K a b| ≤ G a b) (i : ι) (e : ℤ)
    (a b : ι) : |signedLetter K i e a b| ≤ countLetter G i e a b := by
  rw [signedLetter_apply, countLetter_apply]
  have h1 : |(1 : Matrix ι ι ℝ) a b| = (1 : Matrix ι ι ℝ) a b := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  split_ifs with hai
  · calc |(1 : Matrix ι ι ℝ) a b - (e : ℝ) * K i b|
        ≤ |(1 : Matrix ι ι ℝ) a b| + |(e : ℝ) * K i b| := abs_sub _ _
      _ ≤ (1 : Matrix ι ι ℝ) a b + |(e : ℝ)| * G i b := by
          rw [h1, abs_mul]; gcongr; exact hKG i b
  · simp [h1]

/-- **Word-level domination**: `|K| ≤ G` entrywise gives `|E_W| ≤ P_W` entrywise for every word,
whatever the signs of the exponents. -/
theorem abs_signedWord_le {G K : Matrix ι ι ℝ} (hKG : ∀ a b, |K a b| ≤ G a b)
    (w : List (ι × ℤ)) (a b : ι) :
    |(w.map fun l => signedLetter K l.1 l.2).prod a b| ≤
      (w.map fun l => countLetter G l.1 l.2).prod a b := by
  have := abs_list_prod_le (w.map fun l => (signedLetter K l.1 l.2, countLetter G l.1 l.2))
    (by
      intro p hp
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hp
      exact abs_signedLetter_le hKG l.1 l.2) a b
  simpa [List.map_map, Function.comp_def] using this

end Matrix
