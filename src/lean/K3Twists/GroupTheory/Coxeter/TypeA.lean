/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.Coxeter.GeometricRepresentation
import Mathlib.Data.Sym.Card
import Mathlib.Order.Sym2

/-!
# The longest element of the Weyl group of type `A_n`

The root system of type `A_n` sits in `ℤ^{n+1}` with basis `ε_0, …, ε_n`: the simple roots are
`α_k = ε_k - ε_{k+1}`, the positive roots are the `ε_a - ε_b` with `a < b`, which are the sums
`α_a + ⋯ + α_{b-1}`, and the Weyl group acts by permuting the `ε_k`, the simple reflection `s_k`
exchanging `ε_k` and `ε_{k+1}`. This file writes the vectors of `ℤ^n = ⊕ ℤα_k` in these
coordinates (`CoxeterMatrix.epsCoordA`, indexed by `ℕ`, so that `A_n` sits inside `A_{n+1}` with
the same coordinates) and proves that the standard reflection `stdReflect (extA n) k` of
`GroupTheory/Coxeter/GeometricRepresentation.lean` is the transposition of `ε_k` and `ε_{k+1}`
(`CoxeterMatrix.epsCoordA_stdReflect`). A word then acts by a permutation of the `ε_k`
(`CoxeterMatrix.epsCoordA_stdWord`), and its prefix roots are differences `ε_a - ε_b`
(`CoxeterMatrix.map_epsCoordA_stdPrefixRoots`).

For the word `longestWordA n = [0] ++ [1, 0] ++ ⋯ ++ [n-1, …, 0]` the permutation is the
reversal `ε_k ↦ ε_{n-k}`, and every prefix root is a positive root. So, for every `n`, the word
sends `α_i` to `-α_{n-1-i}` and all `n(n+1)/2` positive roots to negative roots, and it is a
reduced word for the longest element `w₀` of `W(A_n)`, whose diagram automorphism `-w₀` is
`i ↦ n-1-i`. The computations of `GeometricRepresentation.lean` checked these statements for
`n ≤ 6`.

## Main results

* `CoxeterMatrix.epsCoordA_stdReflect`: `s_k` acts on the coordinates `ε_j` as the transposition
  of `k` and `k + 1`.
* `CoxeterMatrix.mem_positiveRootsA_iff`: the positive roots `positiveRootsA n` are the vectors
  with coordinates `ε_a - ε_b`, `a < b ≤ n`.
* `CoxeterMatrix.stdReflect_mem_positiveRootsA'`: `s_i` maps the positive roots other than `α_i`
  to positive roots.
* `CoxeterMatrix.stdWord_longestWordA'`: `longestWordA n` sends `α_i` to `-α_{n-1-i}`.
* `CoxeterMatrix.isRootPositive_longestWordA'`: `longestWordA n` is root-positive.
* `CoxeterMatrix.inversionCount_longestWordA'`, `CoxeterMatrix.isReduced_longestWordA'`:
  `longestWordA n` sends all `n(n+1)/2` positive roots out of the positive roots, so it is a
  reduced word of `W(A_n)`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. IV–VI, Planche I (the root system of type
  `A_l`: the roots `ε_i - ε_j`, the basis `ε_i - ε_{i+1}` and its positive roots, the Weyl group
  acting by permutations of the `ε_i`).
* J. E. Humphreys, *Reflection groups and Coxeter groups*, §1.8 (the longest element `w₀`, which
  sends the positive roots to negative roots and has length the number of positive roots), §5.6
  (the length of `w` is the number of positive roots sent to negative roots; only the lower bound
  `CoxeterSystem.inversionCount_le_length` is used).
-/

namespace CoxeterMatrix

open BilinearForm

variable {n : ℕ}

/-! ### The coordinates `ε_k` -/

/-- The coordinates of `v ∈ ℤ^n` moved up by one and extended by zero to `ℕ`:
`padCoordA v (k + 1) = v_k` for `k < n`, and `padCoordA v k = 0` for `k = 0` and for `k > n`. -/
def padCoordA (v : Fin n → ℤ) (k : ℕ) : ℤ :=
  if h : 0 < k ∧ k ≤ n then v ⟨k - 1, by omega⟩ else 0

/-- The coordinates of `v = Σ v_k α_k ∈ ℤ^n` in the basis `ε_0, ε_1, …` for the simple roots
`α_k = ε_k - ε_{k+1}` of `A_n`: the coefficient of `ε_k` is `v_k - v_{k-1}`, with
`v_{-1} = v_n = 0`. -/
def epsCoordA (v : Fin n → ℤ) (k : ℕ) : ℤ := padCoordA v (k + 1) - padCoordA v k

/-- The vector `ε_a - ε_b`, as a function `ℕ → ℤ`. -/
def epsRootA (a b k : ℕ) : ℤ := (if k = a then 1 else 0) - (if k = b then 1 else 0)

@[simp] theorem padCoordA_zero (v : Fin n → ℤ) : padCoordA v 0 = 0 := by
  simp [padCoordA]

theorem padCoordA_succ (v : Fin n → ℤ) (k : Fin n) : padCoordA v (k + 1) = v k := by
  have := k.isLt
  rw [padCoordA, dite_eq_left (by omega)]
  simp

/-- The partial sums of the coordinates `ε_k` recover `v`, so `epsCoordA` is injective. -/
theorem epsCoordA_injective : Function.Injective (epsCoordA (n := n)) := by
  intro v w h
  have hpad : ∀ k, padCoordA v k = padCoordA w k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := congrFun h k
      simp only [epsCoordA] at this
      omega
  funext k
  rw [← padCoordA_succ v k, ← padCoordA_succ w k, hpad]

theorem epsCoordA_neg (v : Fin n → ℤ) : epsCoordA (-v) = -epsCoordA v := by
  funext k
  simp only [epsCoordA, padCoordA, Pi.neg_apply]
  split_ifs <;> ring

/-- The simple root `α_i` is `ε_i - ε_{i+1}`. -/
theorem epsCoordA_stdRoot (i : Fin n) : epsCoordA (stdRoot i) = epsRootA i (i + 1) := by
  funext k
  have := i.isLt
  simp only [epsCoordA, padCoordA, epsRootA, stdRoot, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- The interval sum `α_a + ⋯ + α_c` is `ε_a - ε_{c+1}`. -/
theorem epsCoordA_indicator {a c : Fin n} (h : a ≤ c) :
    epsCoordA (fun k => if a ≤ k ∧ k ≤ c then 1 else 0) = epsRootA a (c + 1) := by
  funext k
  have := c.isLt
  have h' : (a : ℕ) ≤ c := h
  simp only [epsCoordA, padCoordA, epsRootA, Fin.le_iff_val_le_val]
  split_ifs <;> omega

/-- For `a ≠ b`, the vector `ε_a - ε_b` determines `a` and `b`. -/
theorem eq_of_epsRootA_eq {a b a' b' : ℕ} (hab : a ≠ b) (h : epsRootA a b = epsRootA a' b') :
    a = a' ∧ b = b' := by
  have h1 := congrFun h a
  have h2 := congrFun h b
  simp only [epsRootA] at h1 h2
  split_ifs at h1 h2 <;> omega

/-! ### The simple reflections are transpositions -/

theorem sum_ite_eq_padCoordA (v : Fin n → ℤ) (m : ℕ) :
    ∑ k : Fin n, (if (k : ℕ) + 1 = m then v k else 0) = padCoordA v m := by
  rw [padCoordA]
  split_ifs with h
  · set k₀ : Fin n := ⟨m - 1, by omega⟩
    have hk₀ : (k₀ : ℕ) = m - 1 := rfl
    rw [Finset.sum_eq_single k₀ (fun k _ hk => ite_eq_right fun h' => hk (Fin.ext (by omega)))
      (fun h' => absurd (Finset.mem_univ _) h'), ite_eq_left (by omega)]
  · exact Finset.sum_eq_zero fun k _ =>
      ite_eq_right fun h' => h ⟨by omega, by have := k.isLt; omega⟩

/-- The Gram matrix of `A_n`, `-2` on the diagonal and `1` between neighbours, as a sum of
indicators. -/
theorem mul_rootMatrix_extA (v : Fin n → ℤ) (k j : Fin n) :
    v k * rootMatrix (extA n) k j = (if (k : ℕ) + 1 = j then v k else 0) -
      2 * (if (k : ℕ) + 1 = j + 1 then v k else 0) +
        (if (k : ℕ) + 1 = j + 1 + 1 then v k else 0) := by
  simp only [rootMatrix, extA, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- The pairing of `v` with `α_j` for the form of `A_n` is `v_{j-1} - 2v_j + v_{j+1}`. -/
theorem sum_mul_rootMatrix_extA (v : Fin n → ℤ) (j : Fin n) :
    ∑ k, v k * rootMatrix (extA n) k j =
      padCoordA v j - 2 * padCoordA v (j + 1) + padCoordA v (j + 1 + 1) := by
  simp only [mul_rootMatrix_extA, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_ite_eq_padCoordA]

/-- `s_j` changes only the coordinate `v_j` of `v`, to `v_{j-1} - v_j + v_{j+1}`. -/
theorem padCoordA_stdReflect (j : Fin n) (v : Fin n → ℤ) (m : ℕ) :
    padCoordA (stdReflect (extA n) j v) m =
      if m = j + 1 then padCoordA v j - padCoordA v (j + 1) + padCoordA v (j + 1 + 1)
      else padCoordA v m := by
  split_ifs with hm
  · subst hm
    rw [padCoordA_succ, stdReflect, Pi.add_apply, Pi.smul_apply, sum_mul_rootMatrix_extA,
      padCoordA_succ, stdRoot, Pi.single_eq_same, smul_eq_mul, mul_one]
    ring
  · unfold padCoordA
    split_ifs with h
    · rw [stdReflect, Pi.add_apply, Pi.smul_apply, stdRoot, Pi.single_eq_of_ne, smul_zero,
        add_zero]
      intro h'
      apply hm
      have := congrArg Fin.val h'
      rw [Fin.val_mk] at this
      omega
    · rfl

/-- **The simple reflection `s_j` of `A_n` exchanges `ε_j` and `ε_{j+1}`.** -/
theorem epsCoordA_stdReflect (j : Fin n) (v : Fin n → ℤ) :
    epsCoordA (stdReflect (extA n) j v) = epsCoordA v ∘ Equiv.swap (j : ℕ) (j + 1) := by
  funext k
  rw [Function.comp_apply, Equiv.swap_apply_def]
  simp only [epsCoordA, padCoordA_stdReflect]
  by_cases h1 : k = j
  · subst h1
    simp
    ring
  · by_cases h2 : k = j + 1
    · subst h2
      simp
    · simp [h1, h2]

/-! ### Words act by permutations -/

/-- The permutation of `ℕ` by which a word acts on the coordinates `ε_k`:
`wordPermA [i₁, …, i_m] = τ_{i_m} ∘ ⋯ ∘ τ_{i₁}` for `τ_i` the transposition of `i` and `i + 1`.
The word sends `ε_k` to `ε_{(wordPermA ω)⁻¹ k}`. -/
def wordPermA : List ℕ → Equiv.Perm ℕ
  | [] => 1
  | i :: ω => wordPermA ω * Equiv.swap i (i + 1)

theorem wordPermA_append (ω₁ ω₂ : List ℕ) :
    wordPermA (ω₁ ++ ω₂) = wordPermA ω₂ * wordPermA ω₁ := by
  induction ω₁ with
  | nil => simp [wordPermA]
  | cons i ω₁ ih => rw [List.cons_append, wordPermA, ih, wordPermA, mul_assoc]

/-- **A word of `A_n` acts on the coordinates `ε_k` by the permutation `wordPermA`.** -/
theorem epsCoordA_stdWord (ω : List (Fin n)) (v : Fin n → ℤ) :
    epsCoordA (stdWord (extA n) ω v) = epsCoordA v ∘ wordPermA (ω.map Fin.val) := by
  induction ω with
  | nil => simp [stdWord, wordPermA]
  | cons i ω ih =>
    rw [List.map_cons, wordPermA, Equiv.Perm.coe_mul, ← Function.comp_assoc, ← ih]
    exact epsCoordA_stdReflect i (stdWord (extA n) ω v)

/-- The word `[m-1, …, 1, 0]` acts by the cycle `k ↦ k + 1` (`k < m`), `m ↦ 0`. -/
theorem wordPermA_range_reverse (m k : ℕ) :
    wordPermA (List.range m).reverse k = if k < m then k + 1 else if k = m then 0 else k := by
  induction m generalizing k with
  | zero =>
    simp only [List.range_zero, List.reverse_nil, wordPermA, Equiv.Perm.coe_one, id_eq]
    split_ifs <;> omega
  | succ m ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      wordPermA, Equiv.Perm.mul_apply, ih, Equiv.swap_apply_def]
    split_ifs <;> omega

/-- As a word of natural numbers, `longestWordA (n + 1)` is `longestWordA n` followed by
`[n, …, 1, 0]`. -/
theorem map_val_longestWordA (n : ℕ) :
    (longestWordA (n + 1)).map Fin.val =
      (longestWordA n).map Fin.val ++ (List.range (n + 1)).reverse := by
  rw [longestWordA, List.map_append, List.map_map, List.map_reverse,
    List.map_coe_finRange_eq_range]
  rfl

/-- **`longestWordA n` acts on the coordinates `ε_0, …, ε_n` by the reversal `k ↦ n - k`.** -/
theorem wordPermA_longestWordA (n k : ℕ) :
    wordPermA ((longestWordA n).map Fin.val) k = if k ≤ n then n - k else k := by
  induction n generalizing k with
  | zero =>
    simp only [longestWordA, List.map_nil, wordPermA, Equiv.Perm.coe_one, id_eq]
    split_ifs <;> omega
  | succ n ih =>
    rw [map_val_longestWordA, wordPermA_append, Equiv.Perm.mul_apply, ih,
      wordPermA_range_reverse]
    split_ifs <;> omega

/-- **`w₀ = longestWordA n` sends `α_i` to `-α_{n-1-i}`**, for every `n`. -/
theorem stdWord_longestWordA' (i : Fin n) :
    stdWord (extA n) (longestWordA n) (stdRoot i) = -stdRoot i.rev := by
  apply epsCoordA_injective
  rw [epsCoordA_stdWord, epsCoordA_neg, epsCoordA_stdRoot, epsCoordA_stdRoot]
  funext k
  have := i.isLt
  simp only [Function.comp_apply, wordPermA_longestWordA, epsRootA, Pi.neg_apply, Fin.val_rev]
  split_ifs <;> omega

/-! ### Prefix roots -/

/-- The prefix roots of a word in the coordinates `ε_k`:
`epsPrefixRootsA (i :: ω) = (ε_i - ε_{i+1}) :: τ_i (epsPrefixRootsA ω)`, the transposition `τ_i`
of `i` and `i + 1` acting on coordinates. -/
def epsPrefixRootsA : List ℕ → List (ℕ → ℤ)
  | [] => []
  | i :: ω => epsRootA i (i + 1) :: (epsPrefixRootsA ω).map (· ∘ Equiv.swap i (i + 1))

/-- **The prefix roots of a word of `A_n` in the coordinates `ε_k`.** -/
theorem map_epsCoordA_stdPrefixRoots (ω : List (Fin n)) :
    (stdPrefixRoots (extA n) ω).map epsCoordA = epsPrefixRootsA (ω.map Fin.val) := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    rw [stdPrefixRoots, List.map_cons, List.map_map, List.map_cons, epsPrefixRootsA, ← ih,
      List.map_map, epsCoordA_stdRoot]
    congr 1
    exact List.map_congr_left fun v _ => epsCoordA_stdReflect i v

/-- The prefix roots of `ω₁ ++ ω₂` are those of `ω₁`, followed by those of `ω₂` moved by
`ω₁`. -/
theorem epsPrefixRootsA_append (ω₁ ω₂ : List ℕ) :
    epsPrefixRootsA (ω₁ ++ ω₂) =
      epsPrefixRootsA ω₁ ++ (epsPrefixRootsA ω₂).map (· ∘ wordPermA ω₁) := by
  induction ω₁ with
  | nil => simp [epsPrefixRootsA, wordPermA]
  | cons i ω₁ ih =>
    simp only [List.cons_append, epsPrefixRootsA, ih, List.map_append, List.map_map, wordPermA,
      Equiv.Perm.coe_mul]
    rfl

/-- The prefix roots of `[m-1, …, 1, 0]` are the `ε_a - ε_m`, `a < m`. -/
theorem exists_of_mem_epsPrefixRootsA_range_reverse {m : ℕ} {f : ℕ → ℤ}
    (hf : f ∈ epsPrefixRootsA (List.range m).reverse) : ∃ a < m, f = epsRootA a m := by
  induction m generalizing f with
  | zero => simp [epsPrefixRootsA] at hf
  | succ m ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      epsPrefixRootsA, List.mem_cons, List.mem_map] at hf
    rcases hf with rfl | ⟨g, hg, rfl⟩
    · exact ⟨m, Nat.lt_succ_self m, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := ih hg
      refine ⟨a, by omega, ?_⟩
      funext k
      simp only [Function.comp_apply, epsRootA, Equiv.swap_apply_def]
      split_ifs <;> omega

/-- The prefix roots of `longestWordA n` are the `ε_a - ε_b` with `a < b ≤ n`. -/
theorem exists_of_mem_epsPrefixRootsA_longestWordA {f : ℕ → ℤ}
    (hf : f ∈ epsPrefixRootsA ((longestWordA n).map Fin.val)) :
    ∃ a b, a < b ∧ b ≤ n ∧ f = epsRootA a b := by
  induction n generalizing f with
  | zero => simp [longestWordA, epsPrefixRootsA] at hf
  | succ n ih =>
    rw [map_val_longestWordA, epsPrefixRootsA_append, List.mem_append, List.mem_map] at hf
    rcases hf with hf | ⟨g, hg, rfl⟩
    · obtain ⟨a, b, hab, hb, rfl⟩ := ih hf
      exact ⟨a, b, hab, by omega, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := exists_of_mem_epsPrefixRootsA_range_reverse hg
      refine ⟨n - a, n + 1, by omega, le_rfl, ?_⟩
      funext k
      simp only [Function.comp_apply, epsRootA, wordPermA_longestWordA]
      split_ifs <;> omega

/-! ### Positive roots -/

/-- **The positive roots of `A_n` are the `ε_a - ε_b` with `a < b ≤ n`.** -/
theorem mem_positiveRootsA_iff (v : Fin n → ℤ) :
    v ∈ positiveRootsA n ↔ ∃ a b, a < b ∧ b ≤ n ∧ epsCoordA v = epsRootA a b := by
  simp only [positiveRootsA, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨a, c, hac, rfl⟩
    exact ⟨a, c + 1, Nat.lt_succ_of_le hac, c.isLt, epsCoordA_indicator hac⟩
  · rintro ⟨a, b, hab, hb, h⟩
    have hle : (⟨a, by omega⟩ : Fin n) ≤ ⟨b - 1, by omega⟩ :=
      Fin.le_iff_val_le_val.2 (show a ≤ b - 1 by omega)
    refine ⟨_, _, hle, epsCoordA_injective ?_⟩
    rw [epsCoordA_indicator hle, h, Fin.val_mk, Fin.val_mk, Nat.sub_add_cancel (by omega)]

/-- A positive root of `A_n` has nonnegative coordinates and is not zero. -/
theorem nonneg_of_mem_positiveRootsA {v : Fin n → ℤ} (hv : v ∈ positiveRootsA n) :
    (∀ k, 0 ≤ v k) ∧ v ≠ 0 := by
  simp only [positiveRootsA, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists] at hv
  obtain ⟨a, c, hac, rfl⟩ := hv
  refine ⟨fun k => by dsimp only; split_ifs <;> norm_num, fun h => ?_⟩
  have := congrFun h a
  simp [hac] at this

/-- `A_n` has `n(n+1)/2` positive roots. -/
theorem card_positiveRootsA (n : ℕ) : (positiveRootsA n).card = n * (n + 1) / 2 := by
  rw [positiveRootsA, Finset.card_image_of_injOn, ← Fintype.card_subtype,
    ← Fintype.card_congr Sym2.sortEquiv, Sym2.card, Fintype.card_fin, Nat.choose_two_right,
    Nat.add_sub_cancel, mul_comm]
  rintro ⟨a, c⟩ hac ⟨a', c'⟩ hac' h
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hac hac'
  have h2 := congrArg epsCoordA h
  dsimp only at h2
  rw [epsCoordA_indicator hac, epsCoordA_indicator hac'] at h2
  obtain ⟨h3, h4⟩ := eq_of_epsRootA_eq (by omega) h2
  simp only [Prod.mk.injEq]
  exact ⟨Fin.ext h3, Fin.ext (by omega)⟩

/-- **`s_i` maps the positive roots other than `α_i` to positive roots**, for every `n`. -/
theorem stdReflect_mem_positiveRootsA' (i : Fin n) (y : Fin n → ℤ)
    (hy : y ∈ positiveRootsA n) (hne : y ≠ stdRoot i) :
    stdReflect (extA n) i y ∈ positiveRootsA n := by
  obtain ⟨a, b, hab, hb, h⟩ := (mem_positiveRootsA_iff y).1 hy
  have hne' : ¬(a = i ∧ b = i + 1) := by
    rintro ⟨rfl, rfl⟩
    exact hne (epsCoordA_injective (by rw [h, epsCoordA_stdRoot]))
  have := i.isLt
  refine (mem_positiveRootsA_iff _).2 ⟨Equiv.swap (i : ℕ) (i + 1) a,
    Equiv.swap (i : ℕ) (i + 1) b, ?_, ?_, ?_⟩
  · simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  · simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  · rw [epsCoordA_stdReflect, h]
    funext k
    simp only [Function.comp_apply, epsRootA, Equiv.swap_apply_def]
    split_ifs <;> omega

/-! ### The longest word -/

/-- **`longestWordA n` is root-positive**, for every `n`: its prefix roots are the
`ε_a - ε_b` with `a < b`. -/
theorem isRootPositive_longestWordA' (n : ℕ) :
    IsRootPositive (rootForm (extA n)) stdRoot (longestWordA n) := by
  refine isRootPositive_rootForm_of _ fun β hβ => nonneg_of_mem_positiveRootsA ?_
  have hmem : epsCoordA β ∈ epsPrefixRootsA ((longestWordA n).map Fin.val) := by
    rw [← map_epsCoordA_stdPrefixRoots]
    exact List.mem_map_of_mem hβ
  obtain ⟨a, b, hab, hb, h⟩ := exists_of_mem_epsPrefixRootsA_longestWordA hmem
  exact (mem_positiveRootsA_iff β).2 ⟨a, b, hab, hb, h⟩

/-- **`w₀ = longestWordA n` sends every positive root out of the positive roots**, for every
`n`: it sends `ε_a - ε_b` to `ε_{n-a} - ε_{n-b}`. -/
theorem inversionCount_longestWordA' (n : ℕ) :
    ((positiveRootsA n).filter fun x => stdWord (extA n) (longestWordA n) x ∉
      positiveRootsA n).card = n * (n + 1) / 2 := by
  rw [Finset.filter_true_of_mem fun x hx => ?_, card_positiveRootsA]
  obtain ⟨a, b, hab, hb, h⟩ := (mem_positiveRootsA_iff x).1 hx
  intro hx'
  obtain ⟨a', b', hab', hb', h'⟩ := (mem_positiveRootsA_iff _).1 hx'
  rw [epsCoordA_stdWord, h] at h'
  have h1 := congrFun h' (n - a)
  have h2 := congrFun h' (n - b)
  simp only [Function.comp_apply, wordPermA_longestWordA, epsRootA] at h1 h2
  split_ifs at h1 h2 <;> omega

/-- **`longestWordA n` is a reduced word** of `W(A_n)`, for every `n`, by the inversion count of
the reflection representation: it moves all `n(n+1)/2` positive roots out of the positive
roots. -/
theorem isReduced_longestWordA' (n : ℕ) :
    (CoxeterMatrix.A n).toCoxeterSystem.IsReduced (longestWordA n) := by
  rw [A_eq_ofExt]
  have hρ := reflectionRep_wordProd_apply (extA n) (extA_symm n)
    (rootForm_symm (extA n) (extA_symm n)) (rootForm_stdRoot_self (extA n))
    (rootForm_stdRoot_of_ne (extA n))
  refine (ofExt (extA n) (extA_symm n)).toCoxeterSystem.isReduced_of_length_le_inversionCount
    (reflectionRep (extA n) (extA_symm n) (rootForm_symm (extA n) (extA_symm n))
      (rootForm_stdRoot_self (extA n)) (rootForm_stdRoot_of_ne (extA n)))
    (Φ := positiveRootsA n) (fun i => ⟨stdRoot i, fun y hy hne => ?_⟩) ?_
  · have h := hρ [i] y
    rw [CoxeterSystem.wordProd_singleton] at h
    rw [LinearEquiv.smul_def, h, reflectWord_cons_apply, reflectWord_nil, one_apply_eq_self,
      reflect_rootForm]
    exact stdReflect_mem_positiveRootsA' i y hy hne
  · rw [CoxeterSystem.inversionCount, length_longestWordA]
    refine le_of_eq ?_
    rw [← inversionCount_longestWordA' n]
    congr 1
    refine Finset.filter_congr fun x _ => ?_
    rw [LinearEquiv.smul_def, hρ, reflectWord_rootForm]

end CoxeterMatrix
