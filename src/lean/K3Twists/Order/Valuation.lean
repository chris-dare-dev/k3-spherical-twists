/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.ModularLattice
import Mathlib.Order.SupClosed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Valuations on a lattice

A *valuation* on a lattice `L` with values in an additive commutative group is a function `f` with

  `f (x ⊔ y) + f (x ⊓ y) = f x + f y`

for all `x y : L`. The rank and the degree of subobjects of an object of an abelian category,
taken through an additive function on objects, are valuations on its lattice of subobjects; so
are linear functions of the dimension vector on the lattice of subrepresentations.

## Main results

* `isModularLattice_of_valuation`: a lattice with a valuation that is injective on comparable
  pairs is modular. This is Birkhoff's argument for lattices with a positive valuation (*Lattice
  theory*, Chapter X), with no order on the values.
* `supClosed_setOf_isMax_valuation`, `infClosed_setOf_isMax_valuation`: the maximizers of a
  valuation with ordered values form a sublattice.
* `topkis`, `greatest_maximizer_antitone`: Topkis's monotonicity theorem for the valuations
  `w_θ = deg - θ rk`, with `rk` monotone. If `x` maximizes `w_θ` and `y` maximizes `w_θ'` with
  `θ ≤ θ'`, then `x ⊔ y` maximizes `w_θ` and `x ⊓ y` maximizes `w_θ'`; so the greatest maximizer,
  when it exists, is antitone in `θ`.
* `val_le_of_chain`, `eq_of_val_eq_of_chain`: let `⊥ = c 0 ≤ c 1 ≤ ⋯ ≤ c n = ⊤`. If on every step
  below `c k` the top maximizes `w` and on every step above it the bottom does, then `c k`
  maximizes `w` on all of `L`; if the local maximizers are unique, so is the global one. This is
  the lattice core of the uniqueness of Harder–Narasimhan filtrations.
-/

namespace Order

/-! ### Modularity -/

/-- **A valuation injective on comparable pairs forces modularity.** If `f : L → G` is a valuation
into an additive commutative group and `x ≤ y`, `f x = f y` imply `x = y`, then `L` is modular. -/
theorem isModularLattice_of_valuation {L G : Type*} [Lattice L] [AddCommGroup G] (f : L → G)
    (hval : ∀ x y, f (x ⊔ y) + f (x ⊓ y) = f x + f y)
    (hinj : ∀ {x y : L}, x ≤ y → f x = f y → x = y) : IsModularLattice L where
  sup_inf_le_assoc_of_le {x} y {z} hxz := by
    have hab : x ⊔ y ⊓ z ≤ (x ⊔ y) ⊓ z :=
      le_inf (sup_le_sup_left inf_le_left x) (sup_le hxz inf_le_right)
    have h1 : x ⊓ (y ⊓ z) = x ⊓ y := by
      rw [inf_comm y z, ← inf_assoc, inf_eq_left.mpr hxz]
    have h2 : x ⊔ y ⊔ z = y ⊔ z := by
      rw [sup_comm x y, sup_assoc, sup_eq_right.mpr hxz]
    have e1 := hval x (y ⊓ z)
    have e2 := hval (x ⊔ y) z
    have e3 := hval x y
    have e4 := hval y z
    rw [h1] at e1
    rw [h2] at e2
    refine (hinj hab ?_).ge
    rw [eq_sub_of_add_eq e1, eq_sub_of_add_eq' e2, eq_sub_of_add_eq e3, eq_sub_of_add_eq e4]
    abel

section Valuation

variable {L K : Type*} [Lattice L] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Maximizers and Topkis's theorem -/

/-- The maximizers of a valuation are closed under `⊔` and `⊓`. -/
theorem isMax_sup_inf_of_valuation {w : L → K}
    (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) {x y : L} (hx : ∀ z, w z ≤ w x)
    (hy : ∀ z, w z ≤ w y) : (∀ z, w z ≤ w (x ⊔ y)) ∧ ∀ z, w z ≤ w (x ⊓ y) := by
  have := hw x y
  have h1 := hx (x ⊔ y)
  have h2 := hy (x ⊓ y)
  exact ⟨fun z ↦ by linarith [hx z], fun z ↦ by linarith [hy z]⟩

/-- The maximizers of a valuation are closed under `⊔`. -/
theorem supClosed_setOf_isMax_valuation {w : L → K}
    (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) : SupClosed {x | ∀ z, w z ≤ w x} :=
  fun _ hx _ hy ↦ (isMax_sup_inf_of_valuation hw hx hy).1

/-- The maximizers of a valuation are closed under `⊓`. -/
theorem infClosed_setOf_isMax_valuation {w : L → K}
    (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) : InfClosed {x | ∀ z, w z ≤ w x} :=
  fun _ hx _ hy ↦ (isMax_sup_inf_of_valuation hw hx hy).2

/-- **Topkis's monotonicity theorem** for the valuations `deg - θ rk`. Let `rk` be a monotone
valuation, `deg` a valuation and `θ ≤ θ'`. If `x` maximizes `deg - θ rk` and `y` maximizes
`deg - θ' rk`, then `x ⊔ y` maximizes the first and `x ⊓ y` the second. -/
theorem topkis {rk deg : L → K} (hrk : Monotone rk)
    (hr : ∀ x y, rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y)
    (hd : ∀ x y, deg (x ⊔ y) + deg (x ⊓ y) = deg x + deg y) {θ θ' : K} (hθ : θ ≤ θ') {x y : L}
    (hx : ∀ z, deg z - θ * rk z ≤ deg x - θ * rk x)
    (hy : ∀ z, deg z - θ' * rk z ≤ deg y - θ' * rk y) :
    (∀ z, deg z - θ * rk z ≤ deg (x ⊔ y) - θ * rk (x ⊔ y)) ∧
      ∀ z, deg z - θ' * rk z ≤ deg (x ⊓ y) - θ' * rk (x ⊓ y) := by
  have e1 := hr x y
  have e2 := hd x y
  have hm : rk (x ⊓ y) ≤ rk y := hrk inf_le_right
  have h1 := hy (x ⊓ y)
  have h2 := hx (x ⊔ y)
  have p1 : 0 ≤ (θ' - θ) * (rk y - rk (x ⊓ y)) := mul_nonneg (by linarith) (by linarith)
  have e1θ : θ * rk (x ⊔ y) + θ * rk (x ⊓ y) = θ * rk x + θ * rk y := by
    rw [← mul_add, ← mul_add, e1]
  have e1θ' : θ' * rk (x ⊔ y) + θ' * rk (x ⊓ y) = θ' * rk x + θ' * rk y := by
    rw [← mul_add, ← mul_add, e1]
  have hexp : (θ' - θ) * (rk y - rk (x ⊓ y)) =
      θ' * rk y - θ' * rk (x ⊓ y) - θ * rk y + θ * rk (x ⊓ y) := by ring
  exact ⟨fun z ↦ by linarith [hx z], fun z ↦ by linarith [hy z]⟩

/-- **Greatest maximizers are antitone.** With `rk` a monotone valuation and `deg` a valuation,
if `t` is the greatest maximizer of `deg - θ rk` and `t'` maximizes `deg - θ' rk` for some
`θ' ≥ θ`, then `t' ≤ t`. -/
theorem greatest_maximizer_antitone {rk deg : L → K} (hrk : Monotone rk)
    (hr : ∀ x y, rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y)
    (hd : ∀ x y, deg (x ⊔ y) + deg (x ⊓ y) = deg x + deg y) {θ θ' : K} (hθ : θ ≤ θ') {t t' : L}
    (ht : IsGreatest {x | ∀ z, deg z - θ * rk z ≤ deg x - θ * rk x} t)
    (ht' : ∀ z, deg z - θ' * rk z ≤ deg t' - θ' * rk t') : t' ≤ t :=
  le_sup_right.trans (ht.2 (topkis hrk hr hd hθ ht.1 ht').1)

/-! ### Maximizers along a chain -/

variable {w : L → K}

/-- If `c ≤ d` and `c` maximizes `w` on `[c, d]`, then `w (y ⊓ d) ≤ w (y ⊓ c)`. -/
lemma val_inf_le (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) {c d : L} (hcd : c ≤ d)
    (H : ∀ z, c ≤ z → z ≤ d → w z ≤ w c) (y : L) : w (y ⊓ d) ≤ w (y ⊓ c) := by
  have h1 := hw (y ⊓ d) c
  have h2 : y ⊓ d ⊓ c = y ⊓ c := by rw [inf_assoc, inf_eq_right.mpr hcd]
  have h3 := H (y ⊓ d ⊔ c) le_sup_right (sup_le inf_le_right hcd)
  rw [h2] at h1
  linarith

/-- If `c ≤ d` and `c` is the only maximizer of `w` on `[c, d]`, then `w (y ⊓ d) = w (y ⊓ c)`
forces `y ⊓ d = y ⊓ c`. -/
lemma inf_eq_of_val_eq (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) {c d : L} (hcd : c ≤ d)
    (H : ∀ z, c ≤ z → z ≤ d → w z = w c → z = c) {y : L} (heq : w (y ⊓ d) = w (y ⊓ c)) :
    y ⊓ d = y ⊓ c := by
  have h1 := hw (y ⊓ d) c
  have h2 : y ⊓ d ⊓ c = y ⊓ c := by rw [inf_assoc, inf_eq_right.mpr hcd]
  rw [h2] at h1
  have hz := H (y ⊓ d ⊔ c) le_sup_right (sup_le inf_le_right hcd) (by linarith)
  exact le_antisymm (le_inf inf_le_left (sup_eq_right.mp hz)) (inf_le_inf_left y hcd)

/-- If `c ≤ d` and `d` maximizes `w` on `[c, d]`, then `w (y ⊔ c) ≤ w (y ⊔ d)`. -/
lemma val_sup_le (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) {c d : L} (hcd : c ≤ d)
    (H : ∀ z, c ≤ z → z ≤ d → w z ≤ w d) (y : L) : w (y ⊔ c) ≤ w (y ⊔ d) := by
  have h1 := hw (y ⊔ c) d
  have h2 : y ⊔ c ⊔ d = y ⊔ d := by rw [sup_assoc, sup_eq_right.mpr hcd]
  have h3 := H ((y ⊔ c) ⊓ d) (le_inf le_sup_right hcd) inf_le_right
  rw [h2] at h1
  linarith

/-- If `c ≤ d` and `d` is the only maximizer of `w` on `[c, d]`, then `w (y ⊔ c) = w (y ⊔ d)`
forces `y ⊔ c = y ⊔ d`. -/
lemma sup_eq_of_val_eq (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) {c d : L} (hcd : c ≤ d)
    (H : ∀ z, c ≤ z → z ≤ d → w z = w d → z = d) {y : L} (heq : w (y ⊔ c) = w (y ⊔ d)) :
    y ⊔ c = y ⊔ d := by
  have h1 := hw (y ⊔ c) d
  have h2 : y ⊔ c ⊔ d = y ⊔ d := by rw [sup_assoc, sup_eq_right.mpr hcd]
  rw [h2] at h1
  have hz := H ((y ⊔ c) ⊓ d) (le_inf le_sup_right hcd) inf_le_right (by linarith)
  exact le_antisymm (sup_le_sup_left hcd y) (sup_le le_sup_left (inf_eq_right.mp hz))

/-- Going up a chain from `c a` through steps whose bottoms maximize `w`:
`w (y ⊓ c (a + m)) ≤ w (y ⊓ c a)`. -/
theorem val_inf_le_of_chain (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) {c : ℕ → L}
    (hc : Monotone c) {a : ℕ} (H : ∀ j, a ≤ j → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c j))
    (y : L) : ∀ m, w (y ⊓ c (a + m)) ≤ w (y ⊓ c a)
  | 0 => le_rfl
  | m + 1 => by
    rw [← add_assoc]
    exact (val_inf_le hw (hc (Nat.le_succ _)) (H _ (Nat.le_add_right a m)) y).trans
      (val_inf_le_of_chain hw hc H y m)

/-- Going up a chain through steps whose bottoms are the only maximizers of `w`, equality of
weights forces `y ⊓ c (a + m) = y ⊓ c a`. -/
theorem inf_eq_of_val_eq_of_chain (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) {c : ℕ → L}
    (hc : Monotone c) {a : ℕ} (H : ∀ j, a ≤ j → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c j))
    (H' : ∀ j, a ≤ j → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z = w (c j) → z = c j) (y : L) :
    ∀ m, w (y ⊓ c (a + m)) = w (y ⊓ c a) → y ⊓ c (a + m) = y ⊓ c a
  | 0, _ => rfl
  | m + 1, heq => by
    rw [← add_assoc] at heq ⊢
    have hP := val_inf_le hw (hc (Nat.le_succ (a + m))) (H _ (Nat.le_add_right a m)) y
    have hQ := val_inf_le_of_chain hw hc H y m
    have hPQ : y ⊓ c (a + m + 1) = y ⊓ c (a + m) :=
      inf_eq_of_val_eq hw (hc (Nat.le_succ _)) (H' _ (Nat.le_add_right a m)) (by linarith)
    rw [hPQ]
    exact inf_eq_of_val_eq_of_chain hw hc H H' y m (by linarith)

/-- Going down a chain to `c j` from `c k` through steps whose tops maximize `w`:
`w (y ⊔ c j) ≤ w (y ⊔ c k)`. -/
theorem val_sup_le_of_chain (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) {c : ℕ → L}
    (hc : Monotone c) {k : ℕ}
    (H : ∀ j, j < k → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c (j + 1))) (y : L) :
    ∀ j, j ≤ k → w (y ⊔ c j) ≤ w (y ⊔ c k) := by
  have key : ∀ d j, j + d = k → w (y ⊔ c j) ≤ w (y ⊔ c k) := by
    intro d
    induction d with
    | zero => intro j h; rw [← h, add_zero]
    | succ d ih =>
      intro j h
      exact (val_sup_le hw (hc (Nat.le_succ j)) (H j (by omega)) y).trans (ih (j + 1) (by omega))
  exact fun j hj ↦ key (k - j) j (by omega)

/-- Going down a chain through steps whose tops are the only maximizers of `w`, equality of
weights forces `y ⊔ c j = y ⊔ c k`. -/
theorem sup_eq_of_val_eq_of_chain (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y) {c : ℕ → L}
    (hc : Monotone c) {k : ℕ}
    (H : ∀ j, j < k → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c (j + 1)))
    (H' : ∀ j, j < k → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z = w (c (j + 1)) → z = c (j + 1))
    (y : L) : ∀ j, j ≤ k → w (y ⊔ c j) = w (y ⊔ c k) → y ⊔ c j = y ⊔ c k := by
  have key : ∀ d j, j + d = k → w (y ⊔ c j) = w (y ⊔ c k) → y ⊔ c j = y ⊔ c k := by
    intro d
    induction d with
    | zero => intro j h _; rw [← h, add_zero]
    | succ d ih =>
      intro j h heq
      have hP := val_sup_le hw (hc (Nat.le_succ j)) (H j (by omega)) y
      have hQ := val_sup_le_of_chain hw hc H y (j + 1) (by omega)
      have hPQ : y ⊔ c j = y ⊔ c (j + 1) :=
        sup_eq_of_val_eq hw (hc (Nat.le_succ j)) (H' j (by omega)) (by linarith)
      rw [hPQ]
      exact ih (j + 1) (by omega) (by linarith)
  exact fun j hj ↦ key (k - j) j (by omega)

/-- On a chain ending at `⊤`, a condition on the steps `j < n` holds on all steps `j`: the steps
past `n` are trivial. -/
private lemma step_eq_of_le [BoundedOrder L] {c : ℕ → L} (hc : Monotone c) {n : ℕ}
    (hn : c n = ⊤) {j : ℕ} (hj : n ≤ j) {z : L} (hz : c j ≤ z) : z = c j := by
  have h1 : c j = ⊤ := top_le_iff.mp (hn ▸ hc hj)
  rw [h1] at hz ⊢
  exact top_le_iff.mp hz

/-- **Chain lemma.** Let `c : ℕ → L` be monotone with `c 0 = ⊥` and `c n = ⊤`. If on every step
below `k` the top maximizes the valuation `w`, and on every step from `k` to `n` the bottom
does, then `c k` maximizes `w` on all of `L`. -/
theorem val_le_of_chain [BoundedOrder L] (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y)
    {c : ℕ → L} (hc : Monotone c) (h0 : c 0 = ⊥) {n k : ℕ} (hn : c n = ⊤) (hk : k ≤ n)
    (hdown : ∀ j, j < k → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c (j + 1)))
    (hup : ∀ j, k ≤ j → j < n → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c j)) (x : L) :
    w x ≤ w (c k) := by
  have hup' : ∀ j, k ≤ j → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c j) := fun j hkj z h1 h2 ↦ by
    rcases lt_or_ge j n with hj | hj
    · exact hup j hkj hj z h1 h2
    · rw [step_eq_of_le hc hn hj h1]
  have hu := val_inf_le_of_chain hw hc hup' (x ⊔ c k) (n - k)
  have hd := val_sup_le_of_chain hw hc hdown (x ⊓ c k) 0 (Nat.zero_le _)
  rw [Nat.add_sub_cancel' hk, hn, inf_top_eq, inf_eq_right.mpr le_sup_right] at hu
  rw [h0, sup_bot_eq, sup_eq_right.mpr inf_le_right] at hd
  have := hw x (c k)
  linarith

/-- **Chain lemma, uniqueness.** With unique local maximizers in `val_le_of_chain`, `c k` is the
only maximizer of `w` on `L`. -/
theorem eq_of_val_eq_of_chain [BoundedOrder L] (hw : ∀ x y, w (x ⊔ y) + w (x ⊓ y) = w x + w y)
    {c : ℕ → L} (hc : Monotone c) (h0 : c 0 = ⊥) {n k : ℕ} (hn : c n = ⊤) (hk : k ≤ n)
    (hdown : ∀ j, j < k → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c (j + 1)))
    (hdown' : ∀ j, j < k → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z = w (c (j + 1)) → z = c (j + 1))
    (hup : ∀ j, k ≤ j → j < n → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c j))
    (hup' : ∀ j, k ≤ j → j < n → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z = w (c j) → z = c j)
    {x : L} (hx : w x = w (c k)) : x = c k := by
  have H : ∀ j, k ≤ j → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z ≤ w (c j) := fun j hkj z h1 h2 ↦ by
    rcases lt_or_ge j n with hj | hj
    · exact hup j hkj hj z h1 h2
    · rw [step_eq_of_le hc hn hj h1]
  have H' : ∀ j, k ≤ j → ∀ z, c j ≤ z → z ≤ c (j + 1) → w z = w (c j) → z = c j :=
    fun j hkj z h1 h2 h3 ↦ by
      rcases lt_or_ge j n with hj | hj
      · exact hup' j hkj hj z h1 h2 h3
      · exact step_eq_of_le hc hn hj h1
  have hu := val_inf_le_of_chain hw hc H (x ⊔ c k) (n - k)
  have hu' := inf_eq_of_val_eq_of_chain hw hc H H' (x ⊔ c k) (n - k)
  have hd := val_sup_le_of_chain hw hc hdown (x ⊓ c k) 0 (Nat.zero_le _)
  have hd' := sup_eq_of_val_eq_of_chain hw hc hdown hdown' (x ⊓ c k) 0 (Nat.zero_le _)
  rw [Nat.add_sub_cancel' hk, hn, inf_top_eq, inf_eq_right.mpr le_sup_right] at hu hu'
  rw [h0, sup_bot_eq, sup_eq_right.mpr inf_le_right] at hd hd'
  have := hw x (c k)
  have e1 := hu' (by linarith)
  have e2 := hd' (by linarith)
  exact le_antisymm (sup_eq_right.mp e1) (inf_eq_right.mp e2)

end Valuation

end Order
