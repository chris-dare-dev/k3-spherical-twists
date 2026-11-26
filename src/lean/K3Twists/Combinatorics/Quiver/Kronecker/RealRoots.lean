/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Matrix.IsotropicRankTwo
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Real roots of the Kronecker quiver

The `g`-Kronecker quiver has Tits form `q(a, b) = a² + b² - gab` on dimension vectors. Its
positive real roots, the solutions of `q(a, b) = 1`, are the dimension vectors of the stable
constituents on either side of a wall with two spherical simples `S₀, S₁`, `g = ext¹(S₀, S₁)`;
a rigid wall object of multiplicities `(a, b)` has `dim End = q(a, b)`.

* `realRoot_classification`: for `g ≥ 2` the nonnegative solutions of `q(a, b) = 1` are exactly
  `R_m = (u_{m+1}, u_m)` and `L_m = (u_m, u_{m+1})`, `m ≥ 0`, where
  `u₀ = 0, u₁ = 1, u_{m+1} = g u_m - u_{m-1}` (`u_m` is the rescaled Chebyshev polynomial
  `S_{m-1}` evaluated at `g`);
* `det_R`: the exact identity `[R_m, R_j] = u_{j-m}` for the determinant `[v, w]` of two dimension
  vectors, and `det_R_sub_ge_one`: `[R_m, R_{j+1} - R_j] ≥ 1` for all integers `m, j`, which
  orders every finite string of roots without a limiting root ratio;
* `fan_minor_ge_one`, `fan_minor_ge_one_left`: the same bound for any fan
  `v_{j+1} = g_j v_j - v_{j-1}` with `g_j ≥ 2` and adjacent minors one;
* `no_null_vector`: for `|g| ≥ 3` the form `x² + gxy + y²` has no nonzero rational zero.
-/

namespace Quiver.Kronecker

open Polynomial

/-! ### The sequence `u_m` -/

/-- `u g m`, the sequence `u₀ = 0`, `u₁ = 1`, `u_{m+1} = g u_m - u_{m-1}` on all of `ℤ`; it is
the rescaled Chebyshev polynomial `S_{m-1}` of Mathlib evaluated at `g`. -/
noncomputable def u (g m : ℤ) : ℤ :=
  (Chebyshev.S ℤ (m - 1)).eval g

@[simp] lemma u_zero (g : ℤ) : u g 0 = 0 := by
  simp [u, Chebyshev.S_neg_one]

@[simp] lemma u_one (g : ℤ) : u g 1 = 1 := by
  simp [u, Chebyshev.S_zero]

lemma u_add_one (g m : ℤ) : u g (m + 1) = g * u g m - u g (m - 1) := by
  have h := Chebyshev.S_add_one ℤ (m - 1)
  simp only [u, add_sub_cancel_right, sub_add_cancel] at h ⊢
  rw [h, eval_sub, eval_mul, eval_X]

@[simp] lemma u_two (g : ℤ) : u g 2 = g := by
  have := u_add_one g 1
  norm_num at this
  simpa using this

lemma u_neg (g m : ℤ) : u g (-m) = -u g m := by
  have h := Chebyshev.S_neg_sub_one ℤ m
  simp only [u]
  rw [show -m - 1 = -m - 1 from rfl, h, eval_neg]

/-- At `g = 2` (a pairing-two wall) the sequence is `u_m = m`. -/
lemma u_two_eq (m : ℤ) : u 2 m = m := by
  simp [u, Chebyshev.S_eval_two]

/-- A sequence satisfying the recursion of `u` that vanishes at `0` and `1` vanishes everywhere. -/
lemma eq_zero_of_rec {g : ℤ} {F : ℤ → ℤ} (hrec : ∀ k, F (k + 1) = g * F k - F (k - 1))
    (h0 : F 0 = 0) (h1 : F 1 = 0) (k : ℤ) : F k = 0 := by
  have hpos : ∀ n : ℕ, F n = 0 ∧ F (n + 1) = 0 := by
    intro n
    induction n with
    | zero => simpa using ⟨h0, h1⟩
    | succ n ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have := hrec ((n : ℤ) + 1)
      push_cast
      rw [this, ih.2, show (n : ℤ) + 1 - 1 = n by ring, ih.1]; ring
  have hneg : ∀ n : ℕ, F (-n) = 0 ∧ F (-n + 1) = 0 := by
    intro n
    induction n with
    | zero => simpa using ⟨h0, h1⟩
    | succ n ih =>
      refine ⟨?_, by push_cast; rw [show -((n : ℤ) + 1) + 1 = -n by ring]; exact ih.1⟩
      have := hrec (-(n : ℤ))
      rw [ih.2, ih.1] at this
      push_cast
      rw [show -((n : ℤ) + 1) = -n - 1 by ring]
      linarith
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact (hpos n).1
  · exact (hneg n).1

/-- Cassini's identity `u_{m+1}² - u_m u_{m+2} = 1`. -/
lemma u_cassini (g m : ℤ) : u g (m + 1) ^ 2 - u g m * u g (m + 2) = 1 := by
  -- the defect is constant in `m`, and it is `1` at `m = 0`
  have step : ∀ k : ℤ, u g (k + 2) ^ 2 - u g (k + 1) * u g (k + 3) =
      u g (k + 1) ^ 2 - u g k * u g (k + 2) := by
    intro k
    have h1 := u_add_one g (k + 2)
    have h2 := u_add_one g (k + 1)
    rw [show k + 2 + 1 = k + 3 by ring, show k + 2 - 1 = k + 1 by ring] at h1
    rw [show k + 1 + 1 = k + 2 by ring, show k + 1 - 1 = k by ring] at h2
    rw [h1]
    linear_combination (u g (k + 2)) * h2
  let F : ℤ → ℤ := fun k => u g (k + 1) ^ 2 - u g k * u g (k + 2) - 1
  have hF : ∀ k, F (k + 1) = F k := by
    intro k; simp only [F]
    rw [show k + 1 + 1 = k + 2 by ring, show k + 1 + 2 = k + 3 by ring, step]
  have hF0 : F 0 = 0 := by simp [F]
  -- a sequence with `F (k + 1) = F k` and `F 0 = 0` vanishes
  have key : ∀ k, F k = 0 := by
    refine eq_zero_of_rec (g := 2) (fun k => ?_) hF0 (by rw [show (1 : ℤ) = 0 + 1 by ring, hF, hF0])
    rw [hF k, show F k = F (k - 1 + 1) by ring_nf, hF (k - 1)]; ring
  have := key m
  simp only [F] at this
  linarith

/-! ### Positive real roots -/

/-- The quadratic form `q(a, b) = a² + b² - gab` of the `g`-Kronecker quiver. A dimension vector
with `q = 1` is a real root; a rigid wall object of multiplicities `(a, b)` has
`dim End = q(a, b)`. -/
def kroneckerForm (g a b : ℤ) : ℤ := a ^ 2 + b ^ 2 - g * a * b

/-- `R_m = (u_{m+1}, u_m)` is a real root for every integer `m`. -/
lemma kroneckerForm_R (g m : ℤ) : kroneckerForm g (u g (m + 1)) (u g m) = 1 := by
  have h := u_cassini g m
  have hr := u_add_one g (m + 1)
  rw [show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring] at hr
  unfold kroneckerForm
  rw [hr] at h
  linear_combination h

lemma kroneckerForm_comm (g a b : ℤ) : kroneckerForm g a b = kroneckerForm g b a := by
  unfold kroneckerForm; ring

/-- For `g ≥ 2`, `u_m ≥ 0` and `u_{m+1} - u_m ≥ 1` at nonnegative indices. -/
lemma u_nonneg_and_step {g : ℤ} (hg : 2 ≤ g) (n : ℕ) :
    0 ≤ u g n ∧ 1 ≤ u g (n + 1) - u g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    push_cast
    refine ⟨by linarith, ?_⟩
    have hr := u_add_one g ((n : ℤ) + 1)
    rw [show (n : ℤ) + 1 + 1 = n + 2 by ring, show (n : ℤ) + 1 - 1 = n by ring] at hr
    rw [show (n : ℤ) + 1 + 1 = n + 2 by ring, hr]
    nlinarith

/-- For `g ≥ 2` the differences of `u` are at least one at **every** integer index; at negative
indices this is `u_{-j} = -u_j`. -/
lemma one_le_u_succ_sub {g : ℤ} (hg : 2 ≤ g) (k : ℤ) : 1 ≤ u g (k + 1) - u g k := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact (u_nonneg_and_step hg n).2
  · rcases n with _ | n
    · simp
    · have := (u_nonneg_and_step hg n).2
      have e1 : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
      rw [e1, u_neg, u_neg]
      push_cast at this ⊢
      linarith

lemma u_strictMono_nat {g : ℤ} (hg : 2 ≤ g) {m n : ℕ} (h : m < n) : u g m < u g n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hs := (u_nonneg_and_step hg n).2
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · push_cast; linarith [ih h]
    · subst h; push_cast; linarith

/-- **The positive real roots.** For `g ≥ 2`, a pair of nonnegative integers solves
`a² + b² - gab = 1` exactly when it is `R_m = (u_{m+1}, u_m)` or `L_m = (u_m, u_{m+1})` for some
`m ≥ 0`. (The proof reflects the larger coordinate, `a ↦ gb - a = (b² - 1)/a < b`, until a
simple root is reached.) -/
theorem realRoot_classification {g : ℤ} (hg : 2 ≤ g) {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    kroneckerForm g a b = 1 ↔
      ∃ m : ℕ, (a = u g (m + 1) ∧ b = u g m) ∨ (a = u g m ∧ b = u g (m + 1)) := by
  constructor
  · intro h
    -- strong induction on `a + b`
    induction hn : (a + b).toNat using Nat.strong_induction_on generalizing a b with
    | _ n ih =>
      unfold kroneckerForm at h
      rcases eq_or_lt_of_le hb with hb0 | hbpos
      · -- `b = 0`, so `a = 1`
        subst hb0
        have : a = 1 := by nlinarith
        exact ⟨0, Or.inl ⟨by simpa using this, by simp⟩⟩
      rcases eq_or_lt_of_le ha with ha0 | hapos
      · subst ha0
        have : b = 1 := by nlinarith
        exact ⟨0, Or.inr ⟨by simp, by simpa using this⟩⟩
      -- both positive; they differ
      have hne : a ≠ b := by
        rintro rfl
        nlinarith
      rcases lt_or_gt_of_ne hne with hab | hab
      · -- `a < b`: reflect `b ↦ g a - b`
        set b' := g * a - b with hb'
        have hprod : b * b' = a ^ 2 - 1 := by rw [hb']; nlinarith
        have hb'0 : 0 ≤ b' := by
          by_contra hneg
          push Not at hneg
          nlinarith
        have hb'a : b' < a := by nlinarith
        have hroot : kroneckerForm g a b' = 1 := by unfold kroneckerForm; rw [hb']; nlinarith
        have hlt : (a + b').toNat < n := by rw [← hn]; omega
        obtain ⟨m, hm⟩ := ih _ hlt ha hb'0 hroot rfl
        rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine ⟨m + 1, Or.inr ⟨by push_cast; exact h1, ?_⟩⟩
          have hr := u_add_one g ((m : ℤ) + 1)
          rw [show (m : ℤ) + 1 - 1 = m by ring] at hr
          push_cast
          rw [hr, ← h1, ← h2, hb']; ring
        · -- `(a, b') = L_m` would give `a < b'`
          exfalso
          have := u_strictMono_nat hg (Nat.lt_succ_self m)
          push_cast at this
          rw [← h1, ← h2] at this
          linarith
      · -- `a > b`: reflect `a ↦ g b - a`
        set a' := g * b - a with ha'
        have hprod : a * a' = b ^ 2 - 1 := by rw [ha']; nlinarith
        have ha'0 : 0 ≤ a' := by
          by_contra hneg
          push Not at hneg
          nlinarith
        have ha'b : a' < b := by nlinarith
        have hroot : kroneckerForm g b a' = 1 := by unfold kroneckerForm; rw [ha']; nlinarith
        have hlt : (b + a').toNat < n := by rw [← hn]; omega
        obtain ⟨m, hm⟩ := ih _ hlt hb ha'0 hroot rfl
        rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine ⟨m + 1, Or.inl ⟨?_, by push_cast; exact h1⟩⟩
          have hr := u_add_one g ((m : ℤ) + 1)
          rw [show (m : ℤ) + 1 - 1 = m by ring] at hr
          push_cast
          rw [hr, ← h1, ← h2, ha']; ring
        · exfalso
          have := u_strictMono_nat hg (Nat.lt_succ_self m)
          push_cast at this
          rw [← h1, ← h2] at this
          linarith
  · rintro ⟨m, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact_mod_cast kroneckerForm_R g m
    · rw [kroneckerForm_comm]; exact_mod_cast kroneckerForm_R g m

/-! ### The determinant identities -/

/-- The determinant `[v, w] = v₁w₂ - v₂w₁` of two dimension vectors. -/
def det2 (v w : ℤ × ℤ) : ℤ := v.1 * w.2 - v.2 * w.1

lemma det2_sub_right (v w w' : ℤ × ℤ) : det2 v (w - w') = det2 v w - det2 v w' := by
  simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring

/-- The root `R_m = (u_{m+1}, u_m)`, defined for every integer `m`. -/
noncomputable def R (g m : ℤ) : ℤ × ℤ := (u g (m + 1), u g m)

/-- **The exact determinant identity** `[R_m, R_j] = u_{j-m}`. -/
theorem det_R (g m j : ℤ) : det2 (R g m) (R g j) = u g (j - m) := by
  -- both sides satisfy the recursion in `j` and agree at `j = m`, `j = m + 1`
  let F : ℤ → ℤ := fun k => det2 (R g m) (R g (m + k)) - u g k
  have hrec : ∀ k, F (k + 1) = g * F k - F (k - 1) := by
    intro k
    simp only [F, det2, R]
    have e1 := u_add_one g (m + k + 1)
    have e2 := u_add_one g k
    rw [show m + (k + 1) + 1 = m + k + 1 + 1 by ring, show m + (k + 1) = m + k + 1 by ring,
      show m + (k - 1) + 1 = m + k by ring, show m + (k - 1) = m + k - 1 by ring]
    have e3 := u_add_one g (m + k)
    rw [show m + k + 1 - 1 = m + k by ring] at e1
    rw [e1, e3, e2]; ring
  have h0 : F 0 = 0 := by simp [F, det2, R]; ring
  have h1 : F 1 = 0 := by
    simp only [F, det2, R, u_one]
    have hc := u_cassini g m
    have hr := u_add_one g (m + 1)
    rw [show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring] at hr
    rw [hr] at hc
    rw [show m + 1 + 1 = m + 2 by ring, hr]
    linear_combination hc
  have := eq_zero_of_rec hrec h0 h1 (j - m)
  simp only [F, show m + (j - m) = j by ring] at this
  linarith

/-- `[R_m, R_{j+1} - R_j] = u_{j-m+1} - u_{j-m}`. -/
theorem det_R_sub (g m j : ℤ) :
    det2 (R g m) (R g (j + 1) - R g j) = u g (j - m + 1) - u g (j - m) := by
  rw [det2_sub_right, det_R, det_R, show j + 1 - m = j - m + 1 by ring]

/-- **Every ray-difference minor is at least one**: `[R_m, R_{j+1} - R_j] ≥ 1` for all integers
`m, j` when `g ≥ 2`. This orders any finite string of roots by integer comparisons alone. -/
theorem det_R_sub_ge_one {g : ℤ} (hg : 2 ≤ g) (m j : ℤ) :
    1 ≤ det2 (R g m) (R g (j + 1) - R g j) := by
  rw [det_R_sub]; exact one_le_u_succ_sub hg _

/-- Adjacent roots have minor one: `[R_m, R_{m+1}] = 1`. -/
lemma det_R_succ (g m : ℤ) : det2 (R g m) (R g (m + 1)) = 1 := by
  rw [det_R, show m + 1 - m = 1 by ring, u_one]

/-! ### Fans with adjacent minors one -/

/-- A chain `D₀ = 0`, `D₁ = 1`, `D_{k+2} = c_k D_{k+1} - D_k` with all `c_k ≥ 2` has `D_k ≥ 0`
and increasing differences `D_{k+1} - D_k ≥ 1`:
`D_{k+2} - D_{k+1} = (D_{k+1} - D_k) + (c_k - 2) D_{k+1}`. -/
lemma chain_bound {c : ℕ → ℤ} (hc : ∀ k, 2 ≤ c k) {D : ℕ → ℤ} (h0 : D 0 = 0) (h1 : D 1 = 1)
    (hrec : ∀ k, D (k + 2) = c k * D (k + 1) - D k) (k : ℕ) :
    0 ≤ D k ∧ 1 ≤ D (k + 1) - D k := by
  induction k with
  | zero => simp [h0, h1]
  | succ k ih =>
    refine ⟨by linarith [ih.1, ih.2], ?_⟩
    rw [hrec k]
    nlinarith [hc k, ih.1, ih.2]

/-- **Fans of spherical walls.** Let `v_j` (`j ≥ 0`) be dimension vectors with
`v_{j+2} = g_{j+1} v_{j+1} - v_j`, all `g_j ≥ 2`, and `[v_m, v_{m+1}] = 1`. Then every
ray-difference minor to the right of `m` is at least one: `[v_m, v_{j+1} - v_j] ≥ 1` for
`j ≥ m`. -/
theorem fan_minor_ge_one {g : ℕ → ℤ} (hg : ∀ j, 2 ≤ g j) {v : ℕ → ℤ × ℤ}
    (hrec : ∀ j, v (j + 2) = g (j + 1) • v (j + 1) - v j) {m : ℕ}
    (hadj : det2 (v m) (v (m + 1)) = 1) {j : ℕ} (hj : m ≤ j) :
    1 ≤ det2 (v m) (v (j + 1) - v j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  let D : ℕ → ℤ := fun i => det2 (v m) (v (m + i))
  have h0 : D 0 = 0 := by simp only [D, add_zero, det2]; ring
  have hD : ∀ i, D (i + 2) = g (m + i + 1) * D (i + 1) - D i := by
    intro i
    simp only [D, show m + (i + 2) = (m + i) + 2 by ring, hrec, det2, Prod.fst_sub,
      Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      show m + i + 1 = m + (i + 1) by ring]
    ring
  have := (chain_bound (c := fun i => g (m + i + 1)) (fun i => hg _) h0 hadj hD k).2
  simpa [D, det2_sub_right, add_assoc] using this

/-- To the left the same holds: `[v_m, v_{j+1} - v_j] ≥ 1` for `j < m`, given
`[v_{m-1}, v_m] = 1`. -/
theorem fan_minor_ge_one_left {g : ℕ → ℤ} (hg : ∀ j, 2 ≤ g j) {v : ℕ → ℤ × ℤ}
    (hrec : ∀ j, v (j + 2) = g (j + 1) • v (j + 1) - v j) {m j : ℕ} (hj : j + 1 ≤ m)
    (hadj' : det2 (v (m - 1)) (v m) = 1) :
    1 ≤ det2 (v m) (v (j + 1) - v j) := by
  -- `E_i = -[v_m, v_{m-i}]` is a chain read leftwards
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
  let E : ℕ → ℤ := fun i => if i ≤ m then -det2 (v m) (v (m - i)) else 0
  have hE0 : E 0 = 0 := by simp [E, det2]; ring
  have hE1 : E 1 = 1 := by
    have hm : 1 ≤ m := by omega
    simp only [E, hm, ↓reduceIte]
    simp only [det2] at hadj' ⊢
    linarith
  -- we only need the chain up to index `m`; extend the recursion by a dummy beyond it
  have hrecE : ∀ i, i + 2 ≤ m → E (i + 2) = g (m - (i + 1)) * E (i + 1) - E i := by
    intro i hi
    have hv := hrec (m - (i + 2))
    rw [show m - (i + 2) + 2 = m - i by omega, show m - (i + 2) + 1 = m - (i + 1) by omega] at hv
    simp only [E, show i + 2 ≤ m from hi, show i + 1 ≤ m by omega, show i ≤ m by omega,
      ↓reduceIte]
    have hvi : v (m - (i + 2)) = g (m - (i + 1)) • v (m - (i + 1)) - v (m - i) := by
      rw [hv]; abel
    rw [hvi]
    simp only [det2, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  -- the chain bound along `i ≤ m`
  have bound : ∀ i, i + 1 ≤ m → 0 ≤ E i ∧ 1 ≤ E (i + 1) - E i := by
    intro i
    induction i with
    | zero => intro _; simp [hE0, hE1]
    | succ i ih =>
      intro hi
      obtain ⟨h0', h1'⟩ := ih (by omega)
      refine ⟨by linarith, ?_⟩
      rw [hrecE i hi]
      nlinarith [hg (m - (i + 1))]
  -- `j + 1 = m - k`, so the minor is `E k - E (k + 1)`... read off at `i = k`
  have hjk : j = m - k - 1 := by omega
  have hb := (bound k (by omega)).2
  simp only [E, show k + 1 ≤ m by omega, show k ≤ m by omega, ↓reduceIte] at hb
  rw [hjk, show m - k - 1 + 1 = m - k by omega, det2_sub_right]
  rw [show m - (k + 1) = m - k - 1 by omega] at hb
  linarith

/-! ### No isotropic class in the span of two spherical classes -/

/-- For `|g| ≥ 3`, `g² - 4` is not a perfect square: it lies strictly between `(|g| - 1)²`
and `g²`. -/
lemma not_isSquare_sq_sub_four {g : ℤ} (hg : 3 ≤ |g|) : ¬ IsSquare (g ^ 2 - 4) := by
  rintro ⟨k, hk⟩
  have hk' : |k| ^ 2 = |g| ^ 2 - 4 := by rw [sq_abs, sq_abs]; linarith [hk]
  have h1 : |k| < |g| := by nlinarith [abs_nonneg k, abs_nonneg g]
  have h2 : |g| - 1 < |k| := by nlinarith [abs_nonneg k, abs_nonneg g]
  omega

/-- **No isotropic vector in a rational span of two spherical classes.** If two spherical
classes pair to `±g` with `|g| ≥ 3`, a rational combination `x s₀ + y s₁` has square
`-2(x² ∓ gxy + y²)`; this vanishes only for `x = y = 0`. The proof is the rank-two wall
criterion `Matrix.isSquare_neg_det_of_isotropic`: `(x, y)` would be isotropic for the wall matrix
`[[2, g], [g, 2]]`, whose negated determinant `g² - 4` is not a square. -/
theorem no_null_vector {g : ℤ} (hg : 3 ≤ |g|) {x y : ℚ} (h : x ^ 2 + g * x * y + y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  by_contra hxy
  have hne : ![x, y] ≠ 0 := fun h0 =>
    hxy ⟨by simpa using congrFun h0 0, by simpa using congrFun h0 1⟩
  have hsymm : (!![2, (g : ℚ); g, 2]).IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hiso : ![x, y] ⬝ᵥ Matrix.mulVec !![2, (g : ℚ); g, 2] ![x, y] = 0 := by
    rw [Matrix.dotProduct_mulVec_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination 2 * h
  have hsq := Matrix.isSquare_neg_det_of_isotropic hsymm hne hiso
  rw [Matrix.det_fin_two_of] at hsq
  apply not_isSquare_sq_sub_four hg
  rw [← Rat.isSquare_intCast_iff]
  convert hsq using 1
  push_cast
  ring

end Quiver.Kronecker
