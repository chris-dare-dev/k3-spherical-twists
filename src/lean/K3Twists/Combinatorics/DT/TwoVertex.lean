/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.DT.FramedMultiplier

/-!
# Coefficients of the framed multiplier of a two-vertex quiver

On two vertices the exponent vectors are the pairs `(a, b)`, written `mk2 a b`. Multiplying a
power series by `1 - x^{(u, v)}` or by its inverse acts on its table of coefficients
`(a, b) ↦ [x^{(a, b)}] f` by an explicit recursion (`table_mul_one_sub`, `table_mul_inv_unitX`).
So the coefficient of the framed multiplier at `(a, b)` is the value at `(a, b)` of a computable
function of the exponents on the box below `(a, b)` (`coeff_S_mk2`), and a closed term can be
evaluated by `decide`. This is how the coefficient `8` at `(2, 2)` of the affine Kronecker
multiplier is computed (`K3Twists/Combinatorics/DT/Quivers.lean`).

## Main results

* `coeff_mul_inv_unitX`: for any `σ`, `[x^d](f (1 - x^α)⁻¹) = Σ_{k < N} [x^{d - kα}] f`, the sum
  over the `k` with `kα ≤ d`, once `Nα ≰ d`;
* `table_mul_factor`: the action of one factor `(1 - x^α)^{e_α}` on tables;
* `coeff_S_mk2`: the coefficient of `S_e` at `(a, b)` is `Table.boxModel ε a b a b`, where `ε` gives
  the exponents on pairs.
-/

open Finset

namespace MvPowerSeries.FramedMultiplier

/-! ### Inverting one factor, for any set of vertices -/

section Geometric

variable {σ R : Type*} [CommRing R]

/-- `[x^d](f (1 - x^α)⁻¹) = Σ_{k < N, kα ≤ d} [x^{d - kα}] f` as soon as `Nα ≰ d`. -/
theorem coeff_mul_inv_unitX (f : MvPowerSeries σ R) (α : Pos σ) (d : σ →₀ ℕ) {N : ℕ}
    (hN : ¬N • α.1 ≤ d) :
    coeff d (f * (↑(unitX (R := R) α)⁻¹ : MvPowerSeries σ R)) =
      ∑ k ∈ range N, if k • α.1 ≤ d then coeff (d - k • α.1) f else 0 := by
  classical
  set g : MvPowerSeries σ R := f * (↑(unitX (R := R) α)⁻¹ : MvPowerSeries σ R) with hg
  -- `g = f + g x^α`
  have hrec : ∀ d', coeff d' g = coeff d' f + if α.1 ≤ d' then coeff (d' - α.1) g else 0 := by
    intro d'
    have h1 : g * (1 - monomial α.1 1) = f := by
      rw [hg, ← unitX_val (R := R), mul_assoc, Units.inv_mul, mul_one]
    have h2 : coeff d' f = coeff d' g - coeff d' (g * monomial α.1 1) := by
      rw [← h1, mul_sub, mul_one, map_sub]
    rw [h2, coeff_mul_monomial]
    split_ifs <;> simp
  -- unfold the recursion `n` times
  have key : ∀ n : ℕ, coeff d g = (∑ k ∈ range n, if k • α.1 ≤ d then coeff (d - k • α.1) f
      else 0) + if n • α.1 ≤ d then coeff (d - n • α.1) g else 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, sum_range_succ, add_assoc]
      congr 1
      by_cases hn : n • α.1 ≤ d
      · rw [hrec, succ_nsmul]
        by_cases h1 : α.1 ≤ d - n • α.1
        · have h2 : n • α.1 + α.1 ≤ d := (le_tsub_iff_left hn).1 h1
          simp only [hn, h1, h2, ↓reduceIte, tsub_tsub]
        · have h2 : ¬n • α.1 + α.1 ≤ d := fun h => h1 (le_tsub_of_add_le_left h)
          simp only [hn, h1, h2, ↓reduceIte]
      · have h2 : ¬(n + 1) • α.1 ≤ d := fun h =>
          hn (le_trans (nsmul_le_nsmul_left (by simp) (Nat.le_succ n)) h)
        simp only [hn, h2, ↓reduceIte, add_zero]
  rw [key N]
  simp only [hN, ↓reduceIte, add_zero]

end Geometric

/-! ### Two vertices -/

section TwoVertex

variable {R : Type*} [CommRing R]

/-- The exponent vector `(a, b)` on two vertices. -/
noncomputable def mk2 (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp]
theorem mk2_apply_zero (a b : ℕ) : mk2 a b 0 = a := by
  simp [mk2]

@[simp]
theorem mk2_apply_one (a b : ℕ) : mk2 a b 1 = b := by
  simp [mk2]

theorem mk2_ext {d d' : Fin 2 →₀ ℕ} (h0 : d 0 = d' 0) (h1 : d 1 = d' 1) : d = d' := by
  ext i
  fin_cases i <;> assumption

theorem eq_mk2 (d : Fin 2 →₀ ℕ) : d = mk2 (d 0) (d 1) :=
  mk2_ext (by simp) (by simp)

theorem mk2_le_mk2 {a b c d : ℕ} : mk2 a b ≤ mk2 c d ↔ a ≤ c ∧ b ≤ d := by
  refine ⟨fun h => ⟨by simpa using h 0, by simpa using h 1⟩, fun h i => ?_⟩
  fin_cases i
  · simpa using h.1
  · simpa using h.2

theorem mk2_sub_mk2 (a b c d : ℕ) : mk2 c d - mk2 a b = mk2 (c - a) (d - b) :=
  mk2_ext (by simp) (by simp)

theorem mk2_eq_zero_iff {a b : ℕ} : mk2 a b = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h => ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h⟩, ?_⟩
  rintro ⟨rfl, rfl⟩
  exact mk2_ext (by simp) (by simp)

theorem nsmul_mk2 (k u v : ℕ) : k • mk2 u v = mk2 (k * u) (k * v) :=
  mk2_ext (by simp) (by simp)

theorem pair_mk2 (p : Fin 2 → ℤ) (a b : ℕ) : pair p (mk2 a b) = p 0 * a + p 1 * b := by
  rw [mk2, pair_add_right, pair_single, pair_single]

/-- A table of coefficients on two vertices. -/
abbrev Table (R : Type*) := ℕ → ℕ → R

/-- The coefficient table `(a, b) ↦ [x^{(a, b)}] f`. -/
noncomputable def table (f : MvPowerSeries (Fin 2) R) : Table R := fun a b => coeff (mk2 a b) f

namespace Table

/-- The table of `1`. -/
def one : Table R := fun a b => if a = 0 ∧ b = 0 then 1 else 0

/-- Multiplication by `1 - x^{(u, v)}`. -/
def mulOneSub (u v : ℕ) (F : Table R) : Table R :=
  fun a b => F a b - if u ≤ a ∧ v ≤ b then F (a - u) (b - v) else 0

/-- Multiplication by `(1 - x^{(u, v)})⁻¹`, for `(u, v) ≠ (0, 0)`. -/
def divOneSub (u v : ℕ) (F : Table R) : Table R :=
  fun a b => ((List.range (a + b + 1)).map fun k =>
    if k * u ≤ a ∧ k * v ≤ b then F (a - k * u) (b - k * v) else 0).sum

/-- Multiplication by `(1 - x^{(u, v)})^n` for an integer `n`. -/
def mulFactor (u v : ℕ) : ℤ → Table R → Table R
  | .ofNat n => (mulOneSub u v)^[n]
  | .negSucc n => (divOneSub u v)^[n + 1]

/-- The table of the product of all factors `(1 - x^{(u, v)})^{ε(u, v)}` with `u ≤ a`, `v ≤ b`
and `(u, v) ≠ (0, 0)`. -/
def boxModel (ε : ℕ → ℕ → ℤ) (a b : ℕ) : Table R :=
  (List.range (a + 1)).foldr (fun u T => (List.range (b + 1)).foldr
    (fun v T' => mulFactor u v (if u = 0 ∧ v = 0 then 0 else ε u v) T') T) one

end Table

theorem table_one : table (1 : MvPowerSeries (Fin 2) R) = Table.one := by
  classical
  funext a b
  simp [table, Table.one, coeff_one, mk2_eq_zero_iff]

theorem table_mul_one_sub (f : MvPowerSeries (Fin 2) R) (u v : ℕ) :
    table (f * (1 - monomial (mk2 u v) 1)) = Table.mulOneSub u v (table f) := by
  funext a b
  simp only [table, Table.mulOneSub, mul_sub, mul_one, map_sub, coeff_mul_monomial, mk2_le_mk2,
    mk2_sub_mk2]

theorem sum_range_eq_list_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ range n, f k = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem prod_range_eq_list_prod {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ k ∈ range n, f k = ((List.range n).map f).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, List.range_succ, List.map_append, List.prod_append]; simp

theorem table_mul_inv_unitX (f : MvPowerSeries (Fin 2) R) {u v : ℕ} (α : Pos (Fin 2))
    (hα : α.1 = mk2 u v) :
    table (f * (↑(unitX (R := R) α)⁻¹ : MvPowerSeries (Fin 2) R)) =
      Table.divOneSub u v (table f) := by
  funext a b
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    exact α.2 (by rw [hα, h.1, h.2]; exact mk2_eq_zero_iff.2 ⟨rfl, rfl⟩)
  have hN : ¬(a + b + 1) • α.1 ≤ mk2 a b := by
    rw [hα, nsmul_mk2, mk2_le_mk2]
    rintro ⟨h1, h2⟩
    rcases huv with h | h
    · have : a + b + 1 ≤ (a + b + 1) * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h)
      omega
    · have : a + b + 1 ≤ (a + b + 1) * v := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h)
      omega
  rw [table, coeff_mul_inv_unitX f α (mk2 a b) hN, Table.divOneSub, ← sum_range_eq_list_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [hα, nsmul_mk2, mk2_le_mk2, mk2_sub_mk2, table]

/-- The action of one factor `(1 - x^α)^{e_α}`, `α = (u, v)`, on tables. -/
theorem table_mul_factor (f : MvPowerSeries (Fin 2) R) (e : (Fin 2 →₀ ℕ) → ℤ) {u v : ℕ}
    (α : Pos (Fin 2)) (hα : α.1 = mk2 u v) :
    table (f * factor e α) = Table.mulFactor u v (e α.1) (table f) := by
  rw [factor]
  generalize e α.1 = n
  cases n with
  | ofNat n =>
    induction n generalizing f with
    | zero => simp [Table.mulFactor]
    | succ n ih =>
      have : ((unitX (R := R) α ^ (Int.ofNat (n + 1)) : (MvPowerSeries (Fin 2) R)ˣ) :
          MvPowerSeries (Fin 2) R) =
          (↑(unitX (R := R) α ^ (Int.ofNat n)) : MvPowerSeries (Fin 2) R) *
            (1 - monomial (mk2 u v) (1 : R)) := by
        rw [← hα, ← unitX_val (R := R), ← Units.val_mul, ← zpow_add_one]
        rfl
      rw [this, ← mul_assoc, table_mul_one_sub, ih]
      simp only [Table.mulFactor, Function.iterate_succ_apply']
  | negSucc n =>
    induction n generalizing f with
    | zero => simp [Table.mulFactor, table_mul_inv_unitX f α hα]
    | succ n ih =>
      have : ((unitX (R := R) α ^ (Int.negSucc (n + 1)) : (MvPowerSeries (Fin 2) R)ˣ) :
          MvPowerSeries (Fin 2) R) =
          (↑(unitX (R := R) α ^ (Int.negSucc n)) : MvPowerSeries (Fin 2) R) *
            (↑(unitX (R := R) α)⁻¹ : MvPowerSeries (Fin 2) R) := by
        rw [← Units.val_mul, ← zpow_sub_one]
        rfl
      rw [this, ← mul_assoc, table_mul_inv_unitX _ α hα, ih]
      simp only [Table.mulFactor, Function.iterate_succ_apply']

/-- The coefficient table of `f` times a list product, by folding the actions of the factors. -/
theorem table_mul_list_prod {ι : Type*} (L : List ι) (G : ι → MvPowerSeries (Fin 2) R)
    (op : ι → Table R → Table R) (hop : ∀ c g, table (g * G c) = op c (table g))
    (f : MvPowerSeries (Fin 2) R) :
    table (f * (L.map G).prod) = L.foldr op (table f) := by
  induction L generalizing f with
  | nil => simp
  | cons c L ih =>
    have h : f * (G c * (L.map G).prod) = f * (L.map G).prod * G c := by ring
    rw [List.map_cons, List.prod_cons, List.foldr_cons, h, hop, ih]

/-- **Coefficients of the multiplier on two vertices.** If `ε` gives the exponents on pairs,
`e (u, v) = ε u v`, the coefficient of `S_e` at `(a, b)` is the value at `(a, b)` of the
computable table `Table.boxModel ε a b`. -/
theorem coeff_S_mk2 (e : (Fin 2 →₀ ℕ) → ℤ) (ε : ℕ → ℕ → ℤ) (he : ∀ u v, e (mk2 u v) = ε u v)
    (a b : ℕ) : coeff (mk2 a b) (S (R := R) e) = Table.boxModel ε a b a b := by
  classical
  -- the factor of the pair `(u, v)`, `1` at `(0, 0)`
  let F : ℕ → ℕ → MvPowerSeries (Fin 2) R := fun u v =>
    if h : mk2 u v = 0 then 1 else factor e ⟨mk2 u v, h⟩
  have hF : ∀ u v g, table (g * F u v) =
      Table.mulFactor u v (if u = 0 ∧ v = 0 then 0 else ε u v) (table g) := by
    intro u v g
    by_cases h : mk2 u v = 0
    · obtain ⟨rfl, rfl⟩ := mk2_eq_zero_iff.1 h
      simp [F, Table.mulFactor, h]
    · have h' : ¬(u = 0 ∧ v = 0) := fun h' => h (mk2_eq_zero_iff.2 h')
      simp only [F, h, dite_false, h', ↓reduceIte]
      rw [table_mul_factor g e ⟨mk2 u v, h⟩ rfl, he]
  -- the box product as a double product over pairs
  have hbox : ∏ α ∈ box (mk2 a b), factor (R := R) e α =
      ∏ u ∈ range (a + 1), ∏ v ∈ range (b + 1), F u v := by
    rw [← prod_product']
    refine prod_bij_ne_one (fun α _ _ => (α.1 0, α.1 1)) ?_ ?_ ?_ ?_
    · intro α hα _
      have := mem_box.1 hα
      rw [eq_mk2 α.1, mk2_le_mk2] at this
      simp only [mem_product, mem_range]
      omega
    · intro α _ _ β _ _ h
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (mk2_ext h.1 h.2)
    · rintro ⟨u, v⟩ huv hne
      have h : mk2 u v ≠ 0 := fun h => hne (by simp [F, h])
      refine ⟨⟨mk2 u v, h⟩, ?_, ?_, by simp⟩
      · simp only [mem_product, mem_range] at huv
        exact mem_box.2 (mk2_le_mk2.2 ⟨by omega, by omega⟩)
      · simpa [F, h] using hne
    · intro α _ _
      have h : mk2 (α.1 0) (α.1 1) ≠ 0 := by rw [← eq_mk2]; exact α.2
      simp only [F, h, dite_false]
      congr 1
      exact Subtype.ext (eq_mk2 α.1)
  have hcoeff := S_coeffEqOn_prod (R := R) e (mk2 a b) (box (mk2 a b)) subset_rfl (mk2 a b)
    (Set.mem_Iic.2 le_rfl)
  rw [hcoeff, hbox, prod_range_eq_list_prod]
  simp_rw [prod_range_eq_list_prod]
  have := table_mul_list_prod (List.range (a + 1))
    (fun u => ((List.range (b + 1)).map (F u)).prod)
    (fun u T => (List.range (b + 1)).foldr
      (fun v T' => Table.mulFactor u v (if u = 0 ∧ v = 0 then 0 else ε u v) T') T)
    (fun u g => table_mul_list_prod _ _ _ (fun v g' => hF u v g') g) 1
  rw [one_mul, table_one] at this
  exact congrFun (congrFun this a) b

end TwoVertex

end MvPowerSeries.FramedMultiplier
