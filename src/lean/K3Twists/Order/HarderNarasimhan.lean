/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Harder–Narasimhan filtrations in a lattice with a slope function

Let `L` be a bounded lattice and `K` a linearly ordered field. A *slope function* on `L` is a
rank `rk` and a degree `deg : L → K`, both valuations,

  `f (x ⊔ y) + f (x ⊓ y) = f x + f y`,

with `rk` strictly monotone. The slope of an interval `x < y` is
`(deg y - deg x) / (rk y - rk x)`, and the *weight* of slope `θ` is `w_θ x = deg x - θ rk x`, so
that `w_θ y - w_θ x = (rk y - rk x) (slope - θ)`.

The subobjects of an object of a finite-length abelian category with a central charge `Z` in the
upper half-plane form such a lattice, with `rk = Im Z` and `deg = -Re Z`: the phase order of
nonzero subquotients is the slope order. So do the subrepresentations of a quiver
representation, with `rk` and `deg` linear in the dimension vector.

An interval `[x, y]` is *semistable* if no `z` with `x < z ≤ y` has a larger slope from `x`. A
*Harder–Narasimhan filtration* is a chain `⊥ = c₀ < c₁ < ⋯ < cₙ = ⊤` whose factors
`[cᵢ, cᵢ₊₁]` are semistable with strictly decreasing slopes `μ₀ > μ₁ > ⋯ > μₙ₋₁`.

## Main results

* `HNFiltration.weight_le`: if every factor below `c_k` has slope at least `θ` and every factor
  above it has slope at most `θ`, then `c_k` maximizes `w_θ` over all of `L`;
* `HNFiltration.eq_of_weight_eq`: with strict inequalities, `c_k` is the only maximizer. So the
  prefixes of an HN filtration are intrinsic (`HNFiltration.mem_range_chain_iff`), and an HN
  filtration is unique (`HNFiltration.instSubsingleton`);
* `HNFiltration.weight_le_edge`, `HNFiltration.convexHull_subset`: every point `(rk x, deg x)`
  lies on or below every edge line of the polygon through the points `(rk cᵢ, deg cᵢ)`, so the
  HN filtration reads the upper boundary of the convex hull of the points; the HN filtration of
  the opposite slope function `s.neg`, with degree `-deg`, reads the lower boundary
  (`HNFiltration.weight_ge_edge_of_neg`).

This is the description of Harder–Narasimhan filtrations by the HN polytope of Baumann,
Kamnitzer and Tingley (arXiv:1110.3661, §3.2), in the generality of a lattice with valuations;
the proofs use only the valuation identities, not modularity of `L` (which they imply).

## Implementation notes

The chain is indexed by `Fin (n + 1)`, with the number of factors `n` part of the data: it has
exactly the entries `c₀, …, cₙ`, from `chain 0 = ⊥` to `chain (Fin.last n) = ⊤`, and the factor
`[cᵢ, cᵢ₊₁]` is indexed by `i : Fin n` through `Fin.castSucc` and `Fin.succ`. So a filtration has
no entries past its end, and filtrations of different lengths are terms of one type, which the
uniqueness statement compares. Proofs that induct on the index pass to the extension
`HNFiltration.c : ℕ → L`, constant `⊤` after `n`. Semistability is stated with weights, which
avoids division; `isSemistable_iff` gives the slope form.
-/

namespace Order

variable (L : Type*) [Lattice L] (K : Type*) [Field K] [LinearOrder K]

/-- A slope function on a lattice: a strictly monotone rank and a degree, both valuations. -/
structure SlopeFunction where
  /-- The rank, a strictly monotone valuation. -/
  rk : L → K
  /-- The degree, a valuation. -/
  deg : L → K
  rk_strictMono : StrictMono rk
  rk_sup_add_inf (x y : L) : rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y
  deg_sup_add_inf (x y : L) : deg (x ⊔ y) + deg (x ⊓ y) = deg x + deg y

namespace SlopeFunction

variable {L K} (s : SlopeFunction L K)

/-- The weight of slope `θ`, `w_θ x = deg x - θ rk x`. -/
def weight (θ : K) (x : L) : K := s.deg x - θ * s.rk x

/-- The slope `(deg y - deg x) / (rk y - rk x)` of the interval from `x` to `y`. -/
def slope (x y : L) : K := (s.deg y - s.deg x) / (s.rk y - s.rk x)

/-- The opposite slope function, with degree `-deg`: the slope order is reversed. -/
def neg : SlopeFunction L K where
  rk := s.rk
  deg x := -s.deg x
  rk_strictMono := s.rk_strictMono
  rk_sup_add_inf := s.rk_sup_add_inf
  deg_sup_add_inf x y := by linear_combination -s.deg_sup_add_inf x y

@[simp] lemma neg_rk : s.neg.rk = s.rk := rfl

@[simp] lemma neg_deg (x : L) : s.neg.deg x = -s.deg x := rfl

lemma neg_weight (θ : K) (x : L) : s.neg.weight θ x = -s.weight (-θ) x := by
  simp only [weight, neg_rk, neg_deg]
  ring

lemma weight_sup_add_inf (θ : K) (x y : L) :
    s.weight θ (x ⊔ y) + s.weight θ (x ⊓ y) = s.weight θ x + s.weight θ y := by
  simp only [weight]
  linear_combination s.deg_sup_add_inf x y - θ * s.rk_sup_add_inf x y

/-- The weight of the slope of `[x, y]` takes the same value at `x` and `y`. -/
lemma weight_slope_eq {x y : L} (h : x < y) :
    s.weight (s.slope x y) y = s.weight (s.slope x y) x := by
  have : s.rk y - s.rk x ≠ 0 := sub_ne_zero.mpr (s.rk_strictMono h).ne'
  simp only [weight, slope]
  field_simp
  ring

/-- `[x, y]` is semistable: `x < y`, and every `z` with `x ≤ z ≤ y` has `w_μ z ≤ w_μ x` for the
slope `μ` of `[x, y]`; that is, `slope x z ≤ μ` when `x < z` (`isSemistable_iff`). -/
def IsSemistable (x y : L) : Prop :=
  x < y ∧ ∀ z, x ≤ z → z ≤ y → s.weight (s.slope x y) z ≤ s.weight (s.slope x y) x

/-- `[x, y]` is stable: `x < y`, and every `z` with `x < z < y` has `w_μ z < w_μ x`, that is
`slope x z < slope x y`. -/
def IsStable (x y : L) : Prop :=
  x < y ∧ ∀ z, x < z → z < y → s.weight (s.slope x y) z < s.weight (s.slope x y) x

variable {s} in
lemma IsStable.isSemistable {x y : L} (h : s.IsStable x y) : s.IsSemistable x y := by
  refine ⟨h.1, fun z hxz hzy ↦ ?_⟩
  rcases hxz.eq_or_lt with rfl | hxz
  · exact le_rfl
  rcases hzy.eq_or_lt with rfl | hzy
  · exact (s.weight_slope_eq h.1).le
  · exact (h.2 z hxz hzy).le

/-- An interval with nothing strictly inside is stable. -/
lemma isStable_of_forall {x y : L} (h : x < y) (H : ∀ z, x < z → z < y → False) :
    s.IsStable x y :=
  ⟨h, fun z hxz hzy ↦ (H z hxz hzy).elim⟩

section OrderedField

variable [IsStrictOrderedRing K]

/-- `w_θ z ≤ w_θ x` for `x < z` means `slope x z ≤ θ`. -/
lemma weight_le_iff_slope_le {x z : L} (h : x < z) (θ : K) :
    s.weight θ z ≤ s.weight θ x ↔ s.slope x z ≤ θ := by
  have hpos : 0 < s.rk z - s.rk x := sub_pos.mpr (s.rk_strictMono h)
  rw [slope, div_le_iff₀ hpos, weight, weight]
  constructor <;> intro h' <;> linarith

/-- The slope form of semistability. -/
lemma isSemistable_iff {x y : L} (h : x < y) :
    s.IsSemistable x y ↔ ∀ z, x < z → z ≤ y → s.slope x z ≤ s.slope x y := by
  refine ⟨fun hs z hxz hzy ↦ (s.weight_le_iff_slope_le hxz _).mp (hs.2 z hxz.le hzy),
    fun H ↦ ⟨h, fun z hxz hzy ↦ ?_⟩⟩
  rcases hxz.eq_or_lt with rfl | hxz
  · exact le_rfl
  · exact (s.weight_le_iff_slope_le hxz _).mpr (H z hxz hzy)

/-- Division-free form of the weight inequality: for `x < y` with slope `μ`,
`w_μ z ≤ w_μ x` means `(deg z - deg x)(rk y - rk x) ≤ (deg y - deg x)(rk z - rk x)`. -/
lemma weight_slope_le_iff {x y : L} (h : x < y) (z : L) :
    s.weight (s.slope x y) z ≤ s.weight (s.slope x y) x ↔
      (s.deg z - s.deg x) * (s.rk y - s.rk x) ≤ (s.deg y - s.deg x) * (s.rk z - s.rk x) := by
  have hpos : 0 < s.rk y - s.rk x := sub_pos.mpr (s.rk_strictMono h)
  have key : (s.weight (s.slope x y) x - s.weight (s.slope x y) z) * (s.rk y - s.rk x) =
      (s.deg y - s.deg x) * (s.rk z - s.rk x) - (s.deg z - s.deg x) * (s.rk y - s.rk x) := by
    simp only [weight, slope]
    field_simp
    ring
  rw [← sub_nonneg, ← mul_nonneg_iff_of_pos_right hpos, key, sub_nonneg]

/-- The strict form of `weight_slope_le_iff`. -/
lemma weight_slope_lt_iff {x y : L} (h : x < y) (z : L) :
    s.weight (s.slope x y) z < s.weight (s.slope x y) x ↔
      (s.deg z - s.deg x) * (s.rk y - s.rk x) < (s.deg y - s.deg x) * (s.rk z - s.rk x) := by
  have hpos : 0 < s.rk y - s.rk x := sub_pos.mpr (s.rk_strictMono h)
  have key : (s.weight (s.slope x y) x - s.weight (s.slope x y) z) * (s.rk y - s.rk x) =
      (s.deg y - s.deg x) * (s.rk z - s.rk x) - (s.deg z - s.deg x) * (s.rk y - s.rk x) := by
    simp only [weight, slope]
    field_simp
    ring
  rw [← sub_pos, ← mul_pos_iff_of_pos_right hpos, key, sub_pos]

/-! ### Weights on a semistable interval -/

variable {s} {x y z : L} {θ : K}

/-- On a semistable `[x, y]` of slope at most `θ`, the bottom `x` maximizes `w_θ`. -/
lemma IsSemistable.weight_le_bot (h : s.IsSemistable x y) (hθ : s.slope x y ≤ θ) (hxz : x ≤ z)
    (hzy : z ≤ y) : s.weight θ z ≤ s.weight θ x := by
  have h1 := h.2 z hxz hzy
  have h2 : s.rk x ≤ s.rk z := s.rk_strictMono.monotone hxz
  simp only [weight] at h1 ⊢
  nlinarith

/-- On a semistable `[x, y]` of slope less than `θ`, the bottom `x` is the only maximizer
of `w_θ`. -/
lemma IsSemistable.eq_bot_of_weight_eq (h : s.IsSemistable x y) (hθ : s.slope x y < θ)
    (hxz : x ≤ z) (hzy : z ≤ y) (heq : s.weight θ z = s.weight θ x) : z = x := by
  by_contra hne
  have hlt := s.rk_strictMono (lt_of_le_of_ne hxz (Ne.symm hne))
  have h1 := h.2 z hxz hzy
  simp only [weight] at h1 heq
  nlinarith

/-- On a semistable `[x, y]` of slope at least `θ`, the top `y` maximizes `w_θ`. -/
lemma IsSemistable.weight_le_top (h : s.IsSemistable x y) (hθ : θ ≤ s.slope x y) (hxz : x ≤ z)
    (hzy : z ≤ y) : s.weight θ z ≤ s.weight θ y := by
  have h1 := h.2 z hxz hzy
  have h2 : s.rk z ≤ s.rk y := s.rk_strictMono.monotone hzy
  have h3 := s.weight_slope_eq h.1
  simp only [weight] at h1 h3 ⊢
  nlinarith

/-- On a semistable `[x, y]` of slope greater than `θ`, the top `y` is the only maximizer
of `w_θ`. -/
lemma IsSemistable.eq_top_of_weight_eq (h : s.IsSemistable x y) (hθ : θ < s.slope x y)
    (hxz : x ≤ z) (hzy : z ≤ y) (heq : s.weight θ z = s.weight θ y) : z = y := by
  by_contra hne
  have hlt := s.rk_strictMono (lt_of_le_of_ne hzy hne)
  have h1 := h.2 z hxz hzy
  have h3 := s.weight_slope_eq h.1
  simp only [weight] at h1 h3 heq
  nlinarith

/-! ### One step along a chain -/

variable {c d : L}

/-- If `c ≤ d` and `c` maximizes `w_θ` on `[c, d]`, then `w_θ (y ⊓ d) ≤ w_θ (y ⊓ c)`. -/
lemma weight_inf_le (hcd : c ≤ d) (H : ∀ z, c ≤ z → z ≤ d → s.weight θ z ≤ s.weight θ c)
    (y : L) : s.weight θ (y ⊓ d) ≤ s.weight θ (y ⊓ c) := by
  have h1 := s.weight_sup_add_inf θ (y ⊓ d) c
  have h2 : y ⊓ d ⊓ c = y ⊓ c := by rw [inf_assoc, inf_eq_right.mpr hcd]
  have h3 := H (y ⊓ d ⊔ c) le_sup_right (sup_le inf_le_right hcd)
  rw [h2] at h1
  linarith

/-- If `c ≤ d` and `c` is the only maximizer of `w_θ` on `[c, d]`, then
`w_θ (y ⊓ d) = w_θ (y ⊓ c)` forces `y ⊓ d = y ⊓ c`. -/
lemma inf_eq_of_weight_eq (hcd : c ≤ d)
    (H : ∀ z, c ≤ z → z ≤ d → s.weight θ z = s.weight θ c → z = c) {y : L}
    (heq : s.weight θ (y ⊓ d) = s.weight θ (y ⊓ c)) : y ⊓ d = y ⊓ c := by
  have h1 := s.weight_sup_add_inf θ (y ⊓ d) c
  have h2 : y ⊓ d ⊓ c = y ⊓ c := by rw [inf_assoc, inf_eq_right.mpr hcd]
  rw [h2] at h1
  have hz := H (y ⊓ d ⊔ c) le_sup_right (sup_le inf_le_right hcd) (by linarith)
  exact le_antisymm (le_inf inf_le_left (sup_eq_right.mp hz)) (inf_le_inf_left y hcd)

/-- If `c ≤ d` and `d` maximizes `w_θ` on `[c, d]`, then `w_θ (y ⊔ c) ≤ w_θ (y ⊔ d)`. -/
lemma weight_sup_le (hcd : c ≤ d) (H : ∀ z, c ≤ z → z ≤ d → s.weight θ z ≤ s.weight θ d)
    (y : L) : s.weight θ (y ⊔ c) ≤ s.weight θ (y ⊔ d) := by
  have h1 := s.weight_sup_add_inf θ (y ⊔ c) d
  have h2 : y ⊔ c ⊔ d = y ⊔ d := by rw [sup_assoc, sup_eq_right.mpr hcd]
  have h3 := H ((y ⊔ c) ⊓ d) (le_inf le_sup_right hcd) inf_le_right
  rw [h2] at h1
  linarith

/-- If `c ≤ d` and `d` is the only maximizer of `w_θ` on `[c, d]`, then
`w_θ (y ⊔ c) = w_θ (y ⊔ d)` forces `y ⊔ c = y ⊔ d`. -/
lemma sup_eq_of_weight_eq (hcd : c ≤ d)
    (H : ∀ z, c ≤ z → z ≤ d → s.weight θ z = s.weight θ d → z = d) {y : L}
    (heq : s.weight θ (y ⊔ c) = s.weight θ (y ⊔ d)) : y ⊔ c = y ⊔ d := by
  have h1 := s.weight_sup_add_inf θ (y ⊔ c) d
  have h2 : y ⊔ c ⊔ d = y ⊔ d := by rw [sup_assoc, sup_eq_right.mpr hcd]
  rw [h2] at h1
  have hz := H ((y ⊔ c) ⊓ d) (le_inf le_sup_right hcd) inf_le_right (by linarith)
  exact le_antisymm (sup_le_sup_left hcd y) (sup_le le_sup_left (inf_eq_right.mp hz))

end OrderedField

/-! ### Harder–Narasimhan filtrations -/

variable [BoundedOrder L]

/-- A Harder–Narasimhan filtration of the slope function `s`: a chain
`⊥ = chain 0 < ⋯ < chain n = ⊤` whose factors are semistable with strictly decreasing slopes. -/
structure HNFiltration where
  /-- The number of factors. -/
  n : ℕ
  /-- The chain of prefixes. -/
  chain : Fin (n + 1) → L
  strictMono : StrictMono chain
  chain_zero : chain 0 = ⊥
  chain_last : chain (Fin.last n) = ⊤
  semistable : ∀ i : Fin n, s.IsSemistable (chain i.castSucc) (chain i.succ)
  slope_strictAnti : StrictAnti fun i : Fin n ↦ s.slope (chain i.castSucc) (chain i.succ)

variable {s} in
/-- A semistable lattice is its own HN filtration, `⊥ < ⊤`. -/
def HNFiltration.ofSemistable (h : s.IsSemistable ⊥ ⊤) : s.HNFiltration where
  n := 1
  chain := ![⊥, ⊤]
  strictMono := Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
    fin_cases i
    exact h.1
  chain_zero := rfl
  chain_last := rfl
  semistable i := by
    fin_cases i
    exact h
  slope_strictAnti := Fin.strictAnti_iff_succ_lt.mpr fun i ↦ i.elim0

variable {s} in
/-- The two-step HN filtration `⊥ < x < ⊤`, from semistable factors of decreasing slopes. -/
def HNFiltration.two {x : L} (h₁ : s.IsSemistable ⊥ x) (h₂ : s.IsSemistable x ⊤)
    (h : s.slope x ⊤ < s.slope ⊥ x) : s.HNFiltration where
  n := 2
  chain := ![⊥, x, ⊤]
  strictMono := Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
    fin_cases i
    exacts [h₁.1, h₂.1]
  chain_zero := rfl
  chain_last := rfl
  semistable i := by
    fin_cases i
    exacts [h₁, h₂]
  slope_strictAnti := Fin.strictAnti_iff_succ_lt.mpr fun i ↦ by
    fin_cases i
    exact h

namespace HNFiltration

variable {s} (F : s.HNFiltration)

/-- The slope of the `i`th factor `[chain i, chain (i + 1)]`. -/
def factorSlope (i : Fin F.n) : K := s.slope (F.chain i.castSucc) (F.chain i.succ)

/-- The weight of the slope of a factor takes the same value at both of its ends. -/
lemma weight_factorSlope_succ (i : Fin F.n) :
    s.weight (F.factorSlope i) (F.chain i.succ) =
      s.weight (F.factorSlope i) (F.chain i.castSucc) :=
  s.weight_slope_eq (F.strictMono i.castSucc_lt_succ)

/-- The chain extended to `ℕ`, constant `⊤` after `n`. -/
def c (j : ℕ) : L := F.chain ⟨min j F.n, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma c_of_le {j : ℕ} (hj : j ≤ F.n) : F.c j = F.chain ⟨j, Nat.lt_succ_of_le hj⟩ := by
  simp only [c, min_eq_left hj]

lemma c_fin (k : Fin (F.n + 1)) : F.c k = F.chain k := by
  rw [F.c_of_le (Nat.le_of_lt_succ k.isLt)]

@[simp] lemma c_zero : F.c 0 = ⊥ := by
  rw [F.c_of_le (Nat.zero_le _)]
  exact F.chain_zero

lemma c_n : F.c F.n = ⊤ := by
  rw [F.c_of_le le_rfl]
  exact F.chain_last

lemma c_mono : Monotone F.c := fun _ _ h ↦
  F.strictMono.monotone (Fin.mk_le_mk.mpr (min_le_min_right _ h))

lemma c_succ_of_le {j : ℕ} (hj : F.n ≤ j) : F.c (j + 1) = F.c j := by
  simp only [c, min_eq_right hj, min_eq_right (hj.trans (Nat.le_succ j))]

lemma c_isSemistable {j : ℕ} (hj : j < F.n) : s.IsSemistable (F.c j) (F.c (j + 1)) := by
  rw [F.c_of_le hj.le, F.c_of_le hj]
  exact F.semistable ⟨j, hj⟩

lemma slope_c {j : ℕ} (hj : j < F.n) :
    s.slope (F.c j) (F.c (j + 1)) = F.factorSlope ⟨j, hj⟩ := by
  rw [F.c_of_le hj.le, F.c_of_le hj]
  rfl

section OrderedField

variable [IsStrictOrderedRing K] {θ : K}

/-- A factor of slope at most `θ` has its bottom as a maximizer of `w_θ`. -/
lemma weight_le_c_bot {j : ℕ} (hj : j < F.n) (hθ : F.factorSlope ⟨j, hj⟩ ≤ θ) {z : L}
    (h1 : F.c j ≤ z) (h2 : z ≤ F.c (j + 1)) : s.weight θ z ≤ s.weight θ (F.c j) :=
  (F.c_isSemistable hj).weight_le_bot (by rw [F.slope_c hj]; exact hθ) h1 h2

/-- A factor of slope less than `θ` has its bottom as the only maximizer of `w_θ`. -/
lemma eq_c_bot {j : ℕ} (hj : j < F.n) (hθ : F.factorSlope ⟨j, hj⟩ < θ) {z : L}
    (h1 : F.c j ≤ z) (h2 : z ≤ F.c (j + 1)) (heq : s.weight θ z = s.weight θ (F.c j)) :
    z = F.c j :=
  (F.c_isSemistable hj).eq_bot_of_weight_eq (by rw [F.slope_c hj]; exact hθ) h1 h2 heq

/-- A factor of slope at least `θ` has its top as a maximizer of `w_θ`. -/
lemma weight_le_c_top {j : ℕ} (hj : j < F.n) (hθ : θ ≤ F.factorSlope ⟨j, hj⟩) {z : L}
    (h1 : F.c j ≤ z) (h2 : z ≤ F.c (j + 1)) : s.weight θ z ≤ s.weight θ (F.c (j + 1)) :=
  (F.c_isSemistable hj).weight_le_top (by rw [F.slope_c hj]; exact hθ) h1 h2

/-- A factor of slope greater than `θ` has its top as the only maximizer of `w_θ`. -/
lemma eq_c_top {j : ℕ} (hj : j < F.n) (hθ : θ < F.factorSlope ⟨j, hj⟩) {z : L}
    (h1 : F.c j ≤ z) (h2 : z ≤ F.c (j + 1)) (heq : s.weight θ z = s.weight θ (F.c (j + 1))) :
    z = F.c (j + 1) :=
  (F.c_isSemistable hj).eq_top_of_weight_eq (by rw [F.slope_c hj]; exact hθ) h1 h2 heq

/-- Going up from `c a` through factors of slope at most `θ`:
`w_θ (y ⊓ c (a + m)) ≤ w_θ (y ⊓ c a)`. -/
lemma weight_inf_c_le {a : ℕ} (hθ : ∀ j (hj : j < F.n), a ≤ j → F.factorSlope ⟨j, hj⟩ ≤ θ)
    (y : L) : ∀ m, s.weight θ (y ⊓ F.c (a + m)) ≤ s.weight θ (y ⊓ F.c a)
  | 0 => le_rfl
  | m + 1 => by
    refine le_trans ?_ (weight_inf_c_le hθ y m)
    rw [← add_assoc]
    by_cases hj : a + m < F.n
    · exact weight_inf_le (F.c_mono (Nat.le_succ _))
        (fun z h1 h2 ↦ F.weight_le_c_bot hj (hθ _ hj (by omega)) h1 h2) y
    · rw [F.c_succ_of_le (by omega)]

/-- Going up through factors of slope less than `θ`, equality of weights forces
`y ⊓ c (a + m) = y ⊓ c a`. -/
lemma inf_c_eq {a : ℕ} (hθ : ∀ j (hj : j < F.n), a ≤ j → F.factorSlope ⟨j, hj⟩ < θ)
    (y : L) : ∀ m, s.weight θ (y ⊓ F.c (a + m)) = s.weight θ (y ⊓ F.c a) →
      y ⊓ F.c (a + m) = y ⊓ F.c a
  | 0, _ => rfl
  | m + 1, heq => by
    have hθ' : ∀ j (hj : j < F.n), a ≤ j → F.factorSlope ⟨j, hj⟩ ≤ θ :=
      fun j hj ha ↦ (hθ j hj ha).le
    have hQ := F.weight_inf_c_le hθ' y m
    rw [← add_assoc] at heq ⊢
    by_cases hj : a + m < F.n
    · have hP := weight_inf_le (F.c_mono (Nat.le_succ (a + m)))
        (fun z h1 h2 ↦ F.weight_le_c_bot hj (hθ' _ hj (by omega)) h1 h2) y
      have hPQ : y ⊓ F.c (a + m + 1) = y ⊓ F.c (a + m) :=
        inf_eq_of_weight_eq (F.c_mono (Nat.le_succ _))
          (fun z h1 h2 h3 ↦ F.eq_c_bot hj (hθ _ hj (by omega)) h1 h2 h3) (by linarith)
      rw [hPQ]
      exact inf_c_eq hθ y m (by linarith)
    · rw [F.c_succ_of_le (by omega)] at heq ⊢
      exact inf_c_eq hθ y m heq

/-- Going down to `c j` from `c a = c (j + d)` through factors of slope at least `θ`:
`w_θ (y ⊔ c j) ≤ w_θ (y ⊔ c a)`. -/
lemma weight_sup_c_le {a : ℕ} (hθ : ∀ j (hj : j < F.n), j + 1 ≤ a → θ ≤ F.factorSlope ⟨j, hj⟩)
    (ha : a ≤ F.n) (y : L) :
    ∀ d j, j + d = a → s.weight θ (y ⊔ F.c j) ≤ s.weight θ (y ⊔ F.c a)
  | 0, j, h => by rw [← h, add_zero]
  | d + 1, j, h => by
    have hj : j < F.n := by omega
    refine le_trans ?_ (weight_sup_c_le hθ ha y d (j + 1) (by omega))
    exact weight_sup_le (F.c_mono (Nat.le_succ j))
      (fun z h1 h2 ↦ F.weight_le_c_top hj (hθ _ hj (by omega)) h1 h2) y

/-- Going down through factors of slope greater than `θ`, equality of weights forces
`y ⊔ c j = y ⊔ c a`. -/
lemma sup_c_eq {a : ℕ} (hθ : ∀ j (hj : j < F.n), j + 1 ≤ a → θ < F.factorSlope ⟨j, hj⟩)
    (ha : a ≤ F.n) (y : L) : ∀ d j, j + d = a →
      s.weight θ (y ⊔ F.c j) = s.weight θ (y ⊔ F.c a) → y ⊔ F.c j = y ⊔ F.c a
  | 0, j, h, _ => by rw [← h, add_zero]
  | d + 1, j, h, heq => by
    have hj : j < F.n := by omega
    have hθ' : ∀ j (hj : j < F.n), j + 1 ≤ a → θ ≤ F.factorSlope ⟨j, hj⟩ :=
      fun j hj ha ↦ (hθ j hj ha).le
    have hP := weight_sup_le (F.c_mono (Nat.le_succ j))
      (fun z h1 h2 ↦ F.weight_le_c_top hj (hθ' _ hj (by omega)) h1 h2) y
    have hQ := F.weight_sup_c_le hθ' ha y d (j + 1) (by omega)
    have hPQ : y ⊔ F.c j = y ⊔ F.c (j + 1) :=
      sup_eq_of_weight_eq (F.c_mono (Nat.le_succ _))
        (fun z h1 h2 h3 ↦ F.eq_c_top hj (hθ _ hj (by omega)) h1 h2 h3) (by linarith)
    rw [hPQ]
    exact sup_c_eq hθ ha y d (j + 1) (by omega) (by linarith)

/-- **The prefixes maximize the weights.** If the factors below `chain k` have slopes at least
`θ` and those above have slopes at most `θ`, then `chain k` maximizes `w_θ` over `L`. -/
theorem weight_le (k : Fin (F.n + 1)) (h₁ : ∀ i : Fin F.n, i.succ ≤ k → θ ≤ F.factorSlope i)
    (h₂ : ∀ i : Fin F.n, k ≤ i.castSucc → F.factorSlope i ≤ θ) (x : L) :
    s.weight θ x ≤ s.weight θ (F.chain k) := by
  have hk := F.c_fin k
  have hkn : (k : ℕ) ≤ F.n := Nat.le_of_lt_succ k.isLt
  have hup := F.weight_inf_c_le (a := k)
    (fun j hj ha ↦ h₂ ⟨j, hj⟩ (by simpa [Fin.le_def] using ha)) (x ⊔ F.chain k) (F.n - k)
  have hdown := F.weight_sup_c_le (a := k)
    (fun j hj ha ↦ h₁ ⟨j, hj⟩ (by simpa [Fin.le_def] using ha)) hkn (x ⊓ F.chain k) k 0
    (zero_add _)
  rw [Nat.add_sub_cancel' hkn, F.c_n, inf_top_eq, hk, inf_eq_right.mpr le_sup_right] at hup
  rw [F.c_zero, sup_bot_eq, hk, sup_eq_right.mpr inf_le_right] at hdown
  have := s.weight_sup_add_inf θ x (F.chain k)
  linarith

/-- **The prefixes are the only maximizers.** If the factors below `chain k` have slopes greater
than `θ` and those above have slopes less than `θ`, then `chain k` is the only maximizer
of `w_θ`. -/
theorem eq_of_weight_eq (k : Fin (F.n + 1))
    (h₁ : ∀ i : Fin F.n, i.succ ≤ k → θ < F.factorSlope i)
    (h₂ : ∀ i : Fin F.n, k ≤ i.castSucc → F.factorSlope i < θ) {x : L}
    (hx : s.weight θ x = s.weight θ (F.chain k)) : x = F.chain k := by
  have hk := F.c_fin k
  have hkn : (k : ℕ) ≤ F.n := Nat.le_of_lt_succ k.isLt
  have h₂' : ∀ j (hj : j < F.n), (k : ℕ) ≤ j → F.factorSlope ⟨j, hj⟩ < θ :=
    fun j hj ha ↦ h₂ ⟨j, hj⟩ (by simpa [Fin.le_def] using ha)
  have h₁' : ∀ j (hj : j < F.n), j + 1 ≤ (k : ℕ) → θ < F.factorSlope ⟨j, hj⟩ :=
    fun j hj ha ↦ h₁ ⟨j, hj⟩ (by simpa [Fin.le_def] using ha)
  have hup := F.weight_inf_c_le (fun j hj ha ↦ (h₂' j hj ha).le) (x ⊔ F.chain k) (F.n - k)
  have hdown := F.weight_sup_c_le (fun j hj ha ↦ (h₁' j hj ha).le) hkn (x ⊓ F.chain k) k 0
    (zero_add _)
  have hup' := F.inf_c_eq h₂' (x ⊔ F.chain k) (F.n - k)
  have hdown' := F.sup_c_eq h₁' hkn (x ⊓ F.chain k) k 0 (zero_add _)
  rw [Nat.add_sub_cancel' hkn, F.c_n, inf_top_eq, hk, inf_eq_right.mpr le_sup_right] at hup hup'
  rw [F.c_zero, sup_bot_eq, hk, sup_eq_right.mpr inf_le_right] at hdown hdown'
  have := s.weight_sup_add_inf θ x (F.chain k)
  have e1 := hup' (by linarith)
  have e2 := hdown' (by linarith)
  exact le_antisymm (sup_eq_right.mp e1) (inf_eq_right.mp e2)

omit [IsStrictOrderedRing K] in
/-- Every `θ` lies between the slopes around some prefix. -/
lemma exists_index (θ : K) : ∃ k : Fin (F.n + 1),
    (∀ i : Fin F.n, i.succ ≤ k → θ ≤ F.factorSlope i) ∧
      ∀ i : Fin F.n, k ≤ i.castSucc → F.factorSlope i ≤ θ := by
  classical
  have hP : ∃ j, j = F.n ∨ ∃ hj : j < F.n, F.factorSlope ⟨j, hj⟩ ≤ θ := ⟨F.n, Or.inl rfl⟩
  have hkn : Nat.find hP ≤ F.n := Nat.find_min' hP (Or.inl rfl)
  refine ⟨⟨Nat.find hP, Nat.lt_succ_of_le hkn⟩, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have hlt : (i : ℕ) < Nat.find hP := by simpa [Fin.le_def] using hi
    have := Nat.find_min hP hlt
    simp only [not_or, not_exists, not_le] at this
    exact (this.2 i.isLt).le
  · have hle : Nat.find hP ≤ (i : ℕ) := by simpa [Fin.le_def] using hi
    rcases Nat.find_spec hP with h | ⟨hj, hθ⟩
    · omega
    · exact (F.slope_strictAnti.antitone (Fin.mk_le_mk.mpr hle)).trans hθ

omit [Lattice L] [BoundedOrder L] in
private lemma exists_between_finset {A B : Finset K} (h : ∀ a ∈ A, ∀ b ∈ B, b < a) :
    ∃ θ : K, (∀ a ∈ A, θ < a) ∧ ∀ b ∈ B, b < θ := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rcases B.eq_empty_or_nonempty with rfl | hB
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨B.max' hB + 1, by simp, fun b hb ↦ (B.le_max' b hb).trans_lt (lt_add_one _)⟩
  · rcases B.eq_empty_or_nonempty with rfl | hB
    · exact ⟨A.min' hA - 1, fun a ha ↦ (sub_one_lt _).trans_le (A.min'_le a ha), by simp⟩
    · obtain ⟨θ, h1, h2⟩ := exists_between (h _ (A.min'_mem hA) _ (B.max'_mem hB))
      exact ⟨θ, fun a ha ↦ h2.trans_le (A.min'_le a ha), fun b hb ↦ (B.le_max' b hb).trans_lt h1⟩

/-- Every prefix lies strictly between the slopes around it for some `θ`. -/
lemma exists_slope_between (k : Fin (F.n + 1)) : ∃ θ : K,
    (∀ i : Fin F.n, i.succ ≤ k → θ < F.factorSlope i) ∧
      ∀ i : Fin F.n, k ≤ i.castSucc → F.factorSlope i < θ := by
  classical
  obtain ⟨θ, h1, h2⟩ := exists_between_finset
    (A := (Finset.univ.filter fun i : Fin F.n ↦ i.succ ≤ k).image F.factorSlope)
    (B := (Finset.univ.filter fun i : Fin F.n ↦ k ≤ i.castSucc).image F.factorSlope) (by
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩
      refine F.slope_strictAnti ?_
      rw [Fin.lt_def]
      rw [Fin.le_def] at hi hi'
      simp only [Fin.val_succ, Fin.val_castSucc] at hi hi'
      omega)
  exact ⟨θ, fun i hi ↦ h1 _ (Finset.mem_image_of_mem _ (by simpa using hi)),
    fun i hi ↦ h2 _ (Finset.mem_image_of_mem _ (by simpa using hi))⟩

/-- **The prefixes are intrinsic.** An element is a prefix of an HN filtration if and only if it
is the unique maximizer of some weight `w_θ`. -/
theorem mem_range_chain_iff (x : L) : x ∈ Set.range F.chain ↔
    ∃ θ : K, ∀ y, s.weight θ y ≤ s.weight θ x ∧ (s.weight θ y = s.weight θ x → y = x) := by
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨θ, h₁, h₂⟩ := F.exists_slope_between k
    exact ⟨θ, fun y ↦ ⟨F.weight_le k (fun i hi ↦ (h₁ i hi).le) (fun i hi ↦ (h₂ i hi).le) y,
      F.eq_of_weight_eq k h₁ h₂⟩⟩
  · rintro ⟨θ, hx⟩
    obtain ⟨k, h₁, h₂⟩ := F.exists_index θ
    exact ⟨k, ((hx (F.chain k)).2 (le_antisymm (hx _).1 (F.weight_le k h₁ h₂ x)))⟩

/-- **Uniqueness.** A slope function has at most one HN filtration. -/
instance instSubsingleton : Subsingleton s.HNFiltration := by
  refine ⟨fun F G ↦ ?_⟩
  have hrange : Set.range F.chain = Set.range G.chain :=
    Set.ext fun x ↦ by rw [F.mem_range_chain_iff, G.mem_range_chain_iff]
  have hn : F.n = G.n := by
    have hF := Nat.card_range_of_injective F.strictMono.injective
    have hG := Nat.card_range_of_injective G.strictMono.injective
    rw [hrange, hG, Nat.card_fin, Nat.card_fin] at hF
    omega
  cases F with
  | mk n chain hmono _ _ _ _ =>
    cases G with
    | mk m chain' hmono' _ _ _ _ =>
      dsimp only at hn hrange
      subst hn
      have := (StrictMono.range_inj_of_wellFoundedLT hmono hmono').mp hrange
      subst this
      rfl

/-- **The edges of the HN polygon support the points from above.** For the slope `μᵢ` of the
`i`th factor, `w_{μᵢ} x ≤ w_{μᵢ} (chain i) = w_{μᵢ} (chain (i + 1))`: the point
`(rk x, deg x)` lies on or below the line through the `i`th edge. -/
theorem weight_le_edge (i : Fin F.n) (x : L) :
    s.weight (F.factorSlope i) x ≤ s.weight (F.factorSlope i) (F.chain i.castSucc) := by
  refine F.weight_le i.castSucc (fun j hj ↦ F.slope_strictAnti.antitone ?_)
    (fun j hj ↦ F.slope_strictAnti.antitone ?_) x
  · rw [Fin.le_def] at hj ⊢
    simp only [Fin.val_succ, Fin.val_castSucc] at hj
    omega
  · rwa [Fin.castSucc_le_castSucc_iff] at hj

/-- **The HN filtration reads the upper boundary of the convex hull** of the points
`(rk x, deg x)`: the hull lies below every edge line of the polygon through the points
`(rk (chain k), deg (chain k))`, which are among the points. -/
theorem convexHull_subset :
    convexHull K (Set.range fun x : L ↦ (s.rk x, s.deg x)) ⊆
      ⋂ i : Fin F.n, {p : K × K | p.2 - F.factorSlope i * p.1 ≤
        s.weight (F.factorSlope i) (F.chain i.castSucc)} := by
  refine convexHull_min ?_ (convex_iInter fun i ↦ convex_halfSpace_le ?_ _)
  · rintro _ ⟨x, rfl⟩
    exact Set.mem_iInter.mpr fun i ↦ F.weight_le_edge i x
  · exact ⟨fun p q ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun a p ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩

end OrderedField

end HNFiltration

variable {s} in
/-- **HN filtrations only depend on the slope order.** An HN filtration of `s` is one of every
slope function `t` on `L` whose interval slopes are ordered like those of `s`. -/
def HNFiltration.ofSlopeOrder [IsStrictOrderedRing K] {K' : Type*} [Field K'] [LinearOrder K']
    [IsStrictOrderedRing K'] {t : SlopeFunction L K'}
    (h : ∀ x y x' y' : L, x < y → x' < y' →
      (s.slope x y ≤ s.slope x' y' ↔ t.slope x y ≤ t.slope x' y'))
    (F : s.HNFiltration) : t.HNFiltration where
  n := F.n
  chain := F.chain
  strictMono := F.strictMono
  chain_zero := F.chain_zero
  chain_last := F.chain_last
  semistable i := by
    have hlt := F.strictMono i.castSucc_lt_succ
    rw [t.isSemistable_iff hlt]
    intro z hz₁ hz₂
    exact (h _ _ _ _ hz₁ hlt).mp ((s.isSemistable_iff hlt).mp (F.semistable i) z hz₁ hz₂)
  slope_strictAnti i j hij := by
    have := F.slope_strictAnti hij
    rw [← not_le] at this ⊢
    rwa [← h _ _ _ _ (F.strictMono (Fin.castSucc_lt_succ (i := i)))
      (F.strictMono (Fin.castSucc_lt_succ (i := j)))]

variable {s} in
@[simp] lemma HNFiltration.ofSlopeOrder_chain [IsStrictOrderedRing K] {K' : Type*} [Field K']
    [LinearOrder K'] [IsStrictOrderedRing K'] {t : SlopeFunction L K'}
    (h : ∀ x y x' y' : L, x < y → x' < y' →
      (s.slope x y ≤ s.slope x' y' ↔ t.slope x y ≤ t.slope x' y'))
    (F : s.HNFiltration) : (F.ofSlopeOrder h).chain = F.chain := rfl

variable {s} in
/-- **The opposite HN filtration reads the lower boundary.** For an HN filtration of `s.neg`
with factor slopes `μ'ᵢ`, every point `(rk x, deg x)` lies on or above the line of slope `-μ'ᵢ`
through its `i`th edge. -/
theorem HNFiltration.weight_ge_edge_of_neg [IsStrictOrderedRing K] (F : s.neg.HNFiltration)
    (i : Fin F.n) (x : L) :
    s.weight (-F.factorSlope i) (F.chain i.castSucc) ≤ s.weight (-F.factorSlope i) x := by
  have := F.weight_le_edge i x
  rw [neg_weight, neg_weight] at this
  linarith

end SlopeFunction

end Order
