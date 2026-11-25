/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Order.CompleteLattice.Basic

/-!
# The Thompson and Hilbert pseudometrics on positive functions

For two real functions `x, y` on an index type `ι` and a set `s` of indices, put
`f = log x - log y` on `s`. This file defines

* `thompsonEDist s x y = sup_{i ∈ s} |f i|`, the **Thompson pseudometric**;
* `hilbertEDist s x y = sup_{i, j ∈ s} (f i - f j)`, the oscillation of `f` on `s`, the
  **Hilbert projective pseudometric**,

both with values in `[0, ∞]`, so that no boundedness of the ratios is assumed. For `x, y`
positive on `s`, with `M(x/y) = sup_{i ∈ s} x i / y i`, they are the classical
`log max (M(x/y), M(y/x))` (Thompson, Proc. Amer. Math. Soc. 14 (1963)) and
`log (M(x/y) M(y/x))` (Hilbert 1895; Birkhoff, Trans. Amer. Math. Soc. 85 (1957)) on the open
cone of functions positive on `s`. The Hilbert pseudometric is invariant under positive
rescaling of either argument, so it is a pseudometric on rays; the Thompson pseudometric is not.

Mathlib has neither metric. They are plain functions here, with no `PseudoEMetricSpace`
instance on functions, which carry Mathlib's sup metric. This is the one module for both: the
Birkhoff contraction (`Analysis/Convex/Birkhoff2.lean`), the profile pseudometrics
(`CategoryTheory/MassProfile/Basic.lean`) and the nonexpansiveness of monotone homogeneous maps
use it.

## Main results

* `thompsonEDist_self`, `thompsonEDist_comm`, `thompsonEDist_triangle`, and the same for
  `hilbertEDist`: both are extended pseudometrics on all functions; positivity is used only to
  identify their zeros, `thompsonEDist_eq_zero_iff` (equality on `s`) and
  `hilbertEDist_eq_zero_iff` (proportionality on `s`).
* `hilbertEDist_le_two_mul_thompsonEDist`: `d_H ≤ 2 d_T`.
* `hilbertEDist_smul_left`, `hilbertEDist_smul_right`: rescaling by a positive constant does not
  change `d_H`.
* `thompsonEDist_comp`, `hilbertEDist_comp`: reindexing along any map `e : κ → ι` replaces `s` by
  its image. A bijection of indices preserving `s` is therefore an isometry of both.
-/

open Real Set
open scoped ENNReal

variable {ι κ : Type*}

section Thompson

/-- The **Thompson pseudometric** of two real functions on a set `s` of indices,
`sup_{i ∈ s} |log x i - log y i|`, with values in `[0, ∞]`. For functions positive on `s` it is
`log max (M(x/y), M(y/x))`, `M(x/y) = sup_{i ∈ s} x i / y i` (Thompson, Proc. Amer. Math.
Soc. 14 (1963)). -/
noncomputable def thompsonEDist (s : Set ι) (x y : ι → ℝ) : ℝ≥0∞ :=
  ⨆ i ∈ s, ENNReal.ofReal |log (x i) - log (y i)|

variable {s t : Set ι} {x y z : ι → ℝ}

lemma le_thompsonEDist {i : ι} (hi : i ∈ s) :
    ENNReal.ofReal |log (x i) - log (y i)| ≤ thompsonEDist s x y :=
  le_iSup₂ (f := fun i (_ : i ∈ s) ↦ ENNReal.ofReal |log (x i) - log (y i)|) i hi

lemma thompsonEDist_le_iff {c : ℝ≥0∞} :
    thompsonEDist s x y ≤ c ↔ ∀ i ∈ s, ENNReal.ofReal |log (x i) - log (y i)| ≤ c :=
  iSup₂_le_iff

@[simp]
lemma thompsonEDist_self : thompsonEDist s x x = 0 := by
  simp [thompsonEDist]

lemma thompsonEDist_comm : thompsonEDist s x y = thompsonEDist s y x := by
  simp only [thompsonEDist, abs_sub_comm]

lemma thompsonEDist_triangle :
    thompsonEDist s x z ≤ thompsonEDist s x y + thompsonEDist s y z := by
  refine thompsonEDist_le_iff.2 fun i hi ↦ ?_
  calc ENNReal.ofReal |log (x i) - log (z i)|
      ≤ ENNReal.ofReal (|log (x i) - log (y i)| + |log (y i) - log (z i)|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ = ENNReal.ofReal |log (x i) - log (y i)| + ENNReal.ofReal |log (y i) - log (z i)| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ thompsonEDist s x y + thompsonEDist s y z :=
        add_le_add (le_thompsonEDist hi) (le_thompsonEDist hi)

lemma thompsonEDist_mono (h : s ⊆ t) : thompsonEDist s x y ≤ thompsonEDist t x y :=
  biSup_mono fun _ hi ↦ h hi

@[simp]
lemma thompsonEDist_empty : thompsonEDist ∅ x y = 0 := by
  simp [thompsonEDist]

/-- Reindexing along any map `e` replaces the set of indices by its image. -/
lemma thompsonEDist_comp (e : κ → ι) (t : Set κ) :
    thompsonEDist t (x ∘ e) (y ∘ e) = thompsonEDist (e '' t) x y := by
  simp only [thompsonEDist, Function.comp_apply, iSup_image]

/-- For functions positive on `s`, the Thompson pseudometric vanishes exactly when they agree
on `s`. -/
lemma thompsonEDist_eq_zero_iff (hx : ∀ i ∈ s, 0 < x i) (hy : ∀ i ∈ s, 0 < y i) :
    thompsonEDist s x y = 0 ↔ EqOn x y s := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦ ?_⟩
  · have h0 := (le_thompsonEDist (x := x) (y := y) hi).trans h.le
    rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero] at h0
    exact Real.log_injOn_pos (hx i hi) (hy i hi) h0
  · refine le_antisymm (thompsonEDist_le_iff.2 fun i hi ↦ ?_) bot_le
    simp [h hi]

end Thompson

section Hilbert

/-- The **Hilbert projective pseudometric** of two real functions on a set `s` of indices: the
oscillation `sup_{i, j ∈ s} ((log x i - log y i) - (log x j - log y j))` of `log x - log y` on
`s`, with values in `[0, ∞]`. For functions positive on `s` it is `log (M(x/y) M(y/x))`,
`M(x/y) = sup_{i ∈ s} x i / y i` (Birkhoff, Trans. Amer. Math. Soc. 85 (1957)). -/
noncomputable def hilbertEDist (s : Set ι) (x y : ι → ℝ) : ℝ≥0∞ :=
  ⨆ i ∈ s, ⨆ j ∈ s, ENNReal.ofReal ((log (x i) - log (y i)) - (log (x j) - log (y j)))

variable {s t : Set ι} {x y z : ι → ℝ}

lemma le_hilbertEDist {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    ENNReal.ofReal ((log (x i) - log (y i)) - (log (x j) - log (y j))) ≤ hilbertEDist s x y :=
  (le_iSup₂ (f := fun j (_ : j ∈ s) ↦
      ENNReal.ofReal ((log (x i) - log (y i)) - (log (x j) - log (y j)))) j hj).trans
    (le_iSup₂ (f := fun i (_ : i ∈ s) ↦ ⨆ j ∈ s,
      ENNReal.ofReal ((log (x i) - log (y i)) - (log (x j) - log (y j)))) i hi)

lemma hilbertEDist_le_iff {c : ℝ≥0∞} :
    hilbertEDist s x y ≤ c ↔ ∀ i ∈ s, ∀ j ∈ s,
      ENNReal.ofReal ((log (x i) - log (y i)) - (log (x j) - log (y j))) ≤ c := by
  simp only [hilbertEDist, iSup₂_le_iff]

@[simp]
lemma hilbertEDist_self : hilbertEDist s x x = 0 := by
  simp [hilbertEDist]

lemma hilbertEDist_comm : hilbertEDist s x y = hilbertEDist s y x := by
  refine le_antisymm (hilbertEDist_le_iff.2 fun i hi j hj ↦ ?_)
    (hilbertEDist_le_iff.2 fun i hi j hj ↦ ?_)
  · refine le_of_eq_of_le ?_ (le_hilbertEDist (x := y) (y := x) hj hi)
    ring_nf
  · refine le_of_eq_of_le ?_ (le_hilbertEDist (x := x) (y := y) hj hi)
    ring_nf

lemma hilbertEDist_triangle :
    hilbertEDist s x z ≤ hilbertEDist s x y + hilbertEDist s y z := by
  refine hilbertEDist_le_iff.2 fun i hi j hj ↦ ?_
  have key : (log (x i) - log (z i)) - (log (x j) - log (z j)) =
      ((log (x i) - log (y i)) - (log (x j) - log (y j))) +
        ((log (y i) - log (z i)) - (log (y j) - log (z j))) := by ring
  rw [key]
  exact ENNReal.ofReal_add_le.trans (add_le_add (le_hilbertEDist hi hj) (le_hilbertEDist hi hj))

lemma hilbertEDist_mono (h : s ⊆ t) : hilbertEDist s x y ≤ hilbertEDist t x y :=
  hilbertEDist_le_iff.2 fun _ hi _ hj ↦ le_hilbertEDist (h hi) (h hj)

@[simp]
lemma hilbertEDist_empty : hilbertEDist ∅ x y = 0 := by
  simp [hilbertEDist]

/-- Reindexing along any map `e` replaces the set of indices by its image. -/
lemma hilbertEDist_comp (e : κ → ι) (t : Set κ) :
    hilbertEDist t (x ∘ e) (y ∘ e) = hilbertEDist (e '' t) x y := by
  simp only [hilbertEDist, Function.comp_apply, iSup_image]

/-- `d_H ≤ 2 d_T`: an oscillation is at most twice the supremum of the absolute value. -/
lemma hilbertEDist_le_two_mul_thompsonEDist :
    hilbertEDist s x y ≤ 2 * thompsonEDist s x y := by
  refine hilbertEDist_le_iff.2 fun i hi j hj ↦ ?_
  calc ENNReal.ofReal ((log (x i) - log (y i)) - (log (x j) - log (y j)))
      ≤ ENNReal.ofReal (|log (x i) - log (y i)| + |log (x j) - log (y j)|) :=
        ENNReal.ofReal_le_ofReal (by
          linarith [le_abs_self (log (x i) - log (y i)), neg_abs_le (log (x j) - log (y j))])
    _ = ENNReal.ofReal |log (x i) - log (y i)| + ENNReal.ofReal |log (x j) - log (y j)| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ thompsonEDist s x y + thompsonEDist s x y :=
        add_le_add (le_thompsonEDist hi) (le_thompsonEDist hj)
    _ = 2 * thompsonEDist s x y := (two_mul _).symm

/-- Rescaling the first function by a positive constant does not change `d_H`, provided it does
not vanish on `s`. -/
lemma hilbertEDist_smul_left {c : ℝ} (hc : 0 < c) (hx : ∀ i ∈ s, x i ≠ 0) :
    hilbertEDist s (c • x) y = hilbertEDist s x y := by
  have key : ∀ i ∈ s, ∀ j ∈ s, (log ((c • x) i) - log (y i)) - (log ((c • x) j) - log (y j)) =
      (log (x i) - log (y i)) - (log (x j) - log (y j)) := by
    intro i hi j hj
    simp only [Pi.smul_apply, smul_eq_mul, Real.log_mul hc.ne' (hx i hi),
      Real.log_mul hc.ne' (hx j hj)]
    ring
  refine le_antisymm (hilbertEDist_le_iff.2 fun i hi j hj ↦ ?_)
    (hilbertEDist_le_iff.2 fun i hi j hj ↦ ?_)
  · rw [key i hi j hj]
    exact le_hilbertEDist hi hj
  · rw [← key i hi j hj]
    exact le_hilbertEDist hi hj

/-- Rescaling the second function by a positive constant does not change `d_H`, provided it
does not vanish on `s`. -/
lemma hilbertEDist_smul_right {c : ℝ} (hc : 0 < c) (hy : ∀ i ∈ s, y i ≠ 0) :
    hilbertEDist s x (c • y) = hilbertEDist s x y := by
  rw [hilbertEDist_comm, hilbertEDist_smul_left hc hy, hilbertEDist_comm]

/-- For functions positive on `s`, the Hilbert pseudometric vanishes exactly when they are
proportional on `s`. -/
lemma hilbertEDist_eq_zero_iff (hx : ∀ i ∈ s, 0 < x i) (hy : ∀ i ∈ s, 0 < y i) :
    hilbertEDist s x y = 0 ↔ ∃ c : ℝ, 0 < c ∧ EqOn x (c • y) s := by
  constructor
  · intro h
    rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
    · exact ⟨1, one_pos, fun _ hi ↦ hi.elim⟩
    refine ⟨x i₀ / y i₀, div_pos (hx i₀ hi₀) (hy i₀ hi₀), fun i hi ↦ ?_⟩
    have hle : ∀ i ∈ s, ∀ j ∈ s,
        (log (x i) - log (y i)) - (log (x j) - log (y j)) ≤ 0 := fun i hi j hj ↦ by
      have h0 := (le_hilbertEDist (x := x) (y := y) hi hj).trans h.le
      rwa [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h0
    have heq : log (x i) - log (y i) = log (x i₀) - log (y i₀) :=
      le_antisymm (by linarith [hle i hi i₀ hi₀]) (by linarith [hle i₀ hi₀ i hi])
    have hxi := hx i hi
    have hyi := hy i hi
    have hx₀ := hx i₀ hi₀
    have hy₀ := hy i₀ hi₀
    rw [← Real.log_div hxi.ne' hyi.ne', ← Real.log_div hx₀.ne' hy₀.ne'] at heq
    have h2 : x i / y i = x i₀ / y i₀ :=
      Real.log_injOn_pos (Set.mem_Ioi.2 (div_pos hxi hyi)) (Set.mem_Ioi.2 (div_pos hx₀ hy₀)) heq
    rw [div_eq_div_iff hyi.ne' hy₀.ne'] at h2
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hy₀.ne']
    linarith
  · rintro ⟨c, hc, hxy⟩
    have hxy' : hilbertEDist s x y = hilbertEDist s (c • y) y := by
      refine le_antisymm (hilbertEDist_le_iff.2 fun i hi j hj ↦ ?_)
        (hilbertEDist_le_iff.2 fun i hi j hj ↦ ?_)
      · rw [hxy hi, hxy hj]
        exact le_hilbertEDist hi hj
      · rw [← hxy hi, ← hxy hj]
        exact le_hilbertEDist hi hj
    rw [hxy', hilbertEDist_smul_left hc fun i hi ↦ (hy i hi).ne', hilbertEDist_self]

end Hilbert
