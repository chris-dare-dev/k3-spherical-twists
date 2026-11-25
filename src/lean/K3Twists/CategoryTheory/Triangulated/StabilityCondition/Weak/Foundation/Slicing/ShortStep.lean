/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Foundation.PreStabilityCondition
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Evaluation
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The short-step stability test

Let `τ` and `ν` be slicings whose intrinsic phases differ by less than `ε` on every nonzero object,
`|φ^±_ν(E) - φ^±_τ(E)| < ε` (`Slicing.PhaseClose`), and let `Z` be a central charge compatible with
`ν`. This is the situation of one short step along a path of stability conditions: for Bridgeland's
metric (arXiv:math/0212237, §8) it holds as soon as the distance is less than `ε`. The **short-step
stability test** decides `ν`-semistability of an object from `τ` and `Z` alone, with no `ν`-HN
filtration in sight:

* (A) `E ∈ P([l, r])` if and only if `Hom(P(> r), E) = 0` and `Hom(E, P(< l)) = 0`, in any slicing
  (`Slicing.mem_closedInterval_iff`);
* (B) the **Im-form test**: for `ε ≤ 1/4` and `Z(Y) ∈ ℝ_{> 0} e^{iπφ}`, the object `Y` is
  `ν`-semistable of phase `φ` if and only if `Y ∈ P_τ([φ - ε, φ + ε])` and no distinguished
  triangle `N → Y → Q → N[1]` with `N, Q ≠ 0` in `P_τ([φ - 3ε, φ + 3ε])` has
  `Im(e^{-iπφ} Z(N)) > 0` (`Slicing.semistable_iff_imPhase`); `Y` is `ν`-stable if and only if
  moreover none has `Im(e^{-iπφ} Z(N)) ≥ 0` (`Slicing.isStable_iff_imPhase`).

The bound `ε ≤ 1/4` is what the proof uses: it keeps `N` in `P_ν((φ - 1, φ])` and `Q[-1]` in
`P_ν(≤ φ)`, so that `Hom(P_ν(> φ), Q[-1]) = 0` and the sign of `Im(e^{-iπφ} Z(N))` is that of a
sum of `m_i sin π(φ_i - φ)` with every `φ_i - φ` in `(-1, 0]`.

## Main definitions

* `Slicing.PhaseClose τ ν ε`: the intrinsic phases of `τ` and `ν` differ by less than `ε`.
* `Slicing.IsStable s φ Y`: `Y` is a simple object of the abelian category `P(φ)`, read through
  distinguished triangles with all three vertices in `P(φ)`.
* `PreStabilityCondition.WithClassMap.imPhase σ φ E = Im(e^{-iπφ} Z(E))`.

## Main results

* `Slicing.leProp_iff_phiPlus_le` and its three siblings: the phase cuts of a nonzero object
  through its intrinsic phases; `Slicing.semistable_of_phiPlus_le_of_le_phiMinus`.
* `Slicing.mem_closedInterval_iff`: (A).
* `PreStabilityCondition.WithClassMap.imPhase_pos`, `imPhase_nonpos`, `imPhase_neg`,
  `semistable_of_imPhase_eq_zero`: the sign of `Im(e^{-iπφ} Z(E))` on phase windows of width one.
* `Slicing.semistable_iff_imPhase`, `Slicing.isStable_iff_imPhase`: (B).

## Implementation notes

`P([a, b])` is written `s.geProp C a E ∧ s.leProp C b E`. Only (B) needs the octahedral axiom,
for the truncation of `Y` at `φ` (`HNFiltration.exists_split_at_cutoff`).

## References

* T. Bridgeland, *Stability conditions on triangulated categories*, arXiv:math/0212237, §§3, 5, 8.

## Tags

stability condition, slicing, short-step stability test, semistable object, phase
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Slicing

/-! ### Phase cuts through the intrinsic phases -/

/-- A nonzero semistable object lies below a strict upper phase bound above its phase. -/
theorem ltProp_of_semistable (s : Slicing C) {S : C} {φ t : ℝ} (hS : s.P φ S) (h : φ < t) :
    s.ltProp C t S :=
  s.ltProp_of_hn C (HNFiltration.single C S φ hS) t
    (fun _ => by simpa [HNFiltration.single] using h) (by change 0 < 1; omega)

theorem phiPlus_le_of_leProp (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : s.leProp C t E) : s.phiPlus C E hE ≤ t := by
  rcases h with h | ⟨F, hF, hle⟩
  · exact absurd h hE
  obtain ⟨G, hG, hne⟩ := s.exists_hn_nonzero_first C hE
  rw [s.phiPlus_eq C E hE G hG hne]
  exact (G.phiPlus_le_of_firstFactor_nonzero C s F hG hF hne).trans hle

theorem phiPlus_lt_of_ltProp (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : s.ltProp C t E) : s.phiPlus C E hE < t := by
  rcases h with h | ⟨F, hF, hlt⟩
  · exact absurd h hE
  obtain ⟨G, hG, hne⟩ := s.exists_hn_nonzero_first C hE
  rw [s.phiPlus_eq C E hE G hG hne]
  exact (G.phiPlus_le_of_firstFactor_nonzero C s F hG hF hne).trans_lt hlt

theorem le_phiMinus_of_geProp (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : s.geProp C t E) : t ≤ s.phiMinus C E hE := by
  rcases h with h | ⟨F, hF, hge⟩
  · exact absurd h hE
  obtain ⟨G, hG, hne⟩ := s.exists_hn_nonzero_last C hE
  rw [s.phiMinus_eq C E hE G hG hne]
  exact hge.trans (F.phiMinus_le_of_lastFactor_nonzero C s G hF hG hne)

theorem lt_phiMinus_of_gtProp (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : s.gtProp C t E) : t < s.phiMinus C E hE := by
  rcases h with h | ⟨F, hF, hgt⟩
  · exact absurd h hE
  obtain ⟨G, hG, hne⟩ := s.exists_hn_nonzero_last C hE
  rw [s.phiMinus_eq C E hE G hG hne]
  exact hgt.trans_le (F.phiMinus_le_of_lastFactor_nonzero C s G hF hG hne)

theorem leProp_of_phiPlus_le (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : s.phiPlus C E hE ≤ t) : s.leProp C t E := by
  obtain ⟨G, hG, hne⟩ := s.exists_hn_nonzero_first C hE
  rw [s.phiPlus_eq C E hE G hG hne] at h
  exact Or.inr ⟨G, hG, h⟩

theorem ltProp_of_phiPlus_lt (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : s.phiPlus C E hE < t) : s.ltProp C t E := by
  obtain ⟨G, hG, hne⟩ := s.exists_hn_nonzero_first C hE
  rw [s.phiPlus_eq C E hE G hG hne] at h
  exact Or.inr ⟨G, hG, h⟩

theorem geProp_of_le_phiMinus (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : t ≤ s.phiMinus C E hE) : s.geProp C t E := by
  obtain ⟨G, hG, hne⟩ := s.exists_hn_nonzero_last C hE
  rw [s.phiMinus_eq C E hE G hG hne] at h
  exact Or.inr ⟨G, hG, h⟩

theorem gtProp_of_lt_phiMinus (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : t < s.phiMinus C E hE) : s.gtProp C t E := by
  obtain ⟨G, hG, hne⟩ := s.exists_hn_nonzero_last C hE
  rw [s.phiMinus_eq C E hE G hG hne] at h
  exact Or.inr ⟨G, hG, h⟩

/-- A nonzero object has all its phases at most `t` exactly when `φ⁺ ≤ t`. -/
theorem leProp_iff_phiPlus_le (s : Slicing C) {E : C} (hE : ¬IsZero E) (t : ℝ) :
    s.leProp C t E ↔ s.phiPlus C E hE ≤ t :=
  ⟨s.phiPlus_le_of_leProp hE, s.leProp_of_phiPlus_le hE⟩

/-- A nonzero object has all its phases below `t` exactly when `φ⁺ < t`. -/
theorem ltProp_iff_phiPlus_lt (s : Slicing C) {E : C} (hE : ¬IsZero E) (t : ℝ) :
    s.ltProp C t E ↔ s.phiPlus C E hE < t :=
  ⟨s.phiPlus_lt_of_ltProp hE, s.ltProp_of_phiPlus_lt hE⟩

/-- A nonzero object has all its phases at least `t` exactly when `t ≤ φ⁻`. -/
theorem geProp_iff_le_phiMinus (s : Slicing C) {E : C} (hE : ¬IsZero E) (t : ℝ) :
    s.geProp C t E ↔ t ≤ s.phiMinus C E hE :=
  ⟨s.le_phiMinus_of_geProp hE, s.geProp_of_le_phiMinus hE⟩

/-- A nonzero object has all its phases above `t` exactly when `t < φ⁻`. -/
theorem gtProp_iff_lt_phiMinus (s : Slicing C) {E : C} (hE : ¬IsZero E) (t : ℝ) :
    s.gtProp C t E ↔ t < s.phiMinus C E hE :=
  ⟨s.lt_phiMinus_of_gtProp hE, s.gtProp_of_lt_phiMinus hE⟩

/-- An object whose intrinsic phases are both `φ` is semistable of phase `φ`. -/
theorem semistable_of_phiPlus_le_of_le_phiMinus (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {φ : ℝ} (h₁ : s.phiPlus C E hE ≤ φ) (h₂ : φ ≤ s.phiMinus C E hE) : s.P φ E := by
  obtain ⟨F, hn, hp, hm⟩ := s.exists_hn_intrinsic_width C hE
  have hle := s.phiMinus_le_phiPlus C E hE
  have h0 : F.φ ⟨0, hn⟩ = φ := by
    change F.phiPlus C hn = φ
    linarith
  have hlast : F.φ ⟨F.n - 1, by omega⟩ = φ := by
    change F.phiMinus C hn = φ
    linarith
  have hF1 : F.n = 1 := by
    by_contra hne
    have : F.φ ⟨F.n - 1, by omega⟩ < F.φ ⟨0, hn⟩ := F.hφ (Fin.mk_lt_mk.mpr (by omega))
    linarith
  have := HNFiltration.semistable_of_length_one C s.closedUnderIso F hF1
  rwa [h0] at this

/-- The phase cuts at the phase of a nonzero semistable object. -/
theorem phiPlus_eq_phiMinus_of_semistable (s : Slicing C) {E : C} (hE : ¬IsZero E) {φ : ℝ}
    (hP : s.P φ E) : s.phiPlus C E hE = φ ∧ s.phiMinus C E hE = φ :=
  ⟨s.phiPlus_eq_of_semistable C E hE φ hP, s.phiMinus_eq_of_semistable C E hE φ hP⟩

/-- A nonzero object has an HN filtration with nonzero first and last factors whose phases are the
intrinsic phases and bound every other phase. -/
theorem exists_hn_phase_bounds (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.factor ⟨0, hn⟩) ∧ ¬IsZero (F.factor ⟨F.n - 1, by omega⟩) ∧
        F.φ ⟨0, hn⟩ = s.phiPlus C E hE ∧ F.φ ⟨F.n - 1, by omega⟩ = s.phiMinus C E hE ∧
          ∀ i, s.phiMinus C E hE ≤ F.φ i ∧ F.φ i ≤ s.phiPlus C E hE := by
  obtain ⟨F, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hE
  have hp : F.φ ⟨0, hn⟩ = s.phiPlus C E hE := (s.phiPlus_eq C E hE F hn hfirst).symm
  have hm : F.φ ⟨F.n - 1, by omega⟩ = s.phiMinus C E hE := (s.phiMinus_eq C E hE F hn hlast).symm
  refine ⟨F, hn, hfirst, hlast, hp, hm, fun i => ?_⟩
  have := F.phase_mem_range C hn i
  exact ⟨hm ▸ this.1, hp ▸ this.2⟩

/-! ### (A): closed intervals through Hom vanishing -/

/-- **(A) of the short-step stability test.** `E ∈ P([l, r])` if and only if `Hom(P(> r), E) = 0`
and `Hom(E, P(< l)) = 0`. -/
theorem mem_closedInterval_iff (s : Slicing C) {l r : ℝ} {E : C} :
    (s.geProp C l E ∧ s.leProp C r E) ↔
      (∀ ⦃X : C⦄, s.gtProp C r X → ∀ f : X ⟶ E, f = 0) ∧
        (∀ ⦃Y : C⦄, s.ltProp C l Y → ∀ f : E ⟶ Y, f = 0) := by
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨fun X hX f => s.hom_eq_zero_of_gtProp_leProp hX hr f,
      fun Y hY f => s.hom_eq_zero_of_geProp_ltProp hl hY f⟩
  · rintro ⟨hr, hl⟩
    by_cases hE : IsZero E
    · exact ⟨Or.inl hE, Or.inl hE⟩
    constructor
    · refine s.geProp_of_le_phiMinus hE (not_lt.mp fun h => ?_)
      obtain ⟨F, hn, hne⟩ := s.exists_hn_nonzero_last C hE
      rw [s.phiMinus_eq C E hE F hn hne] at h
      exact hne (F.lastFactor_isZero_of_hom_eq_zero C s hn fun f =>
        hl (s.ltProp_of_semistable (F.semistable _) h) f)
    · refine s.leProp_of_phiPlus_le hE (not_lt.mp fun h => ?_)
      obtain ⟨F, hn, hne⟩ := s.exists_hn_nonzero_first C hE
      rw [s.phiPlus_eq C E hE F hn hne] at h
      exact hne (F.firstFactor_isZero_of_hom_eq_zero C s hn fun f =>
        hr (s.gtProp_of_semistable C (F.semistable _) h) f)

/-- An object receiving no nonzero map from `P(> t)` has all its phases at most `t`. -/
theorem leProp_of_hom_eq_zero (s : Slicing C) {t : ℝ} {E : C}
    (h : ∀ ⦃X : C⦄, s.gtProp C t X → ∀ f : X ⟶ E, f = 0) : s.leProp C t E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  refine s.leProp_of_phiPlus_le hE (not_lt.mp fun hlt => ?_)
  obtain ⟨F, hn, hne⟩ := s.exists_hn_nonzero_first C hE
  rw [s.phiPlus_eq C E hE F hn hne] at hlt
  exact hne (F.firstFactor_isZero_of_hom_eq_zero C s hn fun f =>
    h (s.gtProp_of_semistable C (F.semistable _) hlt) f)

/-- An object with no nonzero map to `P(< t)` has all its phases at least `t`. -/
theorem geProp_of_hom_eq_zero (s : Slicing C) {t : ℝ} {E : C}
    (h : ∀ ⦃Y : C⦄, s.ltProp C t Y → ∀ f : E ⟶ Y, f = 0) : s.geProp C t E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  refine s.geProp_of_le_phiMinus hE (not_lt.mp fun hlt => ?_)
  obtain ⟨F, hn, hne⟩ := s.exists_hn_nonzero_last C hE
  rw [s.phiMinus_eq C E hE F hn hne] at hlt
  exact hne (F.lastFactor_isZero_of_hom_eq_zero C s hn fun f =>
    h (s.ltProp_of_semistable (F.semistable _) hlt) f)

/-! ### Phase closeness -/

/-- The intrinsic phases of `τ` and `ν` differ by less than `ε` on every nonzero object. For
Bridgeland's metric this holds when the distance between the two stability conditions is less than
`ε` (arXiv:math/0212237, §8). -/
def PhaseClose (τ ν : Slicing C) (ε : ℝ) : Prop :=
  ∀ (E : C) (hE : ¬IsZero E), |ν.phiPlus C E hE - τ.phiPlus C E hE| < ε ∧
    |ν.phiMinus C E hE - τ.phiMinus C E hE| < ε

namespace PhaseClose

variable {τ ν : Slicing C} {ε : ℝ}

theorem symm (h : τ.PhaseClose ν ε) : ν.PhaseClose τ ε := fun E hE =>
  ⟨by rw [abs_sub_comm]; exact (h E hE).1, by rw [abs_sub_comm]; exact (h E hE).2⟩

theorem mono (h : τ.PhaseClose ν ε) {ε' : ℝ} (hε : ε ≤ ε') : τ.PhaseClose ν ε' := fun E hE =>
  ⟨(h E hE).1.trans_le hε, (h E hE).2.trans_le hε⟩

theorem pos (h : τ.PhaseClose ν ε) {E : C} (hE : ¬IsZero E) : 0 < ε :=
  (abs_nonneg _).trans_lt (h E hE).1

/-- Lower phase bounds move by less than `ε`. -/
theorem gtProp_of_geProp (h : τ.PhaseClose ν ε) {a : ℝ} {E : C} (hE : τ.geProp C a E) :
    ν.gtProp C (a - ε) E := by
  by_cases hz : IsZero E
  · exact Or.inl hz
  have h1 := τ.le_phiMinus_of_geProp hz hE
  have h2 := (abs_lt.mp (h E hz).2).1
  exact ν.gtProp_of_lt_phiMinus hz (by linarith)

/-- Upper phase bounds move by less than `ε`. -/
theorem ltProp_of_leProp (h : τ.PhaseClose ν ε) {b : ℝ} {E : C} (hE : τ.leProp C b E) :
    ν.ltProp C (b + ε) E := by
  by_cases hz : IsZero E
  · exact Or.inl hz
  have h1 := τ.phiPlus_le_of_leProp hz hE
  have h2 := (abs_lt.mp (h E hz).1).2
  exact ν.ltProp_of_phiPlus_lt hz (by linarith)

end PhaseClose

/-! ### Stable objects -/

/-- `Y` is **stable** of phase `φ`: it is nonzero and semistable of phase `φ`, and every
distinguished triangle `N → Y → Q → N[1]` with `N` and `Q` semistable of phase `φ` has `N = 0` or
`Q = 0`. These triangles are the short exact sequences of the abelian category `P(φ)`
(Bridgeland, arXiv:math/0212237, Lemma 5.2), so `Y` is a simple object of `P(φ)`. -/
def IsStable (s : Slicing C) (φ : ℝ) (Y : C) : Prop :=
  s.P φ Y ∧ ¬IsZero Y ∧ ∀ ⦃N Q : C⦄ (i : N ⟶ Y) (p : Y ⟶ Q) (δ : Q ⟶ N⟦(1 : ℤ)⟧),
    Triangle.mk i p δ ∈ distTriang C → s.P φ N → s.P φ Q → IsZero N ∨ IsZero Q

end Slicing

/-! ### The sign of `Im(e^{-iπφ} Z)` -/

namespace PreStabilityCondition.WithClassMap

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- `Im(e^{-iπφ} Z(E))`: positive when the charge of `E` lies strictly counterclockwise from the
ray of phase `φ`, within a half-turn. -/
def imPhase (σ : WithClassMap C v) (φ : ℝ) (E : C) : ℝ :=
  (Complex.exp (-(((Real.pi * φ : ℝ) : ℂ) * Complex.I)) * σ.charge E).im

/-- A charge `m e^{iπψ}` has `Im(e^{-iπφ} Z) = m sin π(ψ - φ)`. -/
theorem imPhase_of_charge_eq (σ : WithClassMap C v) (φ : ℝ) {E : C} {m ψ : ℝ}
    (h : σ.charge E = (m : ℂ) * Complex.exp ((Real.pi * ψ : ℝ) * Complex.I)) :
    σ.imPhase φ E = m * Real.sin (Real.pi * (ψ - φ)) := by
  have e : Complex.exp (-(((Real.pi * φ : ℝ) : ℂ) * Complex.I)) *
      ((m : ℂ) * Complex.exp ((Real.pi * ψ : ℝ) * Complex.I)) =
        (m : ℂ) * Complex.exp (((Real.pi * (ψ - φ) : ℝ) : ℂ) * Complex.I) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [imPhase, h, e, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- A semistable factor of phase `ψ` contributes `m sin π(ψ - φ)` with `m ≥ 0`, and `m > 0` when
it is nonzero. -/
theorem exists_imPhase_of_semistable (σ : WithClassMap C v) (φ : ℝ) {E : C} {ψ : ℝ}
    (hP : σ.slicing.P ψ E) :
    ∃ m : ℝ, 0 ≤ m ∧ (¬IsZero E → 0 < m) ∧
      σ.imPhase φ E = m * Real.sin (Real.pi * (ψ - φ)) := by
  by_cases hE : IsZero E
  · refine ⟨0, le_rfl, fun h => absurd hE h, ?_⟩
    simp [imPhase, charge_isZero σ hE]
  · obtain ⟨m, hm, hZ⟩ := σ.compat ψ E hP hE
    exact ⟨m, hm.le, fun _ => hm, σ.imPhase_of_charge_eq φ hZ⟩

theorem imPhase_iso (σ : WithClassMap C v) (φ : ℝ) {E E' : C} (e : E ≅ E') :
    σ.imPhase φ E = σ.imPhase φ E' := by
  simp only [imPhase, charge_def, classOf_iso C v e]

theorem imPhase_isZero (σ : WithClassMap C v) (φ : ℝ) {E : C} (hE : IsZero E) :
    σ.imPhase φ E = 0 := by
  simp [imPhase, charge_isZero σ hE]

/-- `Im(e^{-iπφ} Z)` is additive on distinguished triangles. -/
theorem imPhase_triangle (σ : WithClassMap C v) (φ : ℝ) (T : Triangle C)
    (hT : T ∈ distTriang C) :
    σ.imPhase φ T.obj₂ = σ.imPhase φ T.obj₁ + σ.imPhase φ T.obj₃ := by
  simp only [imPhase, charge_def, classOf_triangle C v T hT, map_add, mul_add, Complex.add_im]

/-- `Im(e^{-iπφ} Z)` is the sum over the factors of an HN filtration. -/
theorem imPhase_eq_sum (σ : WithClassMap C v) (φ : ℝ) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    σ.imPhase φ E = ∑ i, σ.imPhase φ (F.factor i) := by
  simp only [imPhase, σ.charge_postnikovTower_eq_sum F.toPostnikovTower, Finset.mul_sum,
    Complex.im_sum]

/-- A nonzero object with all phases in `(φ, φ + 1)` has `Im(e^{-iπφ} Z) > 0`. -/
theorem imPhase_pos (σ : WithClassMap C v) {φ : ℝ} {E : C} (hE : ¬IsZero E)
    (h₁ : σ.slicing.gtProp C φ E) (h₂ : σ.slicing.ltProp C (φ + 1) E) :
    0 < σ.imPhase φ E := by
  obtain ⟨F, hn, hfirst, -, -, -, hb⟩ := σ.slicing.exists_hn_phase_bounds hE
  have hlo := σ.slicing.lt_phiMinus_of_gtProp hE h₁
  have hhi := σ.slicing.phiPlus_lt_of_ltProp hE h₂
  have hterm : ∀ i, ∃ m : ℝ, 0 ≤ m ∧ (¬IsZero (F.factor i) → 0 < m) ∧
      σ.imPhase φ (F.factor i) = m * Real.sin (Real.pi * (F.φ i - φ)) ∧
        0 < Real.sin (Real.pi * (F.φ i - φ)) := fun i => by
    obtain ⟨m, hm, hmpos, he⟩ := σ.exists_imPhase_of_semistable φ (F.semistable i)
    refine ⟨m, hm, hmpos, he, Real.sin_pos_of_pos_of_lt_pi ?_ ?_⟩
    · have := (hb i).1; nlinarith [Real.pi_pos]
    · have := (hb i).2; nlinarith [Real.pi_pos]
  rw [σ.imPhase_eq_sum φ F]
  refine Finset.sum_pos' (fun i _ => ?_) ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
  · obtain ⟨m, hm, -, he, hs⟩ := hterm i
    rw [he]; positivity
  · obtain ⟨m, -, hmpos, he, hs⟩ := hterm ⟨0, hn⟩
    rw [he]; exact mul_pos (hmpos hfirst) hs

/-- An object with all phases in `(φ - 1, φ]` has `Im(e^{-iπφ} Z) ≤ 0`. -/
theorem imPhase_nonpos (σ : WithClassMap C v) {φ : ℝ} {E : C}
    (h₁ : σ.slicing.gtProp C (φ - 1) E) (h₂ : σ.slicing.leProp C φ E) :
    σ.imPhase φ E ≤ 0 := by
  by_cases hE : IsZero E
  · exact (σ.imPhase_isZero φ hE).le
  obtain ⟨F, hn, -, -, -, -, hb⟩ := σ.slicing.exists_hn_phase_bounds hE
  have hlo := σ.slicing.lt_phiMinus_of_gtProp hE h₁
  have hhi := σ.slicing.phiPlus_le_of_leProp hE h₂
  rw [σ.imPhase_eq_sum φ F]
  refine Finset.sum_nonpos fun i _ => ?_
  obtain ⟨m, hm, -, he⟩ := σ.exists_imPhase_of_semistable φ (F.semistable i)
  rw [he]
  refine mul_nonpos_of_nonneg_of_nonpos hm (Real.sin_nonpos_of_nonpos_of_neg_pi_le ?_ ?_)
  · have := (hb i).2; nlinarith [Real.pi_pos]
  · have := (hb i).1; nlinarith [Real.pi_pos]

/-- A nonzero object with all phases in `(φ - 1, φ)` has `Im(e^{-iπφ} Z) < 0`. -/
theorem imPhase_neg (σ : WithClassMap C v) {φ : ℝ} {E : C} (hE : ¬IsZero E)
    (h₁ : σ.slicing.gtProp C (φ - 1) E) (h₂ : σ.slicing.ltProp C φ E) :
    σ.imPhase φ E < 0 := by
  obtain ⟨F, hn, hfirst, -, -, -, hb⟩ := σ.slicing.exists_hn_phase_bounds hE
  have hlo := σ.slicing.lt_phiMinus_of_gtProp hE h₁
  have hhi := σ.slicing.phiPlus_lt_of_ltProp hE h₂
  have hterm : ∀ i, ∃ m : ℝ, 0 ≤ m ∧ (¬IsZero (F.factor i) → 0 < m) ∧
      σ.imPhase φ (F.factor i) = m * Real.sin (Real.pi * (F.φ i - φ)) ∧
        Real.sin (Real.pi * (F.φ i - φ)) < 0 := fun i => by
    obtain ⟨m, hm, hmpos, he⟩ := σ.exists_imPhase_of_semistable φ (F.semistable i)
    refine ⟨m, hm, hmpos, he, Real.sin_neg_of_neg_of_neg_pi_lt ?_ ?_⟩
    · have := (hb i).2; nlinarith [Real.pi_pos]
    · have := (hb i).1; nlinarith [Real.pi_pos]
  rw [σ.imPhase_eq_sum φ F]
  refine Finset.sum_neg' (fun i _ => ?_) ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
  · obtain ⟨m, hm, -, he, hs⟩ := hterm i
    rw [he]; exact mul_nonpos_of_nonneg_of_nonpos hm hs.le
  · obtain ⟨m, -, hmpos, he, hs⟩ := hterm ⟨0, hn⟩
    rw [he]; exact mul_neg_of_pos_of_neg (hmpos hfirst) hs

/-- A nonzero object with all phases in `(φ - 1, φ]` and `Im(e^{-iπφ} Z) = 0` is semistable of
phase `φ`. -/
theorem semistable_of_imPhase_eq_zero (σ : WithClassMap C v) {φ : ℝ} {E : C} (hE : ¬IsZero E)
    (h₁ : σ.slicing.gtProp C (φ - 1) E) (h₂ : σ.slicing.leProp C φ E)
    (h₀ : σ.imPhase φ E = 0) : σ.slicing.P φ E := by
  obtain ⟨F, hn, -, hlast, -, hm, hb⟩ := σ.slicing.exists_hn_phase_bounds hE
  have hlo := σ.slicing.lt_phiMinus_of_gtProp hE h₁
  have hhi := σ.slicing.phiPlus_le_of_leProp hE h₂
  have hnonpos : ∀ i ∈ Finset.univ, σ.imPhase φ (F.factor i) ≤ 0 := fun i _ => by
    obtain ⟨m, hm, -, he⟩ := σ.exists_imPhase_of_semistable φ (F.semistable i)
    rw [he]
    refine mul_nonpos_of_nonneg_of_nonpos hm (Real.sin_nonpos_of_nonpos_of_neg_pi_le ?_ ?_)
    · have := (hb i).2; nlinarith [Real.pi_pos]
    · have := (hb i).1; nlinarith [Real.pi_pos]
  rw [σ.imPhase_eq_sum φ F] at h₀
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp h₀ ⟨F.n - 1, by omega⟩
    (Finset.mem_univ _)
  obtain ⟨m, -, hmpos, he⟩ := σ.exists_imPhase_of_semistable φ (F.semistable ⟨F.n - 1, by omega⟩)
  rw [he] at hzero
  have hsin : Real.sin (Real.pi * (F.φ ⟨F.n - 1, by omega⟩ - φ)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (hmpos hlast).ne'
  rw [hm] at hsin
  have hx : Real.pi * (σ.slicing.phiMinus C E hE - φ) = 0 := by
    refine (Real.sin_eq_zero_iff_of_lt_of_lt ?_ ?_).mp hsin
    · nlinarith [Real.pi_pos]
    · have := σ.slicing.phiMinus_le_phiPlus C E hE; nlinarith [Real.pi_pos]
  have hφ : σ.slicing.phiMinus C E hE = φ := by
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h Real.pi_ne_zero
    · linarith
  exact σ.slicing.semistable_of_phiPlus_le_of_le_phiMinus hE hhi hφ.ge

/-- A nonzero object with all phases in `[φ, φ + 1)` and `Im(e^{-iπφ} Z) = 0` is semistable of
phase `φ`. -/
theorem semistable_of_imPhase_eq_zero' (σ : WithClassMap C v) {φ : ℝ} {E : C} (hE : ¬IsZero E)
    (h₁ : σ.slicing.geProp C φ E) (h₂ : σ.slicing.ltProp C (φ + 1) E)
    (h₀ : σ.imPhase φ E = 0) : σ.slicing.P φ E := by
  obtain ⟨F, hn, hfirst, -, hp, -, hb⟩ := σ.slicing.exists_hn_phase_bounds hE
  have hlo := σ.slicing.le_phiMinus_of_geProp hE h₁
  have hhi := σ.slicing.phiPlus_lt_of_ltProp hE h₂
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ σ.imPhase φ (F.factor i) := fun i _ => by
    obtain ⟨m, hm, -, he⟩ := σ.exists_imPhase_of_semistable φ (F.semistable i)
    rw [he]
    refine mul_nonneg hm (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
    · have := (hb i).1; nlinarith [Real.pi_pos]
    · have := (hb i).2; nlinarith [Real.pi_pos]
  rw [σ.imPhase_eq_sum φ F] at h₀
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h₀ ⟨0, hn⟩ (Finset.mem_univ _)
  obtain ⟨m, -, hmpos, he⟩ := σ.exists_imPhase_of_semistable φ (F.semistable ⟨0, hn⟩)
  rw [he] at hzero
  have hsin : Real.sin (Real.pi * (F.φ ⟨0, hn⟩ - φ)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (hmpos hfirst).ne'
  rw [hp] at hsin
  have hx : Real.pi * (σ.slicing.phiPlus C E hE - φ) = 0 := by
    refine (Real.sin_eq_zero_iff_of_lt_of_lt ?_ ?_).mp hsin
    · have := σ.slicing.phiMinus_le_phiPlus C E hE; nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hφ : σ.slicing.phiPlus C E hE = φ := by
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h Real.pi_ne_zero
    · linarith
  exact σ.slicing.semistable_of_phiPlus_le_of_le_phiMinus hE hφ.le hlo

end PreStabilityCondition.WithClassMap

/-! ### (B): the Im-form test -/

namespace Slicing

open PreStabilityCondition.WithClassMap

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Truncation at `t` of an object with phases in `(a, b)`: both pieces keep the outer bound. -/
theorem exists_split_of_bounds [IsTriangulated C] (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {a b : ℝ} (ha : s.gtProp C a E) (hb : s.ltProp C b E) (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ s.gtProp C t X ∧ s.ltProp C b X ∧
        s.leProp C t Y ∧ s.gtProp C a Y := by
  obtain ⟨F, hn, -, -, hp, hm, hbd⟩ := s.exists_hn_phase_bounds hE
  have hlo := s.lt_phiMinus_of_gtProp hE ha
  have hhi := s.phiPlus_lt_of_ltProp hE hb
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, hGYlo, hGXorig⟩ := F.exists_split_at_cutoff C t
  refine ⟨X, Y, f, g, h, hT, ?_, ?_, ?_, ?_⟩
  · by_cases hX : 0 < GX.n
    · exact s.gtProp_of_hn C GX t hGX hX
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  · by_cases hX : 0 < GX.n
    · refine s.ltProp_of_hn C GX b (fun j => ?_) hX
      obtain ⟨i, hi⟩ := hGXorig j
      rw [hi]; linarith [(hbd i).2]
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  · by_cases hY : 0 < GY.n
    · exact s.leProp_of_hn C GY t hGY hY
    · exact Or.inl (GY.isZero_of_length_zero (by omega))
  · by_cases hY : 0 < GY.n
    · refine s.gtProp_of_hn C GY a (fun j => ?_) hY
      have := hGYlo hn j
      rw [hm] at this; linarith
    · exact Or.inl (GY.isZero_of_length_zero (by omega))

variable (τ : Slicing C) (σ : PreStabilityCondition.WithClassMap C v)

/-- In a triangle `N → Y → Q → N[1]` with `Y ∈ P_ν(φ)` and `Q[-1] ∈ P_ν(≤ φ)`, the subobject `N`
has all its `ν`-phases at most `φ`. -/
theorem leProp_of_triangle_of_semistable {φ : ℝ} {N Y Q : C} {i : N ⟶ Y} {p : Y ⟶ Q}
    {δ : Q ⟶ N⟦(1 : ℤ)⟧} (hT : Triangle.mk i p δ ∈ distTriang C) (s : Slicing C)
    (hY : s.P φ Y) (hQ : s.leProp C φ (Q⟦(-1 : ℤ)⟧)) : s.leProp C φ N := by
  refine s.leProp_of_hom_eq_zero fun X hX f => ?_
  have hfi : f ≫ i = 0 := s.hom_eq_zero_of_gtProp_leProp hX (s.leProp_of_semistable C hY le_rfl) _
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) f hfi
  have hg0 : g = 0 := s.hom_eq_zero_of_gtProp_leProp hX hQ g
  rw [hg, hg0]
  exact zero_comp

/-- In a triangle `N → Y → Q → N[1]` with `Y ∈ P_ν(φ)` and `N[1] ∈ P_ν(> φ)`, the quotient `Q`
has all its `ν`-phases at least `φ`. -/
theorem geProp_of_triangle_of_semistable {φ : ℝ} {N Y Q : C} {i : N ⟶ Y} {p : Y ⟶ Q}
    {δ : Q ⟶ N⟦(1 : ℤ)⟧} (hT : Triangle.mk i p δ ∈ distTriang C) (s : Slicing C)
    (hY : s.P φ Y) (hN : s.gtProp C φ (N⟦(1 : ℤ)⟧)) : s.geProp C φ Q := by
  refine s.geProp_of_hom_eq_zero fun Z hZ f => ?_
  have hpf : p ≫ f = 0 := s.hom_eq_zero_of_geProp_ltProp (s.geProp_of_semistable C hY) hZ _
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hT f hpf
  have hg0 : g = 0 := s.hom_eq_zero_of_gtProp_leProp hN (s.leProp_of_ltProp C _ hZ) g
  rw [hg, hg0]
  exact comp_zero

/-- The charge of `Y` on the ray of phase `φ` makes `Y` nonzero with `Im(e^{-iπφ} Z(Y)) = 0`. -/
private theorem ray_facts {φ r : ℝ} (hr : 0 < r) {Y : C}
    (hY : σ.charge Y = (r : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I)) :
    ¬IsZero Y ∧ σ.imPhase φ Y = 0 := by
  refine ⟨fun hz => ?_, ?_⟩
  · rw [charge_isZero σ hz] at hY
    have := congrArg (‖·‖) hY
    simp only [norm_zero, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs] at this
    linarith [abs_pos.mpr hr.ne']
  · rw [σ.imPhase_of_charge_eq φ hY, sub_self, mul_zero, Real.sin_zero, mul_zero]

/-- The `ν`-bounds of the two ends of a triangle of the Im-form test. -/
private theorem triangle_bounds {ε : ℝ} (hε : ε ≤ 1 / 4) (hclose : τ.PhaseClose σ.slicing ε)
    {φ : ℝ} {E : C} (hE : τ.geProp C (φ - 3 * ε) E ∧ τ.leProp C (φ + 3 * ε) E) :
    σ.slicing.gtProp C (φ - 1) E ∧ σ.slicing.ltProp C (φ + 1) E := by
  refine ⟨σ.slicing.gtProp_anti C (show φ - 1 ≤ φ - 3 * ε - ε by linarith) _
    (hclose.gtProp_of_geProp hE.1), σ.slicing.ltProp_mono C
      (show φ + 3 * ε + ε ≤ φ + 1 by linarith) _ (hclose.ltProp_of_leProp hE.2)⟩

/-- **The short-step stability test, (B).** Let `τ` and `ν` be slicings whose intrinsic phases
differ by less than `ε ≤ 1/4`, and `Z` a central charge compatible with `ν`. An object `Y` with
`Z(Y) ∈ ℝ_{>0} e^{iπφ}` is `ν`-semistable of phase `φ` if and only if `Y ∈ P_τ([φ - ε, φ + ε])`
and no distinguished triangle `N → Y → Q → N[1]` with `N, Q ≠ 0` in `P_τ([φ - 3ε, φ + 3ε])` has
`Im(e^{-iπφ} Z(N)) > 0`. -/
theorem semistable_iff_imPhase [IsTriangulated C] {ε : ℝ} (hε : ε ≤ 1 / 4)
    (hclose : τ.PhaseClose σ.slicing ε) {φ r : ℝ} (hr : 0 < r) {Y : C}
    (hY : σ.charge Y = (r : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I)) :
    σ.slicing.P φ Y ↔ (τ.geProp C (φ - ε) Y ∧ τ.leProp C (φ + ε) Y) ∧
      ∀ ⦃N Q : C⦄ (i : N ⟶ Y) (p : Y ⟶ Q) (δ : Q ⟶ N⟦(1 : ℤ)⟧),
        Triangle.mk i p δ ∈ distTriang C → ¬IsZero N → ¬IsZero Q →
          (τ.geProp C (φ - 3 * ε) N ∧ τ.leProp C (φ + 3 * ε) N) →
          (τ.geProp C (φ - 3 * ε) Q ∧ τ.leProp C (φ + 3 * ε) Q) →
            σ.imPhase φ N ≤ 0 := by
  obtain ⟨hYnz, hYim⟩ := ray_facts σ hr hY
  have hε0 : 0 < ε := hclose.pos hYnz
  constructor
  · intro hP
    obtain ⟨hp, hm⟩ := σ.slicing.phiPlus_eq_phiMinus_of_semistable hYnz hP
    obtain ⟨h1, h2⟩ := hclose Y hYnz
    rw [hp, abs_lt] at h1
    rw [hm, abs_lt] at h2
    refine ⟨⟨τ.geProp_of_le_phiMinus hYnz (by linarith),
      τ.leProp_of_phiPlus_le hYnz (by linarith)⟩, ?_⟩
    intro N Q i p δ hT _ _ hN hQ
    have hNb := triangle_bounds τ σ hε hclose hN
    have hQb := triangle_bounds τ σ hε hclose hQ
    have hQ' : σ.slicing.leProp C φ (Q⟦(-1 : ℤ)⟧) := by
      have := σ.slicing.ltProp_shift C (φ + 1) Q (-1) hQb.2
      rw [show φ + 1 + ((-1 : ℤ) : ℝ) = φ by push_cast; ring] at this
      exact σ.slicing.leProp_of_ltProp C _ this
    exact σ.imPhase_nonpos hNb.1
      (leProp_of_triangle_of_semistable hT σ.slicing hP hQ')
  · rintro ⟨⟨hge, hle⟩, htri⟩
    have hgt : σ.slicing.gtProp C (φ - ε - ε) Y := hclose.gtProp_of_geProp hge
    have hlt : σ.slicing.ltProp C (φ + ε + ε) Y := hclose.ltProp_of_leProp hle
    -- first, `φ⁺_ν(Y) ≤ φ`
    have hYle : σ.slicing.leProp C φ Y := by
      refine σ.slicing.leProp_of_phiPlus_le hYnz (not_lt.mp fun hlt' => ?_)
      obtain ⟨X, Y', f, g, h, hT, hX₁, hX₂, hY₁, hY₂⟩ :=
        σ.slicing.exists_split_of_bounds hYnz hgt hlt φ
      have hXnz : ¬IsZero X := fun hX => by
        have : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ hT).mp hX
        have hYle' : σ.slicing.leProp C φ Y :=
          (σ.slicing.leProp C φ).prop_of_iso (asIso g).symm hY₁
        exact absurd (σ.slicing.phiPlus_le_of_leProp hYnz hYle') (not_le.mpr hlt')
      have hXpos : 0 < σ.imPhase φ X := σ.imPhase_pos hXnz hX₁
        (σ.slicing.ltProp_mono C (show φ + ε + ε ≤ φ + 1 by linarith) _ hX₂)
      by_cases hY'z : IsZero Y'
      · have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hY'z
        rw [σ.imPhase_iso φ (asIso f)] at hXpos
        linarith
      · have hsym := hclose.symm
        have hXτ : τ.geProp C (φ - 3 * ε) X ∧ τ.leProp C (φ + 3 * ε) X := by
          refine ⟨τ.geProp_anti C (show φ - 3 * ε ≤ φ - ε by linarith) _
            (τ.geProp_of_gtProp C _ (hsym.gtProp_of_geProp (σ.slicing.geProp_of_gtProp C _ hX₁))),
            τ.leProp_mono C (show φ + ε + ε + ε ≤ φ + 3 * ε by linarith) _
              (τ.leProp_of_ltProp C _ (hsym.ltProp_of_leProp
                (σ.slicing.leProp_of_ltProp C _ hX₂)))⟩
        have hY'τ : τ.geProp C (φ - 3 * ε) Y' ∧ τ.leProp C (φ + 3 * ε) Y' := by
          refine ⟨τ.geProp_anti C (show φ - 3 * ε ≤ φ - ε - ε - ε by linarith) _
            (τ.geProp_of_gtProp C _ (hsym.gtProp_of_geProp
              (σ.slicing.geProp_of_gtProp C _ hY₂))),
            τ.leProp_mono C (show φ + ε ≤ φ + 3 * ε by linarith) _
              (τ.leProp_of_ltProp C _ (hsym.ltProp_of_leProp hY₁))⟩
        have := htri f g h hT hXnz hY'z hXτ hY'τ
        linarith
    exact σ.semistable_of_imPhase_eq_zero hYnz
      (σ.slicing.gtProp_anti C (show φ - 1 ≤ φ - ε - ε by linarith) _ hgt) hYle hYim

/-- **The short-step stability test for stable objects.** Under the hypotheses of
`semistable_iff_imPhase`, `Y` is `ν`-stable of phase `φ` if and only if
`Y ∈ P_τ([φ - ε, φ + ε])` and every distinguished triangle `N → Y → Q → N[1]` with `N, Q ≠ 0` in
`P_τ([φ - 3ε, φ + 3ε])` has `Im(e^{-iπφ} Z(N)) < 0`. -/
theorem isStable_iff_imPhase [IsTriangulated C] {ε : ℝ} (hε : ε ≤ 1 / 4)
    (hclose : τ.PhaseClose σ.slicing ε) {φ r : ℝ} (hr : 0 < r) {Y : C}
    (hY : σ.charge Y = (r : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I)) :
    σ.slicing.IsStable φ Y ↔ (τ.geProp C (φ - ε) Y ∧ τ.leProp C (φ + ε) Y) ∧
      ∀ ⦃N Q : C⦄ (i : N ⟶ Y) (p : Y ⟶ Q) (δ : Q ⟶ N⟦(1 : ℤ)⟧),
        Triangle.mk i p δ ∈ distTriang C → ¬IsZero N → ¬IsZero Q →
          (τ.geProp C (φ - 3 * ε) N ∧ τ.leProp C (φ + 3 * ε) N) →
          (τ.geProp C (φ - 3 * ε) Q ∧ τ.leProp C (φ + 3 * ε) Q) →
            σ.imPhase φ N < 0 := by
  obtain ⟨hYnz, hYim⟩ := ray_facts σ hr hY
  have hε0 : 0 < ε := hclose.pos hYnz
  have hss := τ.semistable_iff_imPhase σ hε hclose hr hY
  constructor
  · rintro ⟨hP, -, hsimple⟩
    obtain ⟨hbd, hle⟩ := hss.mp hP
    refine ⟨hbd, fun N Q i p δ hT hN hQ hNτ hQτ => ?_⟩
    refine lt_of_le_of_ne (hle i p δ hT hN hQ hNτ hQτ) fun h0 => ?_
    have hNb := triangle_bounds τ σ hε hclose hNτ
    have hQb := triangle_bounds τ σ hε hclose hQτ
    have hQ' : σ.slicing.leProp C φ (Q⟦(-1 : ℤ)⟧) := by
      have := σ.slicing.ltProp_shift C (φ + 1) Q (-1) hQb.2
      rw [show φ + 1 + ((-1 : ℤ) : ℝ) = φ by push_cast; ring] at this
      exact σ.slicing.leProp_of_ltProp C _ this
    have hN' : σ.slicing.gtProp C φ (N⟦(1 : ℤ)⟧) := by
      have := σ.slicing.gtProp_shift C (φ - 1) N 1 hNb.1
      rwa [show φ - 1 + ((1 : ℤ) : ℝ) = φ by push_cast; ring] at this
    have hNP : σ.slicing.P φ N := σ.semistable_of_imPhase_eq_zero hN hNb.1
      (leProp_of_triangle_of_semistable hT σ.slicing hP hQ') h0
    have hQim : σ.imPhase φ Q = 0 := by
      have := σ.imPhase_triangle φ _ hT
      simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at this
      linarith
    have hQP : σ.slicing.P φ Q := σ.semistable_of_imPhase_eq_zero' hQ
      (geProp_of_triangle_of_semistable hT σ.slicing hP hN') hQb.2 hQim
    rcases hsimple i p δ hT hNP hQP with h | h
    · exact hN h
    · exact hQ h
  · rintro ⟨hbd, hneg⟩
    have hP : σ.slicing.P φ Y :=
      hss.mpr ⟨hbd, fun N Q i p δ hT hN hQ hNτ hQτ => (hneg i p δ hT hN hQ hNτ hQτ).le⟩
    refine ⟨hP, hYnz, fun N Q i p δ hT hNP hQP => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hN, hQ⟩ := hcon
    have hτ : ∀ {E : C}, ¬IsZero E → σ.slicing.P φ E →
        τ.geProp C (φ - 3 * ε) E ∧ τ.leProp C (φ + 3 * ε) E := fun {E} hE hEP => by
      obtain ⟨hp, hm⟩ := σ.slicing.phiPlus_eq_phiMinus_of_semistable hE hEP
      obtain ⟨h1, h2⟩ := hclose E hE
      rw [hp, abs_lt] at h1
      rw [hm, abs_lt] at h2
      exact ⟨τ.geProp_of_le_phiMinus hE (by linarith),
        τ.leProp_of_phiPlus_le hE (by linarith)⟩
    have h0 := hneg i p δ hT hN hQ (hτ hN hNP) (hτ hQ hQP)
    obtain ⟨m, -, -, he⟩ := σ.exists_imPhase_of_semistable φ hNP
    rw [he, sub_self, mul_zero, Real.sin_zero, mul_zero] at h0
    exact lt_irrefl _ h0

end Slicing

end CategoryTheory.Triangulated
