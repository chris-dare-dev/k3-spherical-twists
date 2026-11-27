/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.StabilitySpace

/-!
# Transport along a path, node by node

A path of stability conditions is cut into nodes `σ_0, σ_1, …, σ_N` whose consecutive slicings are
`ε`-close (`StabilitySpaceHypotheses.exists_subdivision_phaseClose`). Instead of listing the walls
crossed between two nodes and crossing them one at a time, stability at each node is decided by the
short-step stability test (`Slicing.semistable_iff_imPhase`, `Slicing.isStable_iff_imPhase`) from
the slicing of the previous node and the charge of the next one. The transport is an induction on
the nodes, and no wall between two nodes is named.

The phases of an object `Y` along the nodes are given through its charges:
`Z_{σ_k}(Y) = r_k e^{iπφ_k}` with `r_k > 0`, where the lift `φ_k` moves by at most `ε` from one
node to the next. This is a condition on charges only, not on slicings.

## Main results

* `PreStabilityCondition.WithClassMap.semistable_nodes_iff`: for nodes with `ε`-close consecutive
  slicings, `ε ≤ 1/4`, `Y` is semistable of phase `φ_k` at every node if and only if it is at the
  first node and, at every step, no distinguished triangle `N → Y → Q → N[1]` with `N, Q ≠ 0` in
  `P_{σ_k}([φ_{k+1} - 3ε, φ_{k+1} + 3ε])` has `Im(e^{-iπφ_{k+1}} Z_{σ_{k+1}}(N)) > 0`.
* `PreStabilityCondition.WithClassMap.isStable_nodes_iff`: the same for stable objects, with
  `Im(e^{-iπφ_{k+1}} Z_{σ_{k+1}}(N)) ≥ 0` excluded.
* `StabilitySpaceHypotheses.exists_nodes_semistable_iff`,
  `StabilitySpaceHypotheses.exists_nodes_isStable_iff`: along a path `γ` continuous on `[0, 1]` in
  a space of stability conditions, one subdivision `γ(k/N)` serves every object at once; its last
  node is `γ(1)`.

## Tags

stability condition, path, short-step stability test, semistable object, wall crossing
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- An object semistable of phase `φ` lies in `P([φ' - ε, φ' + ε])` for `|φ' - φ| ≤ ε`. -/
theorem Slicing.mem_closedInterval_of_semistable (s : Slicing C) {φ φ' ε : ℝ} {Y : C}
    (hY : s.P φ Y) (h : |φ' - φ| ≤ ε) : s.geProp C (φ' - ε) Y ∧ s.leProp C (φ' + ε) Y := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp h
  exact ⟨s.geProp_anti C (by linarith) _ (s.geProp_of_semistable C hY),
    s.leProp_of_semistable C hY (by linarith)⟩

namespace PreStabilityCondition.WithClassMap

/-- **Semistability along the nodes of a path, by induction on the nodes.** Let `σ_0, …, σ_N` be
prestability conditions whose consecutive slicings are `ε`-close, `ε ≤ 1/4`, and let the charges of
`Y` be `Z_{σ_k}(Y) = r_k e^{iπφ_k}` with `r_k > 0` and `|φ_{k+1} - φ_k| ≤ ε`. Then `Y` is
semistable of phase `φ_k` at every node if and only if it is semistable of phase `φ_0` at the first
node and, at every step `k → k + 1`, every distinguished triangle `N → Y → Q → N[1]` with `N, Q ≠ 0`
in `P_{σ_k}([φ_{k+1} - 3ε, φ_{k+1} + 3ε])` has `Im(e^{-iπφ_{k+1}} Z_{σ_{k+1}}(N)) ≤ 0`. Each step is
the short-step stability test (`Slicing.semistable_iff_imPhase`) at the node `σ_{k+1}`, read from
the slicing of `σ_k`; no wall between the nodes is named. -/
theorem semistable_nodes_iff [IsTriangulated C] (σ : ℕ → WithClassMap C v) {N : ℕ} {ε : ℝ}
    (hε : ε ≤ 1 / 4) (hclose : ∀ k < N, (σ k).slicing.PhaseClose (σ (k + 1)).slicing ε)
    {Y : C} {φ r : ℕ → ℝ} (hr : ∀ k ≤ N, 0 < r k)
    (hZ : ∀ k ≤ N,
      (σ k).charge Y = (r k : ℂ) * Complex.exp ((Real.pi * φ k : ℝ) * Complex.I))
    (hφ : ∀ k < N, |φ (k + 1) - φ k| ≤ ε) :
    (∀ k ≤ N, (σ k).slicing.P (φ k) Y) ↔ (σ 0).slicing.P (φ 0) Y ∧
      ∀ k < N, ∀ ⦃M Q : C⦄ (i : M ⟶ Y) (p : Y ⟶ Q) (δ : Q ⟶ M⟦(1 : ℤ)⟧),
        Triangle.mk i p δ ∈ distTriang C → ¬IsZero M → ¬IsZero Q →
          ((σ k).slicing.geProp C (φ (k + 1) - 3 * ε) M ∧
            (σ k).slicing.leProp C (φ (k + 1) + 3 * ε) M) →
          ((σ k).slicing.geProp C (φ (k + 1) - 3 * ε) Q ∧
            (σ k).slicing.leProp C (φ (k + 1) + 3 * ε) Q) →
            (σ (k + 1)).imPhase (φ (k + 1)) M ≤ 0 := by
  constructor
  · intro h
    refine ⟨h 0 (Nat.zero_le _), fun k hk => ?_⟩
    exact (((σ k).slicing.semistable_iff_imPhase (σ (k + 1)) hε (hclose k hk) (hr (k + 1) hk)
      (hZ (k + 1) hk)).mp (h (k + 1) hk)).2
  · rintro ⟨h0, hstep⟩ k hk
    induction k with
    | zero => exact h0
    | succ k ih =>
      have hk' : k < N := by omega
      exact ((σ k).slicing.semistable_iff_imPhase (σ (k + 1)) hε (hclose k hk') (hr (k + 1) hk)
        (hZ (k + 1) hk)).mpr
          ⟨(σ k).slicing.mem_closedInterval_of_semistable (ih hk'.le) (hφ k hk'), hstep k hk'⟩

/-- **Stability along the nodes of a path, by induction on the nodes.** In the setting of
`semistable_nodes_iff`, `Y` is stable of phase `φ_k` at every node if and only if it is stable of
phase `φ_0` at the first node and, at every step `k → k + 1`, every distinguished triangle
`N → Y → Q → N[1]` with `N, Q ≠ 0` in `P_{σ_k}([φ_{k+1} - 3ε, φ_{k+1} + 3ε])` has
`Im(e^{-iπφ_{k+1}} Z_{σ_{k+1}}(N)) < 0` (`Slicing.isStable_iff_imPhase`). -/
theorem isStable_nodes_iff [IsTriangulated C] (σ : ℕ → WithClassMap C v) {N : ℕ} {ε : ℝ}
    (hε : ε ≤ 1 / 4) (hclose : ∀ k < N, (σ k).slicing.PhaseClose (σ (k + 1)).slicing ε)
    {Y : C} {φ r : ℕ → ℝ} (hr : ∀ k ≤ N, 0 < r k)
    (hZ : ∀ k ≤ N,
      (σ k).charge Y = (r k : ℂ) * Complex.exp ((Real.pi * φ k : ℝ) * Complex.I))
    (hφ : ∀ k < N, |φ (k + 1) - φ k| ≤ ε) :
    (∀ k ≤ N, (σ k).slicing.IsStable (φ k) Y) ↔ (σ 0).slicing.IsStable (φ 0) Y ∧
      ∀ k < N, ∀ ⦃M Q : C⦄ (i : M ⟶ Y) (p : Y ⟶ Q) (δ : Q ⟶ M⟦(1 : ℤ)⟧),
        Triangle.mk i p δ ∈ distTriang C → ¬IsZero M → ¬IsZero Q →
          ((σ k).slicing.geProp C (φ (k + 1) - 3 * ε) M ∧
            (σ k).slicing.leProp C (φ (k + 1) + 3 * ε) M) →
          ((σ k).slicing.geProp C (φ (k + 1) - 3 * ε) Q ∧
            (σ k).slicing.leProp C (φ (k + 1) + 3 * ε) Q) →
            (σ (k + 1)).imPhase (φ (k + 1)) M < 0 := by
  constructor
  · intro h
    refine ⟨h 0 (Nat.zero_le _), fun k hk => ?_⟩
    exact (((σ k).slicing.isStable_iff_imPhase (σ (k + 1)) hε (hclose k hk) (hr (k + 1) hk)
      (hZ (k + 1) hk)).mp (h (k + 1) hk)).2
  · rintro ⟨h0, hstep⟩ k hk
    induction k with
    | zero => exact h0
    | succ k ih =>
      have hk' : k < N := by omega
      exact ((σ k).slicing.isStable_iff_imPhase (σ (k + 1)) hε (hclose k hk') (hr (k + 1) hk)
        (hZ (k + 1) hk)).mpr
          ⟨(σ k).slicing.mem_closedInterval_of_semistable (ih hk'.le).1 (hφ k hk'),
            hstep k hk'⟩

end PreStabilityCondition.WithClassMap

namespace StabilitySpaceHypotheses

variable {Stab : Type*} [PseudoMetricSpace Stab] {Γ : Type*} [Group Γ] [MulAction Γ Stab]
  (I : StabilitySpaceHypotheses C v Stab Γ)

/-- The nodes `γ(k/N)` of a subdivision have `ε`-close consecutive slicings. -/
private theorem phaseClose_nodes {γ : ℝ → Stab} {N : ℕ} {ε : ℝ}
    (h : ∀ k < N, (I.cond (γ (k / N))).slicing.PhaseClose (I.cond (γ ((k + 1) / N))).slicing ε) :
    ∀ k < N, (I.cond (γ ((k : ℕ) / N))).slicing.PhaseClose
      (I.cond (γ (((k + 1 : ℕ) : ℝ) / N))).slicing ε := fun k hk => by
  rw [Nat.cast_succ]
  exact h k hk

/-- **Semistability along a path, node by node.** For a path `γ` continuous on `[0, 1]` in a space
of stability conditions and `0 < ε ≤ 1/4`, there is one subdivision into nodes `γ(k/N)`, `N > 0`,
with `ε`-close consecutive slicings (`exists_subdivision_phaseClose`), such that for every object
`Y` whose charges at the nodes are `r_k e^{iπφ_k}`, `r_k > 0`, with `|φ_{k+1} - φ_k| ≤ ε`: `Y` is
semistable of phase `φ_k` at every node, the last being `γ(1)`, if and only if it is at `γ(0)` and
no step destabilizes it in the Im form of the short-step test (`semistable_nodes_iff`). -/
theorem exists_nodes_semistable_iff [IsTriangulated C] (γ : ℝ → Stab)
    (hγ : ContinuousOn γ (Set.Icc 0 1)) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 4) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) / N = 1 ∧ ∀ (Y : C) (φ r : ℕ → ℝ), (∀ k ≤ N, 0 < r k) →
      (∀ k ≤ N, (I.cond (γ ((k : ℕ) / N))).charge Y =
        (r k : ℂ) * Complex.exp ((Real.pi * φ k : ℝ) * Complex.I)) →
      (∀ k < N, |φ (k + 1) - φ k| ≤ ε) →
      ((∀ k ≤ N, (I.cond (γ ((k : ℕ) / N))).slicing.P (φ k) Y) ↔
        (I.cond (γ 0)).slicing.P (φ 0) Y ∧
          ∀ k < N, ∀ ⦃M Q : C⦄ (i : M ⟶ Y) (p : Y ⟶ Q) (δ : Q ⟶ M⟦(1 : ℤ)⟧),
            Triangle.mk i p δ ∈ distTriang C → ¬IsZero M → ¬IsZero Q →
              ((I.cond (γ ((k : ℕ) / N))).slicing.geProp C (φ (k + 1) - 3 * ε) M ∧
                (I.cond (γ ((k : ℕ) / N))).slicing.leProp C (φ (k + 1) + 3 * ε) M) →
              ((I.cond (γ ((k : ℕ) / N))).slicing.geProp C (φ (k + 1) - 3 * ε) Q ∧
                (I.cond (γ ((k : ℕ) / N))).slicing.leProp C (φ (k + 1) + 3 * ε) Q) →
                (I.cond (γ (((k + 1 : ℕ) : ℝ) / N))).imPhase (φ (k + 1)) M ≤ 0) := by
  obtain ⟨N, hN, hclose⟩ := I.exists_subdivision_phaseClose γ hγ hε0
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨N, hN, div_self hN', fun Y φ r hr hZ hφ => ?_⟩
  have h := PreStabilityCondition.WithClassMap.semistable_nodes_iff
    (fun k : ℕ => I.cond (γ ((k : ℕ) / N))) hε (I.phaseClose_nodes hclose) hr hZ hφ
  simpa using h

/-- **Stability along a path, node by node.** The stable form of `exists_nodes_semistable_iff`,
from `isStable_nodes_iff`. -/
theorem exists_nodes_isStable_iff [IsTriangulated C] (γ : ℝ → Stab)
    (hγ : ContinuousOn γ (Set.Icc 0 1)) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 4) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) / N = 1 ∧ ∀ (Y : C) (φ r : ℕ → ℝ), (∀ k ≤ N, 0 < r k) →
      (∀ k ≤ N, (I.cond (γ ((k : ℕ) / N))).charge Y =
        (r k : ℂ) * Complex.exp ((Real.pi * φ k : ℝ) * Complex.I)) →
      (∀ k < N, |φ (k + 1) - φ k| ≤ ε) →
      ((∀ k ≤ N, (I.cond (γ ((k : ℕ) / N))).slicing.IsStable (φ k) Y) ↔
        (I.cond (γ 0)).slicing.IsStable (φ 0) Y ∧
          ∀ k < N, ∀ ⦃M Q : C⦄ (i : M ⟶ Y) (p : Y ⟶ Q) (δ : Q ⟶ M⟦(1 : ℤ)⟧),
            Triangle.mk i p δ ∈ distTriang C → ¬IsZero M → ¬IsZero Q →
              ((I.cond (γ ((k : ℕ) / N))).slicing.geProp C (φ (k + 1) - 3 * ε) M ∧
                (I.cond (γ ((k : ℕ) / N))).slicing.leProp C (φ (k + 1) + 3 * ε) M) →
              ((I.cond (γ ((k : ℕ) / N))).slicing.geProp C (φ (k + 1) - 3 * ε) Q ∧
                (I.cond (γ ((k : ℕ) / N))).slicing.leProp C (φ (k + 1) + 3 * ε) Q) →
                (I.cond (γ (((k + 1 : ℕ) : ℝ) / N))).imPhase (φ (k + 1)) M < 0) := by
  obtain ⟨N, hN, hclose⟩ := I.exists_subdivision_phaseClose γ hγ hε0
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨N, hN, div_self hN', fun Y φ r hr hZ hφ => ?_⟩
  have h := PreStabilityCondition.WithClassMap.isStable_nodes_iff
    (fun k : ℕ => I.cond (γ ((k : ℕ) / N))) hε (I.phaseClose_nodes hclose) hr hZ hφ
  simpa using h

end StabilitySpaceHypotheses

end CategoryTheory.Triangulated
