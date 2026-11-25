/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.Lattice
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.SupportProperty
import K3Twists.Topology.Order.Selection

/-!
# The support property and the root test: examples

Regression tests for `LinearAlgebra/Lattice/Mukai/Support.lean` and the selection lemma.

**The edge of the curve-wall chamber.** At the curve wall of the elliptic K3 surface with a
section, the normalized charge with `β = -C/4`, `H = C + 2F`, `a = 1` keeps its heart for
`x > 5/4` at fixed `β`. At `x = 5/4` the charge of `𝒪_X(F)`, the root `(1, F, 1)` of rank one,
vanishes, and `δ = 15/8 < 2`, so the rank bound `r² ≤ 2/δ = 16/15` of the root test admits the
rank one; at `x = 3`, `δ = 43/8 > 2` admits none (`re_charge_pos`).

**A selection.** `max(t, 2t)` is a continuous selection from two monotone functions, hence
monotone.
-/

namespace K3TwistsTest.SupportPropertyExamples

open Mukai AlgebraicGeometry.K3.EllipticWithSection

/-- `δ = 15/8` at `x = 5/4`. -/
example : normalizedDelta intersectionReal (5 / 4) betaReal polarizationReal 1 = 15 / 8 := by
  norm_num [normalizedDelta]

/-- At `x = 5/4` the normalized charge of `𝒪_X(F)` vanishes. -/
example : normalizedCharge intersectionReal (5 / 4) betaReal polarizationReal 1
    (realModel toRealNS (lineBundle fibre)) = 0 := by
  apply Complex.ext
  · rw [re_normalizedCharge]
    norm_num [lineBundle, fibre]
  · rw [im_normalizedCharge]
    norm_num [lineBundle, fibre]

/-- `𝒪_X(F)` is a root of rank one with `Im Z = 0`. -/
example : IsSpherical intersection (lineBundle fibre) ∧ (lineBundle fibre).1 = 1 ∧
    (charge (lineBundle fibre)).im = 0 := by
  refine ⟨isSpherical_lineBundle _, rfl, ?_⟩
  rw [im_charge]
  norm_num [lineBundle, fibre, intersection_polarization_apply]

/-- At the curve wall itself `Re Z(𝒪_X(F)) = 7/4 > 0`, as the root test says. -/
example : (charge (lineBundle fibre)).re = 7 / 4 := by
  rw [re_charge]
  norm_num [lineBundle, fibre, intersection_curve_apply]

/-- A continuous selection from two monotone functions is monotone. -/
example : MonotoneOn (fun t : ℝ => max t (2 * t)) Set.univ := by
  refine monotoneOn_of_continuousOn_of_selection (g := ![fun t => t, fun t => 2 * t])
    Set.ordConnected_univ (continuous_id.max (continuous_const.mul continuous_id)).continuousOn
    (fun j => ?_) (fun t _ => ?_)
  · fin_cases j
    · exact fun a _ b _ h => h
    · intro a _ b _ h
      change 2 * a ≤ 2 * b
      linarith
  · rcases le_total t (2 * t) with h | h
    · exact ⟨1, by simp [max_eq_right h]⟩
    · exact ⟨0, by simp [max_eq_left h]⟩

end K3TwistsTest.SupportPropertyExamples
