/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.GroupAction.CountCocycle

/-!
# A sign-coherent count cocycle

The parity-graded form of the `g`-Kronecker wall in its canonical orientation
(`Matrix.signRule_canonical`): two centres, the letters `T₀` and `T₁⁻¹`, whose signed and count
matrices are both the Thurston matrices `!![1, g; 0, 1]` and `!![1, 0; g, 1]`. The monoid of
linear endomorphisms of `ℝ²` acts on vectors; counts are absolute values and signed vectors the
vectors themselves. Every field holds, the cocycle is sign coherent with `D = 1`, and the
nonnegative vectors are tight, so `CountCocycleHypotheses.tendsto_tight` applies. This shows that
sign coherence is consistent with the other fields; it is not an instance from real objects
(`AlgebraicGeometry.K3.PicardRankOne.eulerCountCocycle_not_signCoherent`).

Built by `lake test`.
-/

namespace K3TwistsTest.CountCocycleModel

open Matrix

/-- The Thurston matrices of the two letters. -/
def thurstonLetter (g : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => !![1, g; 0, 1]
  | 1 => !![1, 0; g, 1]

lemma thurstonLetter_nonneg {g : ℝ} (hg : 0 ≤ g) (a i j : Fin 2) :
    0 ≤ thurstonLetter g a i j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [thurstonLetter, hg]

/-- The parity-graded Kronecker cocycle. -/
noncomputable def kroneckerModel {g : ℝ} (hg : 0 ≤ g) :
    CountCocycleHypotheses (Module.End ℝ (Fin 2 → ℝ)) (Fin 2 → ℝ) (Fin 2) (Fin 2) where
  T a := Matrix.toLin' (thurstonLetter g a)
  count Y i := |Y i|
  signed Y := Y
  P := thurstonLetter g
  E := thurstonLetter g
  count_nonneg _ _ := abs_nonneg _
  abs_signed_le _ _ := le_rfl
  P_nonneg := thurstonLetter_nonneg hg
  count_smul_le a Y i := by
    change |(thurstonLetter g a *ᵥ Y) i| ≤ (thurstonLetter g a *ᵥ fun i => |Y i|) i
    simp only [mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_mul, abs_of_nonneg (thurstonLetter_nonneg hg a i j)]
  signed_smul _ _ := rfl

theorem kroneckerModel_signCoherent {g : ℝ} (hg : 0 ≤ g) :
    (kroneckerModel hg).SignCoherent 1 := by
  refine ⟨fun _ => Or.inl rfl, fun a => ?_⟩
  simp [kroneckerModel]

/-- Nonnegative vectors are tight. -/
theorem kroneckerModel_isTight {g : ℝ} (hg : 0 ≤ g) {Y : Fin 2 → ℝ} (hY : 0 ≤ Y) :
    (kroneckerModel hg).IsTight 1 Y := by
  funext i
  simp [kroneckerModel, abs_of_nonneg (hY i)]

open Filter Topology in
open scoped Matrix.Norms.Operator in
/-- The tight seed `(1, 1)` of the alternating word `T₀ T₁⁻¹` grows at the Gelfand radius of its
count matrix, which equals that of its signed matrix. -/
example {g : ℝ} (hg : 0 ≤ g) :
    Tendsto (fun n : ℕ =>
        ‖(kroneckerModel hg).count ((kroneckerModel hg).word [0, 1] ^ n • ![1, 1])‖ ^ (n : ℝ)⁻¹)
        atTop (𝓝 (gelfandRadius ((kroneckerModel hg).countWord [0, 1]))) ∧
      gelfandRadius ((kroneckerModel hg).signedWord [0, 1]) =
        gelfandRadius ((kroneckerModel hg).countWord [0, 1]) := by
  have hY : (kroneckerModel hg).IsTight 1 ![1, 1] :=
    kroneckerModel_isTight hg (fun i => by fin_cases i <;> simp)
  obtain ⟨h1, h2, -⟩ := (kroneckerModel hg).tendsto_tight (kroneckerModel_signCoherent hg) hY
    one_pos (fun i => by fin_cases i <;> simp [kroneckerModel]) [0, 1]
  exact ⟨h1, h2⟩

end K3TwistsTest.CountCocycleModel
