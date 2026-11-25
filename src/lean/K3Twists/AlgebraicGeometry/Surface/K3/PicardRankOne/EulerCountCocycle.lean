/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.EulerTwistSystem
import K3Twists.GroupTheory.GroupAction.CountCocycle

/-!
# The count cocycle of the two spherical line bundles

On a K3 surface with `Pic X = ℤH`, `H² = 2d`, let `S₀ = v(𝒪_X)`, `S₁ = v(𝒪_X(H))` and let the
isometries of the Mukai lattice act on classes. For a class `Y` take the signed vector of Euler
pairings with the centres and the count vector of their absolute values,

  `v(Y)_i = ⟨S_i, Y⟩ = -χ(S_i, Y)`,  `c(Y)_i = |⟨S_i, Y⟩|`,

which are the counts `h(S_i, Y)` of `eulerTwistSystem`. The twist `T_a` acts by the reflection in
`S_a`, so `⟨S_i, T_a Y⟩ = ⟨S_i, Y⟩ + ⟨S_i, S_a⟩⟨S_a, Y⟩`: the signed letter is the column
transvection `E_a = 1 + K_{*a} e_aᵀ` with `K_{ia} = ⟨S_i, S_a⟩`, and the count letter
`P_a = 1 + |K_{*a}| e_aᵀ` dominates the counts. This is a `CountCocycleHypotheses` built from
the real classes (`eulerCountCocycle`), with `|E_a| ≤ P_a`, so for every word `W` in the two
twists the growth sandwich holds: the counts `|χ(S_i, Wⁿ Y)|` grow at most at the rate `ρ(P_W)`,
at least at the rate `ρ(E_W)` from seeds meeting the top of the spectrum of `E_W`, and
`ρ(E_W) ≤ ρ(P_W)`.

The sign rule fails here, for every sign diagonal (`eulerCountCocycle_not_signCoherent`): the
diagonal entry of a letter is `1 + ⟨S_a, S_a⟩ = -1` in `E_a` and `1 + 2 = 3` in `P_a`. This is
the symmetric Euler form of a 2-Calabi–Yau category; the squeeze and the exact rate on tight
seeds need the parity-graded form, which real classes with the Euler pairing do not provide.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open MukaiVector Matrix
open scoped Matrix.Norms.Operator

section ColTransvection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The column transvection `1 + x e_aᵀ`, which adds `x_i v_a` to each entry `v_i`. -/
def colTransvection (a : ι) (x : ι → ℝ) : Matrix ι ι ℝ :=
  1 + of fun i j => if j = a then x i else 0

lemma colTransvection_mulVec (a : ι) (x v : ι → ℝ) (i : ι) :
    (colTransvection a x *ᵥ v) i = v i + x i * v a := by
  rw [colTransvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  congr 1
  simp [mulVec, dotProduct, ite_mul, Finset.sum_ite_eq']

omit [Fintype ι] in
lemma colTransvection_apply (a : ι) (x : ι → ℝ) (i j : ι) :
    colTransvection a x i j = (1 : Matrix ι ι ℝ) i j + if j = a then x i else 0 := by
  simp [colTransvection]

end ColTransvection

variable (d : ℤ)

/-- The Gram matrix `K_{ia} = ⟨S_i, S_a⟩` of the centres `v(𝒪_X)`, `v(𝒪_X(H))`. -/
def lineGram (i a : Fin 2) : ℝ := ((pairing d (lineCentre d i) (lineCentre d a) : ℤ) : ℝ)

/-- **The Euler count cocycle** of `𝒪_X` and `𝒪_X(H)`: signed vectors `⟨S_i, Y⟩`, counts
`|⟨S_i, Y⟩|`, signed letters `1 + K_{*a} e_aᵀ`, count letters `1 + |K_{*a}| e_aᵀ`. -/
def eulerCountCocycle :
    CountCocycleHypotheses (mukaiIsometries d) (MukaiVector ℤ) (Fin 2) (Fin 2) where
  T a := reflectIsometry d (isRoot_lineCentre d a)
  count Y i := |((pairing d (lineCentre d i) Y : ℤ) : ℝ)|
  signed Y i := ((pairing d (lineCentre d i) Y : ℤ) : ℝ)
  P a := colTransvection a fun i => |lineGram d i a|
  E a := colTransvection a fun i => lineGram d i a
  count_nonneg _ _ := abs_nonneg _
  abs_signed_le _ _ := le_rfl
  P_nonneg a i j := by
    rw [colTransvection_apply, Matrix.one_apply]
    split_ifs <;> positivity
  count_smul_le a Y i := by
    rw [colTransvection_mulVec]
    simp only [reflectIsometry_smul, pairing_reflect_right, Int.cast_add, Int.cast_mul,
      lineGram]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
  signed_smul a Y := by
    funext i
    rw [colTransvection_mulVec]
    simp only [reflectIsometry_smul, pairing_reflect_right, Int.cast_add, Int.cast_mul,
      lineGram]

/-- The counts of the cocycle are the counts of `eulerTwistSystem` to the centres. -/
lemma eulerCountCocycle_count (Y : MukaiVector ℤ) (i : Fin 2) :
    (eulerCountCocycle d).count Y i = ((eulerTwistSystem d).h (lineCentre d i) Y : ℝ) := by
  simp [eulerCountCocycle, eulerTwistSystem_h, Nat.cast_natAbs, Int.cast_abs]

/-- `|E_a| ≤ P_a` entrywise. -/
theorem eulerCountCocycle_abs_E_le_P (a i j : Fin 2) :
    |(eulerCountCocycle d).E a i j| ≤ (eulerCountCocycle d).P a i j := by
  simp only [eulerCountCocycle, colTransvection_apply, Matrix.one_apply]
  split_ifs
  · exact (abs_add_le _ _).trans (by simp)
  · simp
  · simp
  · simp

/-- **The growth sandwich for words in `T_{𝒪_X}`, `T_{𝒪_X(H)}`**: `ρ(E_W) ≤ ρ(P_W)`. -/
theorem eulerCountCocycle_gelfandRadius_le (w : List (Fin 2)) :
    gelfandRadius ((eulerCountCocycle d).signedWord w) ≤
      gelfandRadius ((eulerCountCocycle d).countWord w) :=
  (eulerCountCocycle d).gelfandRadius_signedWord_le (eulerCountCocycle_abs_E_le_P d) w

/-- **The sign rule fails for the Euler form**: no diagonal of signs conjugates a signed letter
into its count letter, since the diagonal entries are `1 + ⟨S_a, S_a⟩ = -1` and `3`. -/
theorem eulerCountCocycle_not_signCoherent (s : Fin 2 → ℝ) :
    ¬ (eulerCountCocycle d).SignCoherent s := by
  rintro ⟨hs, h⟩
  have h0 := congrFun (congrFun (h 0) 0) 0
  rw [diagonal_conj_apply] at h0
  simp only [eulerCountCocycle, colTransvection_apply, Matrix.one_apply_eq, lineGram,
    lineCentre_root] at h0
  have hs0 := hs.mul_self 0
  norm_num at h0
  nlinarith

end AlgebraicGeometry.K3.PicardRankOne
