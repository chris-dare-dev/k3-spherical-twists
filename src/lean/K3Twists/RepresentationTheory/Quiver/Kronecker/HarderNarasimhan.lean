/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.HarderNarasimhan
import K3Twists.RepresentationTheory.Quiver.Kronecker.RigidRep

/-!
# Harder–Narasimhan filtrations of representations of the doubled Kronecker quiver

Ranks `r₀, r₁ > 0` and degrees `d₀, d₁` in a linearly ordered field `K` give the slope function
`rk = r₀ i + r₁ j`, `deg = d₀ i + d₁ j` on the lattice of subrepresentations of a
finite-dimensional representation, `(i, j)` being the dimension vector
(`DoubledRep.slopeFunction`). A central charge `Z(i, j) = i Z₀ + j Z₁` with `Im Z₀, Im Z₁ > 0`,
such as the perturbed charge on one side of a wall with two simples, is the case `r = Im Z`,
`d = -Re Z`: its phase order on nonzero subquotients is the slope order.

The slope order of nonzero dimension vectors only depends on the sign of `d₁ r₀ - d₀ r₁`: it is
the order of `j/(i + j)` when the sign is positive (`slope_le_slope_iff`), so every such slope
function has the HN filtrations of `DoubledRep.wallSlope`, of rank `i + j` and degree `j`
(`HNFiltration.ofSlopeOrder`), and the opposite sign gives those of `wallSlope.neg`. These are the
two sides of the wall.

For the rigid representation of dimension `(g², g)`:

* `RigidRep.hnUpper`: on the side where the phase increases with `j/(i + j)`, the HN filtration is
  `0 ⊂ (H', W) ⊂ M`, with the stable factor `(H', W)` (`RigidRep.isStable_upperCorner`) of
  dimension `(g² - 1, g)` and the simple quotient of dimension `(1, 0)`;
* `RigidRep.hnLower`: on the other side it is `0 ⊂ (H', 0) ⊂ M`, with the semistable factor
  `(H', 0) = S₀^{g² - 1}` and the stable quotient of dimension `(1, g)`
  (`RigidRep.isStable_lowerCorner_top`);
* `RigidRep.hnUpperOf`, `RigidRep.hnLowerOf`: the same filtrations for every slope function
  `slopeFunction r d` on the corresponding side.

By `Order.SlopeFunction.HNFiltration.instSubsingleton` these are the only HN filtrations, and by
`HNFiltration.convexHull_subset` they read the upper and lower boundaries of the convex hull of
the points `(i + j, j)` of the subrepresentations.
-/

namespace Quiver.Kronecker

open Module Order

namespace DoubledRep

variable {k ι V₀ V₁ : Type*} [Field k] [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
  [Module k V₁] [FiniteDimensional k V₀] [FiniteDimensional k V₁]
  {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The slope function on the subrepresentations of `M` with rank `r₀ i + r₁ j` and degree
`d₀ i + d₁ j` at the dimension vector `(i, j)`. -/
noncomputable def slopeFunction (M : DoubledRep k ι V₀ V₁) {r₀ r₁ : K} (h₀ : 0 < r₀)
    (h₁ : 0 < r₁) (d₀ d₁ : K) : SlopeFunction M.subreps K where
  rk N := r₀ * (dimVec N).1 + r₁ * (dimVec N).2
  deg N := d₀ * (dimVec N).1 + d₁ * (dimVec N).2
  rk_strictMono N N' h := by
    have hle := dimVec_mono h.le
    have hlt := totalDim_lt_of_lt h
    have a₁ : ((dimVec N).1 : K) ≤ (dimVec N').1 := by exact_mod_cast hle.1
    have a₂ : ((dimVec N).2 : K) ≤ (dimVec N').2 := by exact_mod_cast hle.2
    have a₃ : ((dimVec N).1 : K) + (dimVec N).2 < (dimVec N').1 + (dimVec N').2 := by
      exact_mod_cast hlt
    rcases lt_or_eq_of_le a₁ with b | b
    · nlinarith
    · have : ((dimVec N).2 : K) < (dimVec N').2 := by linarith
      nlinarith
  rk_sup_add_inf N N' := by
    have h := dimVec_sup_add_inf N N'
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at h
    have e₁ : ((dimVec (N ⊔ N')).1 : K) + (dimVec (N ⊓ N')).1 = (dimVec N).1 + (dimVec N').1 := by
      exact_mod_cast h.1
    have e₂ : ((dimVec (N ⊔ N')).2 : K) + (dimVec (N ⊓ N')).2 = (dimVec N).2 + (dimVec N').2 := by
      exact_mod_cast h.2
    linear_combination r₀ * e₁ + r₁ * e₂
  deg_sup_add_inf N N' := by
    have h := dimVec_sup_add_inf N N'
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at h
    have e₁ : ((dimVec (N ⊔ N')).1 : K) + (dimVec (N ⊓ N')).1 = (dimVec N).1 + (dimVec N').1 := by
      exact_mod_cast h.1
    have e₂ : ((dimVec (N ⊔ N')).2 : K) + (dimVec (N ⊓ N')).2 = (dimVec N).2 + (dimVec N').2 := by
      exact_mod_cast h.2
    linear_combination d₀ * e₁ + d₁ * e₂

variable (K) in
/-- The slope function of one side of the wall: rank `i + j` and degree `j`, so the phase of a
nonzero dimension vector increases with `j/(i + j)`. The other side is `(wallSlope K M).neg`. -/
noncomputable def wallSlope (M : DoubledRep k ι V₀ V₁) : SlopeFunction M.subreps K :=
  M.slopeFunction one_pos one_pos 0 1

variable (M : DoubledRep k ι V₀ V₁)

@[simp] lemma wallSlope_rk (N : M.subreps) :
    (wallSlope K M).rk N = (dimVec N).1 + (dimVec N).2 := by
  simp [wallSlope, slopeFunction]

@[simp] lemma wallSlope_deg (N : M.subreps) : (wallSlope K M).deg N = (dimVec N).2 := by
  simp [wallSlope, slopeFunction]

lemma slopeFunction_rk (M : DoubledRep k ι V₀ V₁) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (d₀ d₁ : K) (N : M.subreps) :
    (M.slopeFunction h₀ h₁ d₀ d₁).rk N = r₀ * (dimVec N).1 + r₁ * (dimVec N).2 := rfl

lemma slopeFunction_deg (M : DoubledRep k ι V₀ V₁) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (d₀ d₁ : K) (N : M.subreps) :
    (M.slopeFunction h₀ h₁ d₀ d₁).deg N = d₀ * (dimVec N).1 + d₁ * (dimVec N).2 := rfl

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
/-- The cross-multiplied comparison of two slopes `(d₀ a + d₁ b)/(r₀ a + r₁ b)` is the comparison
of the ratios `b/(a + b)`, scaled by `d₁ r₀ - d₀ r₁`. -/
private lemma cross_le_iff {r₀ r₁ d₀ d₁ a b a' b' : K} (hD : d₀ * r₁ < d₁ * r₀) :
    (d₀ * a + d₁ * b) * (r₀ * a' + r₁ * b') ≤ (d₀ * a' + d₁ * b') * (r₀ * a + r₁ * b) ↔
      b * (a' + b') ≤ b' * (a + b) := by
  have key : (d₀ * a' + d₁ * b') * (r₀ * a + r₁ * b) - (d₀ * a + d₁ * b) * (r₀ * a' + r₁ * b') =
      (d₁ * r₀ - d₀ * r₁) * (b' * (a + b) - b * (a' + b')) := by ring
  rw [← sub_nonneg, key, mul_nonneg_iff_of_pos_left (by linarith), sub_nonneg]

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
private lemma cross_le_iff_neg {r₀ r₁ d₀ d₁ a b a' b' : K} (hD : d₁ * r₀ < d₀ * r₁) :
    (d₀ * a + d₁ * b) * (r₀ * a' + r₁ * b') ≤ (d₀ * a' + d₁ * b') * (r₀ * a + r₁ * b) ↔
      -b * (a' + b') ≤ -b' * (a + b) := by
  have key : (d₀ * a' + d₁ * b') * (r₀ * a + r₁ * b) - (d₀ * a + d₁ * b) * (r₀ * a' + r₁ * b') =
      (d₀ * r₁ - d₁ * r₀) * (-b' * (a + b) - -b * (a' + b')) := by ring
  rw [← sub_nonneg, key, mul_nonneg_iff_of_pos_left (by linarith), sub_nonneg]

variable {M} in
/-- The rank and degree differences of `slopeFunction` and of `wallSlope` across `x ≤ y`, in
terms of the differences `a, b` of the dimension vectors. -/
private lemma slope_eq {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) (d₀ d₁ : K) (x y : M.subreps) :
    (M.slopeFunction h₀ h₁ d₀ d₁).slope x y =
        (d₀ * (((dimVec y).1 : K) - (dimVec x).1) + d₁ * (((dimVec y).2 : K) - (dimVec x).2)) /
          (r₀ * (((dimVec y).1 : K) - (dimVec x).1) + r₁ * (((dimVec y).2 : K) - (dimVec x).2)) ∧
      (wallSlope K M).slope x y = (0 * (((dimVec y).1 : K) - (dimVec x).1) +
          1 * (((dimVec y).2 : K) - (dimVec x).2)) /
        (1 * (((dimVec y).1 : K) - (dimVec x).1) + 1 * (((dimVec y).2 : K) - (dimVec x).2)) := by
  constructor <;>
  · simp only [SlopeFunction.slope, slopeFunction_rk, slopeFunction_deg, wallSlope_rk,
      wallSlope_deg]
    congr 1 <;> ring

/-- **The phase order near a wall only depends on the side.** If `d₀ r₁ < d₁ r₀`, the slopes of
`slopeFunction r d` are ordered like the ratios `j/(i + j)`, that is like those of `wallSlope`. -/
theorem slope_le_slope_iff {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) {d₀ d₁ : K}
    (hD : d₀ * r₁ < d₁ * r₀) {x y x' y' : M.subreps} (hxy : x < y) (hxy' : x' < y') :
    (M.slopeFunction h₀ h₁ d₀ d₁).slope x y ≤ (M.slopeFunction h₀ h₁ d₀ d₁).slope x' y' ↔
      (wallSlope K M).slope x y ≤ (wallSlope K M).slope x' y' := by
  have p₁ := sub_pos.mpr ((M.slopeFunction h₀ h₁ d₀ d₁).rk_strictMono hxy)
  have p₂ := sub_pos.mpr ((M.slopeFunction h₀ h₁ d₀ d₁).rk_strictMono hxy')
  have q₁ := sub_pos.mpr ((wallSlope K M).rk_strictMono hxy)
  have q₂ := sub_pos.mpr ((wallSlope K M).rk_strictMono hxy')
  rw [slopeFunction_rk, slopeFunction_rk] at p₁ p₂
  rw [wallSlope_rk, wallSlope_rk] at q₁ q₂
  rw [(slope_eq h₀ h₁ d₀ d₁ x y).1, (slope_eq h₀ h₁ d₀ d₁ x' y').1,
    (slope_eq h₀ h₁ d₀ d₁ x y).2, (slope_eq h₀ h₁ d₀ d₁ x' y').2,
    div_le_div_iff₀ (by linarith) (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]
  simp only [zero_mul, zero_add, one_mul]
  exact cross_le_iff hD

/-- On the other side, `d₁ r₀ < d₀ r₁`, the slopes are ordered like those of `wallSlope.neg`. -/
theorem slope_le_slope_iff_neg {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) {d₀ d₁ : K}
    (hD : d₁ * r₀ < d₀ * r₁) {x y x' y' : M.subreps} (hxy : x < y) (hxy' : x' < y') :
    (M.slopeFunction h₀ h₁ d₀ d₁).slope x y ≤ (M.slopeFunction h₀ h₁ d₀ d₁).slope x' y' ↔
      (wallSlope K M).neg.slope x y ≤ (wallSlope K M).neg.slope x' y' := by
  have p₁ := sub_pos.mpr ((M.slopeFunction h₀ h₁ d₀ d₁).rk_strictMono hxy)
  have p₂ := sub_pos.mpr ((M.slopeFunction h₀ h₁ d₀ d₁).rk_strictMono hxy')
  have q₁ := sub_pos.mpr ((wallSlope K M).rk_strictMono hxy)
  have q₂ := sub_pos.mpr ((wallSlope K M).rk_strictMono hxy')
  rw [slopeFunction_rk, slopeFunction_rk] at p₁ p₂
  rw [wallSlope_rk, wallSlope_rk] at q₁ q₂
  have hneg : ∀ u v : M.subreps, (wallSlope K M).neg.slope u v = -(wallSlope K M).slope u v :=
    fun u v ↦ by simp only [SlopeFunction.slope, SlopeFunction.neg_rk, SlopeFunction.neg_deg]; ring
  rw [hneg, hneg, (slope_eq h₀ h₁ d₀ d₁ x y).1, (slope_eq h₀ h₁ d₀ d₁ x' y').1,
    (slope_eq h₀ h₁ d₀ d₁ x y).2, (slope_eq h₀ h₁ d₀ d₁ x' y').2, ← neg_div, ← neg_div,
    div_le_div_iff₀ (by linarith) (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]
  simp only [zero_mul, zero_add, one_mul]
  exact cross_le_iff_neg hD

end DoubledRep

/-! ### The rigid representation -/

namespace RigidRep

open DoubledRep

variable {k ι : Type*} [Field k] [DecidableEq ι] [Fintype ι] [Nonempty ι]
  (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma bot_lt_upperCorner : (⊥ : (rigidRep k ι).subreps) < upperCorner := by
  refine bot_lt_iff_ne_bot.mpr fun h ↦ ?_
  have := congrArg DoubledRep.dimVec h
  rw [dimVec_upperCorner, DoubledRep.dimVec_bot] at this
  exact Fintype.card_ne_zero (congrArg Prod.snd this)

lemma upperCorner_lt_top : (upperCorner : (rigidRep k ι).subreps) < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun h ↦ ?_
  have := congrArg (fun N ↦ (DoubledRep.dimVec N).1) h
  simp only [dimVec_upperCorner, dimVec_top] at this
  have : 1 ≤ Fintype.card ι ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  omega

lemma bot_lt_lowerCorner (hι : 2 ≤ Fintype.card ι) :
    (⊥ : (rigidRep k ι).subreps) < lowerCorner := by
  refine bot_lt_iff_ne_bot.mpr fun h ↦ ?_
  have := congrArg (fun N ↦ (DoubledRep.dimVec N).1) h
  simp only [dimVec_lowerCorner, DoubledRep.dimVec_bot] at this
  have : 4 ≤ Fintype.card ι ^ 2 := by nlinarith
  omega

lemma lowerCorner_lt_top : (lowerCorner : (rigidRep k ι).subreps) < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun h ↦ ?_
  have := congrArg (fun N ↦ (DoubledRep.dimVec N).2) h
  simp only [dimVec_lowerCorner, dimVec_top] at this
  exact Fintype.card_ne_zero this.symm

omit [Nonempty ι] in
/-- Above `(H', W)` there is only `M`. -/
lemma eq_upperCorner_or_top {N : (rigidRep k ι).subreps} (h : upperCorner ≤ N) :
    N = upperCorner ∨ N = ⊤ := by
  rcases eq_top_or N with rfl | ⟨-, htop, -⟩
  · exact Or.inr rfl
  · exact Or.inl (htop (top_le_iff.mp (Prod.mk_le_mk.mp h).2))

/-- `(H', W)` is stable for the side where the phase increases with `j/(i + j)`: every nonzero
proper subrepresentation has a smaller ratio `j/(i + j)`. -/
theorem isStable_upperCorner :
    (wallSlope K (rigidRep k ι)).IsStable ⊥ upperCorner := by
  refine ⟨bot_lt_upperCorner, fun N h₁ h₂ ↦ ?_⟩
  rw [SlopeFunction.weight_slope_lt_iff _ bot_lt_upperCorner]
  simp only [wallSlope_rk, wallSlope_deg, DoubledRep.dimVec_bot, dimVec_upperCorner]
  have hle := (dimVec_upper N).1
  have hne : (Fintype.card ι ^ 2 - 1 + Fintype.card ι) * (DoubledRep.dimVec N).2 ≠
      Fintype.card ι * ((DoubledRep.dimVec N).1 + (DoubledRep.dimVec N).2) := fun h ↦ by
    rcases dimVec_upper_eq h with h' | h'
    · exact h₁.ne' h'
    · exact h₂.ne h'
  have hlt := lt_of_le_of_ne hle hne
  have h1 : 1 ≤ Fintype.card ι ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  have hcast : ((Fintype.card ι ^ 2 - 1 + Fintype.card ι : ℕ) : K) *
      ((DoubledRep.dimVec N).2 : K) <
      (Fintype.card ι : K) * ((DoubledRep.dimVec N).1 + (DoubledRep.dimVec N).2) := by
    exact_mod_cast hlt
  push_cast [h1] at hcast ⊢
  linarith

/-- **The HN filtration on the side where the phase increases with `j/(i + j)`**:
`0 ⊂ (H', W) ⊂ M`, with slopes `g/(g² + g - 1) > 0`. -/
noncomputable def hnUpper : (wallSlope K (rigidRep k ι)).HNFiltration where
  n := 2
  chain := ![⊥, upperCorner, ⊤]
  strictMono := Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
    fin_cases i
    · exact bot_lt_upperCorner
    · exact upperCorner_lt_top
  chain_zero := rfl
  chain_last := rfl
  semistable i := by
    fin_cases i
    · exact (isStable_upperCorner K).isSemistable
    · exact (SlopeFunction.isStable_of_forall _ upperCorner_lt_top fun N h₁ h₂ ↦ by
        rcases eq_upperCorner_or_top h₁.le with h | h
        · exact h₁.ne' h
        · exact h₂.ne h).isSemistable
  slope_strictAnti := by
    refine Fin.strictAnti_iff_succ_lt.mpr fun i ↦ ?_
    fin_cases i
    simp only [Fin.isValue, Fin.zero_eta, Fin.succ_zero_eq_one, Fin.castSucc_zero,
      Fin.castSucc_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [SlopeFunction.slope, wallSlope_rk, wallSlope_deg, DoubledRep.dimVec_bot,
      dimVec_upperCorner, dimVec_top]
    have h1 : 1 ≤ Fintype.card ι ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
    have hg : (0 : K) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have h1' : (1 : K) ≤ (Fintype.card ι : K) ^ 2 := by exact_mod_cast h1
    push_cast [h1]
    rw [sub_self, zero_div]
    refine div_pos (by linarith) ?_
    linarith

/-- `M/(H', 0)`, of dimension `(1, g)`, is stable for the side where the phase increases with
`i/(i + j)`: every subrepresentation strictly between `(H', 0)` and `M` gives a subobject of
smaller ratio `i/(i + j)`. -/
theorem isStable_lowerCorner_top :
    (wallSlope K (rigidRep k ι)).neg.IsStable lowerCorner ⊤ := by
  refine ⟨lowerCorner_lt_top, fun N h₁ h₂ ↦ ?_⟩
  rw [SlopeFunction.weight_slope_lt_iff _ lowerCorner_lt_top]
  simp only [SlopeFunction.neg_rk, SlopeFunction.neg_deg, wallSlope_rk, wallSlope_deg,
    dimVec_lowerCorner, dimVec_top]
  have hle := dimVec_lower N
  have hne : Fintype.card ι * (DoubledRep.dimVec N).1 ≠
      Fintype.card ι * (Fintype.card ι ^ 2 - 1) + (DoubledRep.dimVec N).2 := fun h ↦ by
    rcases dimVec_lower_eq h with h' | h'
    · exact h₁.ne' h'
    · exact h₂.ne h'
  have hlt := lt_of_le_of_ne hle hne
  have h1 : 1 ≤ Fintype.card ι ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  have hcast : (Fintype.card ι : K) * ((DoubledRep.dimVec N).1 : K) <
      (Fintype.card ι : K) * ((Fintype.card ι ^ 2 - 1 : ℕ) : K) + (DoubledRep.dimVec N).2 := by
    exact_mod_cast hlt
  push_cast [h1] at hcast ⊢
  nlinarith

/-- **The HN filtration on the side where the phase increases with `i/(i + j)`**:
`0 ⊂ (H', 0) ⊂ M`, with slopes `0 > -g/(g + 1)`, for `g ≥ 2`. -/
noncomputable def hnLower (hι : 2 ≤ Fintype.card ι) :
    (wallSlope K (rigidRep k ι)).neg.HNFiltration where
  n := 2
  chain := ![⊥, lowerCorner, ⊤]
  strictMono := Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
    fin_cases i
    · exact bot_lt_lowerCorner hι
    · exact lowerCorner_lt_top
  chain_zero := rfl
  chain_last := rfl
  semistable i := by
    fin_cases i
    · show (wallSlope K (rigidRep k ι)).neg.IsSemistable ⊥ lowerCorner
      refine ⟨bot_lt_lowerCorner hι, fun N _ _ ↦ ?_⟩
      rw [SlopeFunction.weight_slope_le_iff _ (bot_lt_lowerCorner hι)]
      simp only [SlopeFunction.neg_rk, SlopeFunction.neg_deg, wallSlope_rk, wallSlope_deg,
        dimVec_lowerCorner, DoubledRep.dimVec_bot]
      have h1 : 1 ≤ Fintype.card ι ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
      push_cast [h1]
      have : (1 : K) ≤ (Fintype.card ι : K) ^ 2 := by exact_mod_cast h1
      have : (0 : K) ≤ (DoubledRep.dimVec N).2 := Nat.cast_nonneg _
      nlinarith
    · exact (isStable_lowerCorner_top K).isSemistable
  slope_strictAnti := by
    refine Fin.strictAnti_iff_succ_lt.mpr fun i ↦ ?_
    fin_cases i
    simp only [Fin.isValue, Fin.zero_eta, Fin.succ_zero_eq_one, Fin.castSucc_zero,
      Fin.castSucc_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [SlopeFunction.slope, SlopeFunction.neg_rk, SlopeFunction.neg_deg, wallSlope_rk,
      wallSlope_deg, DoubledRep.dimVec_bot, dimVec_lowerCorner, dimVec_top]
    have h1 : 1 ≤ Fintype.card ι ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
    have hg : (0 : K) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    push_cast [h1]
    rw [show (-(0 : K) - -0) = 0 by ring, zero_div]
    refine div_neg_of_neg_of_pos (by linarith) ?_
    linarith

/-- **Every charge on the first side.** For ranks `r₀, r₁ > 0` and degrees with
`d₀ r₁ < d₁ r₀`, the HN filtration of the rigid representation is still `0 ⊂ (H', W) ⊂ M`. -/
noncomputable def hnUpperOf {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) {d₀ d₁ : K}
    (hD : d₀ * r₁ < d₁ * r₀) : ((rigidRep k ι).slopeFunction h₀ h₁ d₀ d₁).HNFiltration :=
  (hnUpper K).ofSlopeOrder fun _ _ _ _ h h' ↦ (slope_le_slope_iff _ h₀ h₁ hD h h').symm

/-- **Every charge on the other side.** For `d₁ r₀ < d₀ r₁` and `g ≥ 2`, the HN filtration of the
rigid representation is `0 ⊂ (H', 0) ⊂ M`. -/
noncomputable def hnLowerOf (hι : 2 ≤ Fintype.card ι) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    {d₀ d₁ : K} (hD : d₁ * r₀ < d₀ * r₁) :
    ((rigidRep k ι).slopeFunction h₀ h₁ d₀ d₁).HNFiltration :=
  (hnLower K hι).ofSlopeOrder fun _ _ _ _ h h' ↦ (slope_le_slope_iff_neg _ h₀ h₁ hD h h').symm

end RigidRep

end Quiver.Kronecker
