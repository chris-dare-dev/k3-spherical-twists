/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.HarderNarasimhan.Polytope
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

## Charge functions and existence

A charge `Z(i, j) = i Z₀ + j Z₁` with `Z₀`, `Z₁` in the upper half-plane or on the negative real
axis is a charge function on the subrepresentations (`DoubledRep.chargeFunction`, rank
`r₀ i + r₁ j`, degree `d₀ i + d₁ j`); a simple on the negative real axis gives vertical steps.

* `DoubledRep.nonempty_hnFiltration`: every charge has an HN filtration on the subrepresentations
  of a finite-dimensional representation, by the existence theorem for charge functions
  (the charge takes finitely many values, `DoubledRep.finite_range_chargeFunction`); it is unique.
  `DoubledRep.hnFiltration` is this filtration.
* `DoubledRep.chargeFunction_phase_le_phase_iff`, `chargeFunction_phase_le_phase_iff_neg`: the
  phase order, vertical steps included, only depends on the side of the wall.
* `RigidRep.range_hnFiltration_chain_upper`, `RigidRep.range_hnFiltration_chain_lower`: the HN
  filtration of the rigid representation given by the existence theorem is `0 ⊂ (H', W) ⊂ M` or
  `0 ⊂ (H', 0) ⊂ M`, for every charge on the corresponding side.
* `RigidRep.verticalCharge_factorPhase_zero`, `RigidRep.verticalCharge_weight_bot_lt`: for the
  charge with `Z₀ = -1`, the first factor `(H', 0) = S₀^{g² - 1}` is vertical, and `⊥` maximizes
  no weight `deg - θ rk`.

## The flag does not depend on the representative

The proposition on rigid wall groups computes the outgoing flag of a wall object on a chosen
matrix representative and transports it to the actual object. That this is well defined is the
following: an isomorphism of representations `u : M ≅ N` maps subrepresentations to
subrepresentations with the same dimension vectors (`DoubledRep.Iso.mapSubrep`), so it carries
the HN filtration of `M` to the HN filtration of `N` (`Iso.map_hnFiltration`, on either side of
the wall); two choices of `u` give the same subrepresentations of `N`, and every automorphism of
`M` fixes the prefixes of its HN filtration (`Iso.mapSubrep_chain`).
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

/-! ### Charge functions, with vertical steps -/

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
/-- A nonzero nonnegative combination of two lexicographically positive vectors is
lexicographically positive. -/
private lemma lex_pos_add {r₀ r₁ d₀ d₁ a b : K} (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    0 < r₀ * a + r₁ * b ∨ (r₀ * a + r₁ * b = 0 ∧ 0 < d₀ * a + d₁ * b) := by
  rcases h₀ with h₀ | ⟨rfl, h₀⟩ <;> rcases h₁ with h₁ | ⟨rfl, h₁⟩
  · left
    rcases ha.lt_or_eq with ha | rfl
    · nlinarith
    · nlinarith
  · rcases ha.lt_or_eq with ha | rfl
    · left; nlinarith
    · right; constructor <;> nlinarith
  · rcases hb.lt_or_eq with hb | rfl
    · left; nlinarith
    · right; constructor <;> nlinarith
  · right
    refine ⟨by ring, ?_⟩
    have p₀ := mul_nonneg h₀.le ha
    have p₁ := mul_nonneg h₁.le hb
    rcases ha.lt_or_eq with ha' | rfl
    · linarith [mul_pos h₀ ha']
    · linarith [mul_pos h₁ (by linarith : 0 < b)]

/-- The charge function on the subrepresentations of `M` with rank `r₀ i + r₁ j` and degree
`d₀ i + d₁ j` at the dimension vector `(i, j)`, for `(r₀, d₀)` and `(r₁, d₁)` lexicographically
positive. With `rk = Im Z`, `deg = -Re Z`, this is the central charge `Z(i, j) = i Z₀ + j Z₁`
with `Z₀`, `Z₁` in the upper half-plane or on the negative real axis; a simple of charge on the
negative real axis gives vertical steps. -/
noncomputable def chargeFunction (M : DoubledRep k ι V₀ V₁) {r₀ r₁ d₀ d₁ : K}
    (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀)) (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) :
    ChargeFunction M.subreps K where
  rk N := r₀ * (dimVec N).1 + r₁ * (dimVec N).2
  deg N := d₀ * (dimVec N).1 + d₁ * (dimVec N).2
  lex_lt {N N'} h := by
    have hle := dimVec_mono h.le
    have hlt := totalDim_lt_of_lt h
    have a₁ : ((dimVec N).1 : K) ≤ (dimVec N').1 := by exact_mod_cast hle.1
    have a₂ : ((dimVec N).2 : K) ≤ (dimVec N').2 := by exact_mod_cast hle.2
    have a₃ : ((dimVec N).1 : K) + (dimVec N).2 < (dimVec N').1 + (dimVec N').2 := by
      exact_mod_cast hlt
    rcases lex_pos_add h₀ h₁ (sub_nonneg.mpr a₁) (sub_nonneg.mpr a₂) (by linarith) with h | h
    · left; linarith
    · right; constructor <;> linarith [h.1, h.2]
  rk_sup_add_inf N N' := (M.slopeFunction one_pos one_pos r₀ r₁).deg_sup_add_inf N N'
  deg_sup_add_inf N N' := (M.slopeFunction one_pos one_pos d₀ d₁).deg_sup_add_inf N N'

lemma chargeFunction_rk {r₀ r₁ d₀ d₁ : K} (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) (N : M.subreps) :
    (M.chargeFunction h₀ h₁).rk N = r₀ * (dimVec N).1 + r₁ * (dimVec N).2 := rfl

lemma chargeFunction_deg {r₀ r₁ d₀ d₁ : K} (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) (N : M.subreps) :
    (M.chargeFunction h₀ h₁).deg N = d₀ * (dimVec N).1 + d₁ * (dimVec N).2 := rfl

/-- The slope function of a charge in the upper half-plane is its charge function. -/
lemma slopeFunction_toChargeFunction {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) (d₀ d₁ : K) :
    (M.slopeFunction h₀ h₁ d₀ d₁).toChargeFunction =
      M.chargeFunction (Or.inl h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
        (Or.inl h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) :=
  rfl

/-- The charge of a subrepresentation takes finitely many values: the dimension vector is at
most `(dim V₀, dim V₁)`. -/
theorem finite_range_chargeFunction {r₀ r₁ d₀ d₁ : K} (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) :
    (Set.range fun N ↦ ((M.chargeFunction h₀ h₁).rk N, (M.chargeFunction h₀ h₁).deg N)).Finite := by
  refine (((Set.finite_Iic (finrank k V₀)).prod (Set.finite_Iic (finrank k V₁))).image
    fun p : ℕ × ℕ ↦ (r₀ * (p.1 : K) + r₁ * p.2, d₀ * (p.1 : K) + d₁ * p.2)).subset ?_
  rintro _ ⟨N, rfl⟩
  have h := dimVec_mono (le_top : N ≤ ⊤)
  rw [dimVec_top] at h
  exact ⟨dimVec N, ⟨h.1, h.2⟩, rfl⟩

/-- The subrepresentations of a finite-dimensional representation satisfy the ascending chain
condition. -/
instance : WellFoundedGT M.subreps :=
  (M.chargeFunction (K := ℚ) (r₀ := 1) (r₁ := 1) (d₀ := 0) (d₁ := 0) (Or.inl one_pos)
    (Or.inl one_pos)).wellFoundedGT_of_finite_range (M.finite_range_chargeFunction _ _)

/-- **Every charge has an HN filtration** on the subrepresentations of a finite-dimensional
representation, from the existence theorem for charge functions. By
`ChargeFunction.HNChain.instSubsingleton` it is unique. -/
theorem nonempty_hnFiltration {r₀ r₁ d₀ d₁ : K} (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) : Nonempty (M.chargeFunction h₀ h₁).HNFiltration :=
  (M.chargeFunction h₀ h₁).nonempty_hnFiltration_of_finite_range
    (M.finite_range_chargeFunction h₀ h₁)

/-- The HN filtration of `M` for the charge `(r₀ i + r₁ j, d₀ i + d₁ j)`, given by
`nonempty_hnFiltration`; it is the only one. -/
noncomputable def hnFiltration {r₀ r₁ d₀ d₁ : K} (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) : (M.chargeFunction h₀ h₁).HNFiltration :=
  Classical.choice (M.nonempty_hnFiltration h₀ h₁)

/-- Every slope function `slopeFunction r d` has an HN filtration. -/
theorem nonempty_hnFiltration_slopeFunction {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (d₀ d₁ : K) : Nonempty (M.slopeFunction h₀ h₁ d₀ d₁).HNFiltration :=
  (M.nonempty_hnFiltration (Or.inl h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (Or.inl h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁))).map SlopeFunction.HNFiltration.ofCharge

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
/-- The cross products of the phases of `chargeFunction` and of `wallSlope`, in the coordinates of
the dimension vectors `(i, j) < (i', j')` and `(k, l) < (k', l')`. -/
private lemma charge_cross_iff {r₀ r₁ d₀ d₁ : K} (hD : d₀ * r₁ < d₁ * r₀)
    (i j i' j' k l k' l' : K) :
    (d₀ * i' + d₁ * j' - (d₀ * i + d₁ * j)) * (r₀ * k' + r₁ * l' - (r₀ * k + r₁ * l)) ≤
        (d₀ * k' + d₁ * l' - (d₀ * k + d₁ * l)) * (r₀ * i' + r₁ * j' - (r₀ * i + r₁ * j)) ↔
      (j' - j) * (k' + l' - (k + l)) ≤ (l' - l) * (i' + j' - (i + j)) := by
  convert cross_le_iff (a := i' - i) (b := j' - j) (a' := k' - k) (b' := l' - l) hD using 2 <;>
    ring

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
private lemma charge_cross_iff_neg {r₀ r₁ d₀ d₁ : K} (hD : d₁ * r₀ < d₀ * r₁)
    (i j i' j' k l k' l' : K) :
    (d₀ * i' + d₁ * j' - (d₀ * i + d₁ * j)) * (r₀ * k' + r₁ * l' - (r₀ * k + r₁ * l)) ≤
        (d₀ * k' + d₁ * l' - (d₀ * k + d₁ * l)) * (r₀ * i' + r₁ * j' - (r₀ * i + r₁ * j)) ↔
      (-j' - -j) * (k' + l' - (k + l)) ≤ (-l' - -l) * (i' + j' - (i + j)) := by
  convert cross_le_iff_neg (a := i' - i) (b := j' - j) (a' := k' - k) (b' := l' - l) hD
    using 2 <;> ring

/-- **The phase order of a charge near the wall only depends on the side**, vertical steps
included: if `d₀ r₁ < d₁ r₀`, the phases of `chargeFunction` are ordered like those of
`wallSlope`. -/
theorem chargeFunction_phase_le_phase_iff {r₀ r₁ d₀ d₁ : K} (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) (hD : d₀ * r₁ < d₁ * r₀) {x y x' y' : M.subreps}
    (hxy : x < y) (hxy' : x' < y') :
    (M.chargeFunction h₀ h₁).phase x y ≤ (M.chargeFunction h₀ h₁).phase x' y' ↔
      (wallSlope K M).toChargeFunction.phase x y ≤
        (wallSlope K M).toChargeFunction.phase x' y' := by
  rw [ChargeFunction.phase_le_phase_iff _ hxy hxy', ChargeFunction.phase_le_phase_iff _ hxy hxy']
  simp only [chargeFunction_rk, chargeFunction_deg, SlopeFunction.toChargeFunction_rk,
    SlopeFunction.toChargeFunction_deg, wallSlope_rk, wallSlope_deg]
  exact charge_cross_iff hD _ _ _ _ _ _ _ _

/-- On the other side, `d₁ r₀ < d₀ r₁`, the phases are ordered like those of `wallSlope.neg`. -/
theorem chargeFunction_phase_le_phase_iff_neg {r₀ r₁ d₀ d₁ : K}
    (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀)) (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁))
    (hD : d₁ * r₀ < d₀ * r₁) {x y x' y' : M.subreps} (hxy : x < y) (hxy' : x' < y') :
    (M.chargeFunction h₀ h₁).phase x y ≤ (M.chargeFunction h₀ h₁).phase x' y' ↔
      (wallSlope K M).neg.toChargeFunction.phase x y ≤
        (wallSlope K M).neg.toChargeFunction.phase x' y' := by
  rw [ChargeFunction.phase_le_phase_iff _ hxy hxy', ChargeFunction.phase_le_phase_iff _ hxy hxy']
  simp only [chargeFunction_rk, chargeFunction_deg, SlopeFunction.toChargeFunction_rk,
    SlopeFunction.toChargeFunction_deg, SlopeFunction.neg_rk, SlopeFunction.neg_deg,
    wallSlope_rk, wallSlope_deg]
  exact charge_cross_iff_neg hD _ _ _ _ _ _ _ _

/-! ### The flag does not depend on the representative -/

section Iso

variable {M} {W₀ W₁ : Type*} [AddCommGroup W₀] [Module k W₀] [AddCommGroup W₁] [Module k W₁]
  [FiniteDimensional k W₀] [FiniteDimensional k W₁] {N : DoubledRep k ι W₀ W₁}

lemma Iso.rk_mapSubrep (u : Iso M N) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) (d₀ d₁ : K)
    (P : M.subreps) :
    (N.slopeFunction h₀ h₁ d₀ d₁).rk (u.mapSubrep P) = (M.slopeFunction h₀ h₁ d₀ d₁).rk P := by
  rw [slopeFunction_rk, slopeFunction_rk, u.dimVec_mapSubrep]

lemma Iso.deg_mapSubrep (u : Iso M N) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) (d₀ d₁ : K)
    (P : M.subreps) :
    (N.slopeFunction h₀ h₁ d₀ d₁).deg (u.mapSubrep P) = (M.slopeFunction h₀ h₁ d₀ d₁).deg P := by
  rw [slopeFunction_deg, slopeFunction_deg, u.dimVec_mapSubrep]

/-- **The HN flag does not depend on the representative.** For every isomorphism `u : M ≅ N`,
the image under `u` of the HN filtration of `M` is the HN filtration of `N`: two isomorphisms
transport the flag to the same subrepresentations of `N`. -/
theorem Iso.map_hnFiltration (u : Iso M N) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) (d₀ d₁ : K)
    (F : (M.slopeFunction h₀ h₁ d₀ d₁).HNFiltration)
    (G : (N.slopeFunction h₀ h₁ d₀ d₁).HNFiltration) :
    F.map u.mapSubrep (u.rk_mapSubrep h₀ h₁ d₀ d₁) (u.deg_mapSubrep h₀ h₁ d₀ d₁) = G :=
  Subsingleton.elim _ _

/-- The same on the opposite side of the wall. -/
theorem Iso.map_hnFiltration_neg (u : Iso M N) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (d₀ d₁ : K) (F : (M.slopeFunction h₀ h₁ d₀ d₁).neg.HNFiltration)
    (G : (N.slopeFunction h₀ h₁ d₀ d₁).neg.HNFiltration) :
    SlopeFunction.HNFiltration.map (s := (M.slopeFunction h₀ h₁ d₀ d₁).neg)
      (s' := (N.slopeFunction h₀ h₁ d₀ d₁).neg) u.mapSubrep
      (fun P ↦ u.rk_mapSubrep h₀ h₁ d₀ d₁ P)
      (fun P ↦ by simp only [SlopeFunction.neg_deg, u.deg_mapSubrep h₀ h₁ d₀ d₁]) F = G :=
  Subsingleton.elim _ _

/-- **Automorphisms fix the HN prefixes.** Every automorphism of `M` maps each prefix of its HN
filtration to itself, on either side of the wall. -/
theorem Iso.mapSubrep_chain (u : Iso M M) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) (d₀ d₁ : K)
    (F : (M.slopeFunction h₀ h₁ d₀ d₁).HNFiltration) (j : Fin (F.n + 1)) :
    u.mapSubrep (F.chain j) = F.chain j :=
  F.apply_chain_eq (u.rk_mapSubrep h₀ h₁ d₀ d₁) (u.deg_mapSubrep h₀ h₁ d₀ d₁) j

theorem Iso.mapSubrep_chain_neg (u : Iso M M) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (d₀ d₁ : K) (F : (M.slopeFunction h₀ h₁ d₀ d₁).neg.HNFiltration) (j : Fin (F.n + 1)) :
    u.mapSubrep (F.chain j) = F.chain j :=
  F.apply_chain_eq (fun P ↦ u.rk_mapSubrep h₀ h₁ d₀ d₁ P)
    (fun P ↦ by simp only [SlopeFunction.neg_deg, u.deg_mapSubrep h₀ h₁ d₀ d₁]) j

end Iso

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

/-! ### Every charge, through the existence and uniqueness theorems -/

variable {K}

/-- **The HN filtration of the rigid representation on the first side, for every charge**, vertical
charges included: for `(r₀, d₀)`, `(r₁, d₁)` lexicographically positive with `d₀ r₁ < d₁ r₀`, it
is `0 ⊂ (H', W) ⊂ M`. -/
noncomputable def hnUpperCharge {r₀ r₁ d₀ d₁ : K} (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) (hD : d₀ * r₁ < d₁ * r₀) :
    ((rigidRep k ι).chargeFunction h₀ h₁).HNFiltration :=
  (hnUpper K).toCharge.ofPhaseOrder fun _ _ _ _ h h' ↦
    ((rigidRep k ι).chargeFunction_phase_le_phase_iff h₀ h₁ hD h h').symm

/-- **The HN filtration of the rigid representation on the other side, for every charge**: for
`d₁ r₀ < d₀ r₁` and `g ≥ 2` it is `0 ⊂ (H', 0) ⊂ M`. -/
noncomputable def hnLowerCharge (hι : 2 ≤ Fintype.card ι) {r₀ r₁ d₀ d₁ : K}
    (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀)) (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁))
    (hD : d₁ * r₀ < d₀ * r₁) : ((rigidRep k ι).chargeFunction h₀ h₁).HNFiltration :=
  (hnLower K hι).toCharge.ofPhaseOrder fun _ _ _ _ h h' ↦
    ((rigidRep k ι).chargeFunction_phase_le_phase_iff_neg h₀ h₁ hD h h').symm

/-- **The HN filtration given by the existence theorem is `0 ⊂ (H', W) ⊂ M`** on the first side:
`DoubledRep.hnFiltration` comes from `ChargeFunction.nonempty_hnFiltration_of_finite_range`, and
uniqueness identifies it with `hnUpperCharge`. -/
theorem range_hnFiltration_chain_upper {r₀ r₁ d₀ d₁ : K} (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀))
    (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁)) (hD : d₀ * r₁ < d₁ * r₀) :
    Set.range ((rigidRep k ι).hnFiltration h₀ h₁).chain = {⊥, upperCorner, ⊤} := by
  rw [Subsingleton.elim ((rigidRep k ι).hnFiltration h₀ h₁) (hnUpperCharge h₀ h₁ hD)]
  change Set.range ![⊥, upperCorner, ⊤] = _
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

/-- **The HN filtration given by the existence theorem is `0 ⊂ (H', 0) ⊂ M`** on the other
side. -/
theorem range_hnFiltration_chain_lower (hι : 2 ≤ Fintype.card ι) {r₀ r₁ d₀ d₁ : K}
    (h₀ : 0 < r₀ ∨ (r₀ = 0 ∧ 0 < d₀)) (h₁ : 0 < r₁ ∨ (r₁ = 0 ∧ 0 < d₁))
    (hD : d₁ * r₀ < d₀ * r₁) :
    Set.range ((rigidRep k ι).hnFiltration h₀ h₁).chain = {⊥, lowerCorner, ⊤} := by
  rw [Subsingleton.elim ((rigidRep k ι).hnFiltration h₀ h₁) (hnLowerCharge hι h₀ h₁ hD)]
  change Set.range ![⊥, lowerCorner, ⊤] = _
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

variable (K) in
/-- The vertical charge: `rk = j`, `deg = i`, that is `Z₀ = -1` on the negative real axis and
`Z₁ = i`. The simple `S₀` has phase `⊤`. -/
noncomputable def verticalCharge : ChargeFunction (rigidRep k ι).subreps K :=
  (rigidRep k ι).chargeFunction (r₀ := 0) (d₀ := 1) (r₁ := 1) (d₁ := 0) (Or.inr ⟨rfl, one_pos⟩)
    (Or.inl one_pos)

/-- **A vertical first edge on a real object.** For the vertical charge and `g ≥ 2`, the HN
filtration of the rigid representation is `0 ⊂ (H', 0) ⊂ M`, and its first factor
`(H', 0) = S₀^{g² - 1}` is vertical. -/
theorem verticalCharge_factorPhase_zero (hι : 2 ≤ Fintype.card ι)
    (F : (verticalCharge (k := k) (ι := ι) K).HNFiltration) (h0 : 0 < F.n) :
    F.factorPhase ⟨0, h0⟩ = ⊤ := by
  refine (F.factorPhase_zero_eq_top_iff h0).mpr ⟨lowerCorner, bot_lt_lowerCorner hι, ?_⟩
  simp [verticalCharge, chargeFunction_rk, dimVec_lowerCorner]

/-- **`⊥` maximizes no weight for the vertical charge.** Every weight `w_θ` is larger at
`(H', 0)` than at `⊥`, so the disjunct `x = ⊥` of `ChargeFunction.HNChain.mem_range_chain_iff`
is needed for the rigid representation. -/
theorem verticalCharge_weight_bot_lt (hι : 2 ≤ Fintype.card ι) (θ : K) :
    (verticalCharge (k := k) (ι := ι) K).weight θ ⊥ <
      (verticalCharge (k := k) (ι := ι) K).weight θ lowerCorner := by
  have h1 : 1 ≤ Fintype.card ι ^ 2 - 1 := by
    have : 4 ≤ Fintype.card ι ^ 2 := by nlinarith
    omega
  have h1' : (1 : K) ≤ ((Fintype.card ι ^ 2 - 1 : ℕ) : K) := by exact_mod_cast h1
  simp only [ChargeFunction.weight, verticalCharge, chargeFunction_rk, chargeFunction_deg,
    DoubledRep.dimVec_bot, dimVec_lowerCorner]
  push_cast
  linarith

end RigidRep

end Quiver.Kronecker
