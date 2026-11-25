/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.GroupAction.TwistSystem
import K3Twists.LinearAlgebra.Lattice.Mukai.PicardRankOne
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# The twist system of the two spherical line bundles, read through the Euler pairing

Let `X` be a K3 surface with `Pic X = ℤH`, `H² = 2d`, `d ≥ 1`. The spherical objects `𝒪_X` and
`𝒪_X(H)` have Mukai vectors `v(𝒪_X) = (1, 0, 1)` and `v(𝒪_X(H)) = (1, 1, d + 1)`, and the twists
`T_{𝒪_X}`, `T_{𝒪_X(H)}` act on the Mukai lattice by the reflections in these roots
(`BilinearForm.reflect` of the Mukai form). The count

  `h(u, v) = |⟨u, v⟩| = |χ(U, V)|`

is the absolute Euler characteristic of the classes. It is a lower bound for the total
dimension of `Ext^*(U, V)`, with equality at the centres: `h(𝒪_X, 𝒪_X) = 2` and
`h(𝒪_X, 𝒪_X(H)) = h⁰(𝒪_X(H)) = d + 2`, the higher cohomology of `𝒪_X(H)` vanishing.

This file checks every axiom of `HomTwistSystem` and every input of the exponent theorem for
these real classes, with the group of isometries of the Mukai lattice acting:

* (A1) the reflections, and all isometries, preserve the pairing;
* (U) and (L) are `⟨u, T v⟩ = ⟨u, v⟩ + ⟨u, S⟩⟨S, v⟩` and the triangle inequality;
* `T_S S = S[-1]` on classes is `BilinearForm.reflect_self`;
* sphericity is `⟨S, S⟩ = -2`; symmetry is `⟨u, v⟩ = ⟨v, u⟩`;
* directed connectivity within two letters is `|⟨v(𝒪_X), v(𝒪_X(H))⟩| = d + 2 ≥ 1`.

So the exponent `η` of `P_q = max |χ(S_i, W S_j)|` exists, with both certificates, and it is
positive: `P_1 ≥ |⟨v(𝒪_X), T_{𝒪_X(H)} v(𝒪_X)⟩| = (d + 2)² - 2 ≥ 7` gives
`η ≥ log(7/4)/3` (`eulerTwistSystem_homExponent_pos`).

The total dimensions `dim Ext^*(S_i, W S_j)` of the objects themselves satisfy the same axioms
(the twist triangles and Serre duality), but they need `D^b(X)` and the twist functors, which the
library does not have; their exponent is at least the one computed here.

## Main definitions

* `mukaiIsometries d`: the isometries of the Mukai lattice, as a subgroup of permutations;
* `reflectIsometry d δ`: the reflection in a root as an isometry;
* `eulerTwistSystem d`: the twist system with centres `v(𝒪_X)`, `v(𝒪_X(H))`, their reflections
  as letters, and the count `|⟨u, v⟩|`.

## Main results

* `eulerTwistSystem_lowerBound`, `eulerTwistSystem_isSpherical`,
  `eulerTwistSystem_directedConnected`, `eulerTwistSystem_symm`: the inputs of the exponent
  theorem;
* `eulerTwistSystem_tendsto`, `eulerTwistSystem_homExponent_pos`: `log P_N / N → η > 0`.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open MukaiVector Filter Topology Real

variable (d : ℤ)

/-- The isometries of the Mukai lattice `ℤ ⊕ ℤH ⊕ ℤ` with `H² = 2d`. -/
def mukaiIsometries : Subgroup (Equiv.Perm (MukaiVector ℤ)) where
  carrier := {g | ∀ u v, pairing d (g u) (g v) = pairing d u v}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun hg hh u v => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hg, hh]
  inv_mem' := fun {g} hg u v => by
    have := hg (g⁻¹ u) (g⁻¹ v)
    simpa using this.symm

/-- The reflection in a root, as a permutation (it is an involution). -/
def reflectPerm {δ : MukaiVector ℤ} (hδ : IsRoot d δ) : Equiv.Perm (MukaiVector ℤ) where
  toFun := BilinearForm.reflect (mukaiForm d) δ
  invFun := BilinearForm.reflect (mukaiForm d) δ
  left_inv := BilinearForm.reflect_reflect (mukaiForm d) δ hδ
  right_inv := BilinearForm.reflect_reflect (mukaiForm d) δ hδ

/-- The reflection in a root, as an isometry: the action of the spherical twist with that
class (and of its inverse). -/
def reflectIsometry {δ : MukaiVector ℤ} (hδ : IsRoot d δ) : mukaiIsometries d :=
  ⟨reflectPerm d hδ, fun u v => by
    have h := BilinearForm.apply_reflect_reflect (mukaiForm d) (mukaiForm_comm d) δ hδ u v
    rwa [mukaiForm_apply, mukaiForm_apply] at h⟩

@[simp] lemma reflectIsometry_smul {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (v : MukaiVector ℤ) :
    reflectIsometry d hδ • v = BilinearForm.reflect (mukaiForm d) δ v := rfl

lemma pairing_smul_isometry (g : mukaiIsometries d) (u v : MukaiVector ℤ) :
    pairing d (g • u) (g • v) = pairing d u v := g.2 u v

/-- The centres `v(𝒪_X) = (1, 0, 1)` and `v(𝒪_X(H)) = (1, 1, d + 1)`. -/
def lineCentre : Fin 2 → MukaiVector ℤ := fun i => lineBundle d (i : ℤ)

lemma isRoot_lineCentre (i : Fin 2) : IsRoot d (lineCentre d i) := isRoot_lineBundle d _

lemma lineCentre_root (i : Fin 2) : pairing d (lineCentre d i) (lineCentre d i) = -2 :=
  isRoot_lineCentre d i

/-- `⟨u, T_S v⟩ = ⟨u, v⟩ + ⟨u, S⟩⟨S, v⟩` for the reflection in `S`. -/
lemma pairing_reflect_right (δ u v : MukaiVector ℤ) :
    pairing d u (BilinearForm.reflect (mukaiForm d) δ v) =
      pairing d u v + pairing d u δ * pairing d δ v := by
  rw [bilinearFormReflect_apply]
  rw [pairing_add_right, pairing_smul_right]
  ring

/-- **The Euler-pairing twist system** of `𝒪_X` and `𝒪_X(H)`: the isometries of the Mukai lattice
act on classes, the letters are the reflections in `v(𝒪_X)` and `v(𝒪_X(H))`, and the count is
`|⟨u, v⟩| = |χ|`. -/
def eulerTwistSystem : HomTwistSystem (mukaiIsometries d) (MukaiVector ℤ) (Fin 2) (Fin 2) where
  S := lineCentre d
  T a := reflectIsometry d (isRoot_lineCentre d a)
  c := id
  h u v := (pairing d u v).natAbs
  h_smul g u v := by rw [pairing_smul_isometry]
  upper a u v := by
    simp only [reflectIsometry_smul, id, pairing_reflect_right]
    rw [← Int.natAbs_mul]
    exact Int.natAbs_add_le _ _
  h_twist_centre a u := by
    simp only [reflectIsometry_smul, id,
      BilinearForm.reflect_self (mukaiForm d) _ (isRoot_lineCentre d a),
      pairing_neg_right, Int.natAbs_neg]

lemma eulerTwistSystem_h (u v : MukaiVector ℤ) :
    (eulerTwistSystem d).h u v = (pairing d u v).natAbs := rfl

/-- (L) for the Euler-pairing system: `|⟨u, S⟩⟨S, v⟩| ≤ |⟨u, v⟩| + |⟨u, T_S v⟩|`. -/
theorem eulerTwistSystem_lowerBound :
    (eulerTwistSystem d).toHomTwistSystem₀.LowerBound := by
  intro a u v
  change (pairing d u (lineCentre d a)).natAbs * (pairing d (lineCentre d a) v).natAbs ≤
    (pairing d u v).natAbs +
      (pairing d u (BilinearForm.reflect (mukaiForm d) (lineCentre d a) v)).natAbs
  rw [pairing_reflect_right, ← Int.natAbs_mul]
  have := Int.natAbs_sub_le (pairing d u v + pairing d u (lineCentre d a) *
    pairing d (lineCentre d a) v) (pairing d u v)
  rw [add_sub_cancel_left] at this
  omega

/-- Sphericity: `|⟨S, S⟩| = 2`. -/
theorem eulerTwistSystem_isSpherical : (eulerTwistSystem d).toHomTwistSystem₀.IsSpherical := by
  intro i
  change (pairing d (lineCentre d i) (lineCentre d i)).natAbs = 2
  rw [lineCentre_root]; rfl

/-- Symmetry of the count, which supplies the bounds for inverse letters. -/
theorem eulerTwistSystem_symm (u v : MukaiVector ℤ) :
    (eulerTwistSystem d).h u v = (eulerTwistSystem d).h v u := by
  simp only [eulerTwistSystem_h, pairing_comm]

lemma pairing_lineCentre_zero_one :
    pairing d (lineCentre d 0) (lineCentre d 1) = -(d + 2) := by
  simp [lineCentre, pairing, lineBundle]; ring

/-- Directed connectivity within two letters, for `d ≥ 0`: `|⟨v(𝒪_X), v(𝒪_X(H))⟩| = d + 2`. -/
theorem eulerTwistSystem_directedConnected (hd : 0 ≤ d) :
    (eulerTwistSystem d).toHomTwistSystem₀.DirectedConnected 1 := by
  intro i j
  refine ⟨j, [i], rfl, rfl, le_rfl, ?_⟩
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  change 1 ≤ (pairing d (lineCentre d j) (lineCentre d i)).natAbs
  fin_cases i <;> fin_cases j
  · simp [lineCentre_root]
  · simp only [Fin.mk_one, Fin.zero_eta]
    rw [pairing_comm, pairing_lineCentre_zero_one]; omega
  · simp only [Fin.mk_one, Fin.zero_eta]
    rw [pairing_lineCentre_zero_one]; omega
  · simp [lineCentre_root]

/-- `|⟨v(𝒪_X), T_{𝒪_X(H)} v(𝒪_X)⟩| = (d + 2)² - 2`. -/
lemma pairing_reflect_lineCentre :
    pairing d (lineCentre d 0)
        (BilinearForm.reflect (mukaiForm d) (lineCentre d 1) (lineCentre d 0)) =
      (d + 2) ^ 2 - 2 := by
  rw [pairing_reflect_right, lineCentre_root, pairing_lineCentre_zero_one, pairing_comm,
    pairing_lineCentre_zero_one]
  ring

/-- **The exponent of the Euler counts exists**, with the certificates of the exponent theorem
(connectivity within `d + 1 = 2` letters). -/
theorem eulerTwistSystem_tendsto (hd : 0 ≤ d) :
    Tendsto (fun N : ℕ => log ((eulerTwistSystem d).maxCount N) / N) atTop
      (𝓝 (eulerTwistSystem d).homExponent) :=
  (eulerTwistSystem d).tendsto_homExponent (eulerTwistSystem_lowerBound d)
    (eulerTwistSystem_isSpherical d) (eulerTwistSystem_directedConnected d hd)

/-- **The exponent is positive** for `d ≥ 1`: `P_1 ≥ (d + 2)² - 2 ≥ 7`, and the lower certificate
at `q = 1` gives `η ≥ log(7/4)/3 > 0`. -/
theorem eulerTwistSystem_homExponent_pos (hd : 1 ≤ d) :
    log (7 / 4) / 3 ≤ (eulerTwistSystem d).homExponent := by
  set E := (eulerTwistSystem d).toHomTwistSystem₀
  have hlow := E.homExponent_lower (eulerTwistSystem_lowerBound d)
    (eulerTwistSystem_isSpherical d) (eulerTwistSystem_directedConnected d (by omega)) 1
  have hP : (7 : ℝ) ≤ E.maxCount 1 := by
    have h := E.le_maxCount (q := 1) 0 0 [1] le_rfl
    have e : E.h (E.S 0) (E.word [1] • E.S 0) = ((d + 2) ^ 2 - 2).natAbs := by
      change (pairing d (lineCentre d 0)
        (BilinearForm.reflect (mukaiForm d) (lineCentre d 1) (lineCentre d 0))).natAbs = _
      rw [pairing_reflect_lineCentre]
    rw [e] at h
    have h7 : 7 ≤ ((d + 2) ^ 2 - 2).natAbs := by
      have : 7 ≤ (d + 2) ^ 2 - 2 := by nlinarith
      omega
    exact_mod_cast h7.trans h
  refine le_trans ?_ hlow
  norm_num only [Nat.cast_ofNat]
  gcongr

end AlgebraicGeometry.K3.PicardRankOne
