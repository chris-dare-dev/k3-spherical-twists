/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.EulerTwistSystem
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.TwistWords

/-!
# The periodic witness

In a twist system with symmetric counts, the lower one-letter bound and `T_S S = S[-1]`, take two
letters `a`, `b` with centres `S`, `B` and `M = h(S, B) ≥ 2`. The twist triangles give the two
inequalities of `theta_lower_bound` for the word `Θ = T_a T_b`, so `h(B, Θⁿ S) ≥ M (M - 1)^{2n}`
(`HomTwistSystem₀.theta_le_count`): along the periodic word the centre counts grow at least like
`(M - 1)` per letter, and the exponent of the centre counts is at least `log(M - 1)`
(`HomTwistSystem₀.log_sub_one_le_homExponent`).

For the two spherical line bundles of a K3 surface with `Pic X = ℤH`, `H² = 2d`, read through the
Euler pairing, `M = |χ(𝒪_X, 𝒪_X(H))| = d + 2`, so the exponent is at least `log(d + 1)`
(`eulerTwistSystem_log_le_homExponent`), for every `d ≥ 0`.
-/

open Filter Topology Real

namespace HomTwistSystem

variable {G Obj ι α : Type*} [Group G] [MulAction G Obj] (H : HomTwistSystem G Obj ι α)

/-- With symmetric counts, `T_S S = S[-1]` gives `h(S, T_S D) = h(S, D)` for the centre `S` of every
letter. -/
theorem h_centre_smul (hsym : ∀ U V, H.h U V = H.h V U) (c : α) (D : Obj) :
    H.h (H.S (H.c c)) (H.T c • D) = H.h (H.S (H.c c)) D := by
  rw [← H.h_inv_smul, hsym, H.twist_centre_inv, hsym]

end HomTwistSystem

namespace HomTwistSystem₀

variable {G Obj ι α : Type*} [Group G] [MulAction G Obj] (H : HomTwistSystem₀ G Obj ι α)

/-- The word `a b a b ⋯ a b` of length `2n`. -/
def thetaWord (a b : α) : ℕ → List α
  | 0 => []
  | n + 1 => a :: b :: thetaWord a b n

lemma length_thetaWord (a b : α) (n : ℕ) : (thetaWord a b n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [thetaWord, ih]; ring

lemma word_thetaWord (a b : α) (n : ℕ) :
    H.word (thetaWord a b n) = (H.T a * H.T b) ^ n := by
  induction n with
  | zero => simp [thetaWord]
  | succ n ih =>
    rw [thetaWord, HomTwistSystem₀.word_cons, HomTwistSystem₀.word_cons, ih, pow_succ', mul_assoc]

/-- **The periodic witness.** With symmetric counts, the lower one-letter bound and
`h(S, T_S D) = h(S, D)` for the centre `S` of each letter (which `T_S S = S[-1]` gives,
`HomTwistSystem.h_centre_smul`), two letters `a`, `b` with `M = h(S_{c(a)}, S_{c(b)}) ≥ 2` satisfy
`h(S_{c(b)}, (T_a T_b)ⁿ S_{c(a)}) ≥ M (M - 1)^{2n}`: these are the inequalities of
`theta_lower_bound`. -/
theorem theta_le_count (hsym : ∀ U V, H.h U V = H.h V U) (hL : H.LowerBound)
    (hsph : H.IsSpherical)
    (hfix : ∀ (c : α) D, H.h (H.S (H.c c)) (H.T c • D) = H.h (H.S (H.c c)) D) (a b : α)
    (hM : 2 ≤ H.h (H.S (H.c a)) (H.S (H.c b))) (n : ℕ) :
    (H.h (H.S (H.c a)) (H.S (H.c b)) : ℝ) * ((H.h (H.S (H.c a)) (H.S (H.c b)) : ℝ) - 1) ^ (2 * n) ≤
      H.h (H.S (H.c b)) (H.word (thetaWord a b n) • H.S (H.c a)) := by
  set i := H.c a
  set j := H.c b
  set M : ℝ := (H.h (H.S i) (H.S j) : ℝ)
  have hM2 : (2 : ℝ) ≤ M := by simp only [M]; exact_mod_cast hM
  have hiter : ∀ m : ℕ, ((fun D => H.T a • D) ∘ fun D => H.T b • D)^[m] (H.S i) =
      (H.T a * H.T b) ^ m • H.S i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul, mul_smul]; rfl
  have hLc : ∀ (c : α) U D, (H.h U (H.S (H.c c)) : ℝ) * H.h (H.S (H.c c)) D ≤
      H.h U D + H.h U (H.T c • D) := fun c U D => by exact_mod_cast hL c U D
  have key := AlgebraicGeometry.K3.PicardRankOne.theta_lower_bound
    (fun D => (H.h (H.S i) D : ℝ)) (fun D => (H.h (H.S j) D : ℝ)) (fun D => H.T a • D)
    (fun D => H.T b • D) (M := M) hM2
    (fun D => by have := hLc b (H.S i) D; simp only [M]; linarith)
    (fun D => by simp only [j]; exact_mod_cast hfix b D)
    (fun D => by
      have := hLc a (H.S j) D
      rw [hsym (H.S j) (H.S (H.c a))] at this
      simp only [M]; linarith)
    (fun D => by simp only [i]; exact_mod_cast hfix a D)
    (H.S i) (by
      have h2 := hsph i
      show (H.h (H.S i) (H.S i) : ℝ) ≤ H.h (H.S j) (H.S i)
      rw [show H.h (H.S i) (H.S i) = 2 from h2, hsym]
      exact_mod_cast hM)
    (by simp only [M]; rw [hsym]) n
  rw [hiter] at key
  rw [word_thetaWord]
  exact key.1

variable [Fintype ι] [Fintype α] [Nonempty ι]

/-- **The exponent of the centre counts is at least `log(M - 1)`** for two letters with
`M = h(S_{c(a)}, S_{c(b)}) ≥ 2`, by the periodic witness along `(T_a T_b)ⁿ`. -/
theorem log_sub_one_le_homExponent (hsym : ∀ U V, H.h U V = H.h V U) (hL : H.LowerBound)
    (hsph : H.IsSpherical)
    (hfix : ∀ (c : α) D, H.h (H.S (H.c c)) (H.T c • D) = H.h (H.S (H.c c)) D) {d : ℕ}
    (hconn : H.DirectedConnected d) (a b : α)
    (hM : 2 ≤ H.h (H.S (H.c a)) (H.S (H.c b))) :
    log ((H.h (H.S (H.c a)) (H.S (H.c b)) : ℝ) - 1) ≤ H.homExponent := by
  set M : ℝ := (H.h (H.S (H.c a)) (H.S (H.c b)) : ℝ)
  have hM2 : (2 : ℝ) ≤ M := by simp only [M]; exact_mod_cast hM
  have hη := H.tendsto_homExponent hL hsph hconn
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.mul_le_mul_left 2 h)
      fun b => ⟨b, by omega⟩
  have hsub := hη.comp h2n
  have hlow : Tendsto (fun n : ℕ => log M / ((2 * n : ℕ) : ℝ) + log (M - 1)) atTop
      (𝓝 (0 + log (M - 1))) :=
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp h2n)).add tendsto_const_nhds
  rw [zero_add] at hlow
  refine le_of_tendsto_of_tendsto hlow hsub ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * n by omega)
  have hP := H.le_maxCount (q := 2 * n) (H.c b) (H.c a) (thetaWord a b n)
    (le_of_eq (length_thetaWord a b n))
  have hw := H.theta_le_count hsym hL hsph hfix a b hM n
  have hPr : M * (M - 1) ^ (2 * n) ≤ H.maxCount (2 * n) := hw.trans (by exact_mod_cast hP)
  have hMpos : 0 < M * (M - 1) ^ (2 * n) :=
    mul_pos (by linarith) (pow_pos (by linarith) _)
  have hlog := log_le_log hMpos hPr
  rw [log_mul (by linarith) (pow_pos (by linarith) _).ne', log_pow] at hlog
  simp only [Function.comp]
  rw [div_add' _ _ _ hpos.ne', div_le_div_iff_of_pos_right hpos]
  push_cast at hlog ⊢
  linarith

end HomTwistSystem₀

namespace AlgebraicGeometry.K3.PicardRankOne

/-- **The periodic witness on a K3 surface of Picard rank one.** For the twist system of `𝒪_X` and
`𝒪_X(H)` read through the Euler pairing, `M = |χ(𝒪_X, 𝒪_X(H))| = d + 2`, so the exponent of the
centre counts is at least `log(d + 1)`. -/
theorem eulerTwistSystem_log_le_homExponent (d : ℤ) (hd : 0 ≤ d) :
    log ((d : ℝ) + 1) ≤ (eulerTwistSystem d).homExponent := by
  have hM : (eulerTwistSystem d).h ((eulerTwistSystem d).S ((eulerTwistSystem d).c 0))
      ((eulerTwistSystem d).S ((eulerTwistSystem d).c 1)) = (d + 2).natAbs := by
    change (MukaiVector.pairing d (lineCentre d 0) (lineCentre d 1)).natAbs = _
    rw [pairing_lineCentre_zero_one, Int.natAbs_neg]
  have hcast : (((d + 2).natAbs : ℕ) : ℝ) = (d : ℝ) + 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast (by omega : 0 ≤ d + 2))]
    push_cast; ring
  have h := (eulerTwistSystem d).toHomTwistSystem₀.log_sub_one_le_homExponent
    (eulerTwistSystem_symm d) (eulerTwistSystem_lowerBound d) (eulerTwistSystem_isSpherical d)
    ((eulerTwistSystem d).h_centre_smul (eulerTwistSystem_symm d))
    (eulerTwistSystem_directedConnected d hd) 0 1 (by rw [hM]; omega)
  rw [hM, hcast] at h
  convert h using 2
  ring

end AlgebraicGeometry.K3.PicardRankOne
