/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.BipartiteJointSpectralRadius
import K3Twists.GroupTheory.GroupAction.TwistSystem

/-!
# The bipartite bound `e^η ≤ ρ_s`

Let `H` be a twist system (with `T_S S = S[-1]` read through the count) whose centres form a
bipartite configuration: a two-colouring `p` of the centres with `h(S_i, S_k) = 0` for distinct
centres of one colour, and `h(S_i, S_k) ≤ s` for distinct centres, `s ≥ 1`. Then

* `HomTwistSystem.exists_maxCount_le_of_bipartite`: for every `R > ρ_s = (s + √(s² + 4))/2` there
  is `C` with `P_q ≤ C R^q` for all `q`;
* `HomTwistSystem.exp_homExponent_le_of_bipartite`: the exponent of the centre counts satisfies
  `e^η ≤ ρ_s`, at every valence of the configuration and for every alphabet of letters at the
  centres.

The proof is the domination recursion `HomTwistSystem.toDomination`: `h(S_i, W S_j)` is at most
`g ∑_k n_k`, with `g = max h(S_i, S_k)` and `n` the `j`-th column of the product of the
transvections of the letters. With the zero diagonal that `T_S S = S[-1]` gives, the transvection
of a letter at `S_c` is the single twist `1 + e_c G_{c*}` of the coupling graph
`G_{ik} = h(S_i, S_k)` (`i ≠ k`) (`HomTwistSystem.cast_dom`), and the single twists of a bipartite
graph have joint spectral radius at most `ρ_s` (`Matrix.jointSpectralRadius_graphTransvection_le`).
That `e^η = ρ_s` on a heaviest edge with letters of both signs is not claimed here: it needs the
signed lower bound of the sign rule.
-/

open Filter Topology Real

namespace HomTwistSystem

open Matrix
open scoped Matrix.Norms.Operator

variable {G Obj ι α : Type*} [Group G] [MulAction G Obj] (H : HomTwistSystem G Obj ι α)
variable [Fintype ι] [DecidableEq ι]

/-- The coupling graph of the centres: `h(S_i, S_k)` off the diagonal and `0` on it. -/
def couplingGraph : Matrix ι ι ℝ := fun i k => if k = i then 0 else (H.h (H.S i) (H.S k) : ℝ)

omit [Fintype ι] in
lemma couplingGraph_nonneg (i k : ι) : 0 ≤ H.couplingGraph i k := by
  unfold couplingGraph
  split_ifs <;> positivity

omit [Fintype ι] in
lemma cast_coupling (a : α) (k : ι) : (H.coupling a k : ℝ) = H.couplingGraph (H.c a) k := by
  unfold coupling couplingGraph
  split_ifs <;> simp

/-- **One step of the domination recursion is a single twist of the coupling graph.** -/
lemma cast_step (a : α) (n : ι → ℕ) :
    (fun k => ((H.toDomination.step a n k : ℕ) : ℝ)) =
      graphTransvection H.couplingGraph (H.c a) *ᵥ fun k => (n k : ℝ) := by
  funext k
  rw [graphTransvection_mulVec_apply]
  show ((n k + if k = H.c a then ∑ j, H.coupling a j * n j else 0 : ℕ) : ℝ) =
    (n k : ℝ) + if k = H.c a then (H.couplingGraph *ᵥ fun k => (n k : ℝ)) (H.c a) else 0
  push_cast
  congr 1
  split_ifs
  · simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [H.cast_coupling]
  · rfl

/-- **The domination recursion is the product of single twists of the coupling graph.** -/
lemma cast_dom (w : List α) (n : ι → ℕ) :
    (fun k => ((H.toDomination.dom w n k : ℕ) : ℝ)) =
      (w.map fun a => graphTransvection H.couplingGraph (H.c a)).prod *ᵥ fun k => (n k : ℝ) := by
  induction w with
  | nil => simp [DominationSystem.dom]
  | cons a w ih =>
    have e : H.toDomination.dom (a :: w) n = H.toDomination.step a (H.toDomination.dom w n) := rfl
    rw [e, H.cast_step, ih, List.map_cons, List.prod_cons, mulVec_mulVec]

/-- **Counts by the product of single twists**: `h(S_i, W S_j) ≤ g |ι| ‖P_W‖`, where `P_W` is the
product of the single twists of the coupling graph at the centres of the letters of `W`. -/
theorem h_word_le_norm (i j : ι) (w : List α) :
    (H.h (H.S i) (H.word w • H.S j) : ℝ) ≤
      H.centreMax * Fintype.card ι *
        ‖(w.map fun a => graphTransvection H.couplingGraph (H.c a)).prod‖ := by
  set P := (w.map fun a => graphTransvection H.couplingGraph (H.c a)).prod with hP
  have hrec := H.toDomination.test_word_le w j (H.S i)
  change (H.h (H.S i) (H.word w • H.S j) : ℝ) ≤
    ∑ k, (H.toDomination.dom w (Pi.single j 1) k : ℝ) * H.h (H.S i) (H.S k) at hrec
  set n := fun k => ((H.toDomination.dom w (Pi.single j 1) k : ℕ) : ℝ) with hn
  have hcast := H.cast_dom w (Pi.single j 1)
  have hn0 : ∀ k, 0 ≤ n k := fun k => Nat.cast_nonneg _
  have hg : ∀ k, (H.h (H.S i) (H.S k) : ℝ) ≤ H.centreMax := fun k => by
    exact_mod_cast H.le_centreMax i k
  have hsum : ∑ k, n k * (H.h (H.S i) (H.S k) : ℝ) ≤ H.centreMax * ∑ k, n k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hg k) (hn0 k)
  -- `∑ n ≤ |ι| ‖n‖ ≤ |ι| ‖P‖ ‖e_j‖ ≤ |ι| ‖P‖`
  have he : ‖(fun k => ((Pi.single j 1 : ι → ℕ) k : ℝ))‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have hnorm : ‖n‖ ≤ ‖P‖ := by
    have : n = P *ᵥ fun k => ((Pi.single j 1 : ι → ℕ) k : ℝ) := hcast
    rw [this]
    refine (linfty_opNorm_mulVec _ _).trans ?_
    calc ‖P‖ * ‖(fun k => ((Pi.single j 1 : ι → ℕ) k : ℝ))‖ ≤ ‖P‖ * 1 := by gcongr
      _ = ‖P‖ := mul_one _
  have hsumn : ∑ k, n k ≤ Fintype.card ι * ‖P‖ := by
    calc ∑ k, n k ≤ ∑ _k : ι, ‖n‖ := Finset.sum_le_sum fun k _ =>
          (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm n k)
      _ = Fintype.card ι * ‖n‖ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card ι * ‖P‖ := by gcongr
  have hg0 : (0 : ℝ) ≤ H.centreMax := Nat.cast_nonneg _
  calc (H.h (H.S i) (H.word w • H.S j) : ℝ) ≤ ∑ k, n k * (H.h (H.S i) (H.S k) : ℝ) := hrec
    _ ≤ H.centreMax * ∑ k, n k := hsum
    _ ≤ H.centreMax * (Fintype.card ι * ‖P‖) := by gcongr
    _ = H.centreMax * Fintype.card ι * ‖P‖ := by ring

variable [Fintype α]

/-- **The bipartite bound on the centre counts.** If the centres are two-coloured by `p` with
`h(S_i, S_k) = 0` for distinct centres of one colour and `h(S_i, S_k) ≤ s` for distinct centres,
`s ≥ 1`, then for every `R > ρ_s = (s + √(s² + 4))/2` there is `C` with `P_q ≤ C R^q`. -/
theorem exists_maxCount_le_of_bipartite [Nonempty ι] (p : ι → Bool)
    (hbip : ∀ i k, i ≠ k → p i = p k → H.h (H.S i) (H.S k) = 0) {s : ℝ} (hs : 1 ≤ s)
    (hle : ∀ i k, i ≠ k → (H.h (H.S i) (H.S k) : ℝ) ≤ s) {R : ℝ}
    (hR : (s + √(s ^ 2 + 4)) / 2 < R) :
    ∃ C, ∀ q, (H.maxCount q : ℝ) ≤ C * R ^ q := by
  have hG : ∀ i k, 0 ≤ H.couplingGraph i k := H.couplingGraph_nonneg
  have hbip' : ∀ i k, p i = p k → H.couplingGraph i k = 0 := by
    intro i k hp
    unfold couplingGraph
    split_ifs with hki
    · rfl
    · rw [hbip i k (Ne.symm hki) hp, Nat.cast_zero]
  have hle' : ∀ i k, H.couplingGraph i k ≤ s := by
    intro i k
    unfold couplingGraph
    split_ifs with hki
    · linarith
    · exact hle i k (Ne.symm hki)
  have hJ := jointSpectralRadius_graphTransvection_le hG p hbip' hle' hs
  obtain ⟨C, hC⟩ := exists_sphereMax_le_mul_pow (graphTransvection H.couplingGraph)
    (hJ.trans_lt hR)
  have hρ1 : 1 ≤ (s + √(s ^ 2 + 4)) / 2 := by
    have : 2 ≤ √(s ^ 2 + 4) := by
      rw [show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hR1 : 1 ≤ R := hρ1.trans hR.le
  set K := (H.centreMax : ℝ) * Fintype.card ι with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * max C 0, fun q => ?_⟩
  obtain ⟨i, j, w, hw, hP⟩ := H.exists_maxCount_eq q
  rw [hP]
  refine (H.h_word_le_norm i j w).trans ?_
  have hword : (w.map fun a => graphTransvection H.couplingGraph (H.c a)).prod =
      (List.ofFn (graphTransvection H.couplingGraph ∘ fun t => H.c (w.get t))).prod := by
    conv_lhs => rw [← List.ofFn_get w]
    rw [List.map_ofFn]
    rfl
  have h1 : ‖(w.map fun a => graphTransvection H.couplingGraph (H.c a)).prod‖ ≤
      max C 0 * R ^ q := by
    rw [hword]
    refine (Monoid.le_sphereMax _ (‖·‖) _).trans ((hC w.length).trans ?_)
    calc C * R ^ w.length ≤ max C 0 * R ^ w.length := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * R ^ q := by gcongr
  calc K * ‖(w.map fun a => graphTransvection H.couplingGraph (H.c a)).prod‖
      ≤ K * (max C 0 * R ^ q) := by gcongr
    _ = K * max C 0 * R ^ q := by ring

/-- **The bipartite bound `e^η ≤ ρ_s`.** Under the hypotheses of the exponent theorem ((L),
sphericity and directed connectivity), a twist system on a bipartite configuration of centres with
counts at most `s ≥ 1` between distinct centres has `e^η ≤ ρ_s = (s + √(s² + 4))/2`. -/
theorem exp_homExponent_le_of_bipartite [Nonempty ι] (hL : H.LowerBound) (hsph : H.IsSpherical)
    {d : ℕ} (hconn : H.DirectedConnected d) (p : ι → Bool)
    (hbip : ∀ i k, i ≠ k → p i = p k → H.h (H.S i) (H.S k) = 0) {s : ℝ} (hs : 1 ≤ s)
    (hle : ∀ i k, i ≠ k → (H.h (H.S i) (H.S k) : ℝ) ≤ s) :
    exp H.homExponent ≤ (s + √(s ^ 2 + 4)) / 2 := by
  have hη := H.tendsto_homExponent hL hsph hconn
  refine le_of_forall_gt_imp_ge_of_dense fun R hR => ?_
  obtain ⟨C, hC⟩ := H.exists_maxCount_le_of_bipartite p hbip hs hle hR
  have hρ0 : 0 < (s + √(s ^ 2 + 4)) / 2 := by
    have := Real.sqrt_nonneg (s ^ 2 + 4)
    linarith
  have hR0 : 0 < R := hρ0.trans hR
  have hP2 : ∀ N, (2 : ℝ) ≤ H.maxCount N := fun N => by exact_mod_cast H.two_le_maxCount hsph N
  have hC0 : 0 < C := by
    have := (hP2 0).trans (hC 0)
    simp only [pow_zero, mul_one] at this
    linarith
  have hlim : Tendsto (fun N : ℕ => log C / N + log R) atTop (𝓝 (log R)) := by
    have := (tendsto_const_nhds (x := log C)).div_atTop tendsto_natCast_atTop_atTop
    simpa using this.add_const (log R)
  have hle' : H.homExponent ≤ log R := by
    refine le_of_tendsto_of_tendsto hη hlim ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : log (H.maxCount N) ≤ log C + N * log R := by
      rw [← log_pow, ← log_mul hC0.ne' (by positivity)]
      exact log_le_log (by linarith [hP2 N]) (hC N)
    rw [div_add' _ _ _ hN'.ne', div_le_div_iff_of_pos_right hN']
    linarith
  calc exp H.homExponent ≤ exp (log R) := exp_le_exp.2 hle'
    _ = R := exp_log hR0

end HomTwistSystem
