/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Discrete
import K3Twists.Analysis.Convex.Birkhoff2

/-!
# Iterated function systems: the coding map and the Cantor embedding

Let `f_b : X → X`, `b ∈ β`, be finitely many maps of a nonempty complete metric space, all
`K`-Lipschitz with `K < 1`. For an infinite word `ω : ℕ → β` the composites
`F_{ω|n} = f_{ω 0} ∘ ⋯ ∘ f_{ω (n-1)}` (`IFS.comp`) converge, from every start, to a point
`π(ω)` (`IFS.codingMap`; Hutchinson, Indiana Univ. Math. J. 30 (1981)). The coding map satisfies
the shift equation `π(ω) = f_{ω 0}(π(σω))`, converges uniformly and is continuous for the product
topology; a word of period `p` is sent to the unique fixed point of `F_{ω|p}`; and when the letters
are injective with pairwise disjoint images it is a closed embedding of `β^ℕ`, a Cantor set.

## The two-block alphabet

For two spherical twists `T₁, T₂` whose centres have a `g`-dimensional space of morphisms
between them, the blocks `T₁² T₂^{-b}` act on the cell counts of the two centres by
`M_b = [[1 + 2bg², 2g], [bg, 1]]` (`Matrix.twoTwistBlock`). The count matrices are the input
here; that the counts transform by them is a statement about twist functors, not proved in this
library. The ratio map of `M_bᵀ` is `f_b(x) = bg + 1 / (2g + 1/x)`, and its Birkhoff
coefficient is `(√(1 + 2bg²) - √(2bg²)) / (√(1 + 2bg²) + √(2bg²)) < 1`
(`Matrix.birkhoffCoeff_twoTwistBlock`). In logarithmic coordinates the letters `b ∈ {2, 4}`
form an iterated function system on `ℝ` (`IFS.twoBlockLetter`), so:

* every infinite word has a centre ratio `x(ω)` (`IFS.centreRatio`), the limit of the finite
  continued fractions from any positive start (`IFS.tendsto_centreRatio`), with
  `x(ω) = b₀g + 1 / (2g + 1 / x(σω))`, that is `x(ω) = [b₀g; 2g, b₁g, 2g, b₂g, …]`
  (`IFS.centreRatio_eq`);
* a periodic word has the fixed ratio of its period (`IFS.centreRatio_periodic`), the unique
  fixed point of the composite of its letters (`IFS.eq_codingMap_of_periodic`);
* for `g ≥ 1/2` the centre ratio is a closed embedding of `{2, 4}^ℕ` into `ℝ`
  (`IFS.isClosedEmbedding_centreRatio`): the images of the two letters lie in the disjoint
  intervals `(bg, bg + 1/(2g))`.

That the centre ratios are the limiting mass profiles of the words needs, besides these counts,
a comparison of masses with counts along continuations, which is not formalized; only the
matrix and coding-map core is proved here.
-/

open Filter Topology Set Real
open scoped NNReal

namespace IFS

variable {X β : Type*} (f : β → X → X)

/-- The shift of an infinite word. -/
def shift (ω : ℕ → β) : ℕ → β := fun i ↦ ω (i + 1)

/-- The composite `f_{ω 0} ∘ f_{ω 1} ∘ ⋯ ∘ f_{ω (n-1)}` along the first `n` letters of `ω`. -/
def comp : ℕ → (ℕ → β) → X → X
  | 0, _ => id
  | n + 1, ω => f (ω 0) ∘ comp n (shift ω)

@[simp]
lemma comp_zero (ω : ℕ → β) (x : X) : comp f 0 ω x = x := rfl

lemma comp_succ (n : ℕ) (ω : ℕ → β) (x : X) :
    comp f (n + 1) ω x = f (ω 0) (comp f n (shift ω) x) := rfl

/-- Composites split at any length: `F_{ω|m+n} = F_{ω|m} ∘ F_{(σ^m ω)|n}`. -/
lemma comp_add (m n : ℕ) (ω : ℕ → β) (x : X) :
    comp f (m + n) ω x = comp f m ω (comp f n (fun i ↦ ω (i + m)) x) := by
  induction m generalizing ω with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, comp_succ, ih, comp_succ]
    congr 3

lemma comp_succ' (n : ℕ) (ω : ℕ → β) (x : X) :
    comp f (n + 1) ω x = comp f n ω (f (ω n) x) := by
  rw [comp_add]
  simp [comp_succ]

variable [MetricSpace X] {f} {K : ℝ≥0}

lemma lipschitzWith_comp (hf : ∀ b, LipschitzWith K (f b)) (n : ℕ) (ω : ℕ → β) :
    LipschitzWith (K ^ n) (comp f n ω) := by
  induction n generalizing ω with
  | zero =>
    rw [pow_zero]
    exact LipschitzWith.id
  | succ n ih =>
    rw [pow_succ']
    exact (hf (ω 0)).comp (ih (shift ω))

lemma dist_comp_succ_le (hf : ∀ b, LipschitzWith K (f b)) {x : X} {D : ℝ}
    (hD : ∀ b, dist (f b x) x ≤ D) (n : ℕ) (ω : ℕ → β) :
    dist (comp f n ω x) (comp f (n + 1) ω x) ≤ D * (K : ℝ) ^ n := by
  rw [comp_succ', dist_comm]
  refine ((lipschitzWith_comp hf n ω).dist_le_mul _ _).trans ?_
  rw [NNReal.coe_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hD _) (by positivity)

section Topology

variable [TopologicalSpace β] [DiscreteTopology β]

lemma continuous_comp (hf : ∀ b, LipschitzWith K (f b)) (n : ℕ) (x : X) :
    Continuous fun ω : ℕ → β ↦ comp f n ω x := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hshift : Continuous (shift : (ℕ → β) → ℕ → β) :=
      continuous_pi fun i ↦ continuous_apply (i + 1)
    have hF : Continuous fun p : β × X ↦ f p.1 p.2 :=
      continuous_prod_of_discrete_left.2 fun b ↦ (hf b).continuous
    exact hF.comp ((continuous_apply 0).prodMk (ih.comp hshift))

end Topology

variable [Finite β]

/-- A bound on the displacement `dist (f_b x) x` over the finitely many letters. -/
lemma exists_dist_le (x : X) : ∃ D : ℝ, 0 ≤ D ∧ ∀ b, dist (f b x) x ≤ D := by
  obtain ⟨D, hD⟩ := (Set.finite_range fun b ↦ dist (f b x) x).bddAbove
  exact ⟨max D 0, le_max_right _ _, fun b ↦ (hD ⟨b, rfl⟩).trans (le_max_left _ _)⟩

lemma cauchySeq_comp (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1) (ω : ℕ → β) (x : X) :
    CauchySeq fun n ↦ comp f n ω x := by
  obtain ⟨D, -, hD⟩ := exists_dist_le (f := f) x
  exact cauchySeq_of_le_geometric (K : ℝ) D hK (dist_comp_succ_le hf hD · ω)

variable [CompleteSpace X] [Nonempty X]

open Classical in
/-- The **coding map** of an iterated function system: the limit of `F_{ω|n}(x)` as `n → ∞`,
which exists and does not depend on `x` when the maps are uniform contractions
(`tendsto_comp_codingMap`). -/
noncomputable def codingMap (f : β → X → X) (ω : ℕ → β) : X :=
  limUnder atTop fun n ↦ comp f n ω (Classical.arbitrary X)

/-- From every start, `F_{ω|n}(x)` converges to the coding map at `ω`. -/
theorem tendsto_comp_codingMap (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1) (ω : ℕ → β)
    (x : X) : Tendsto (fun n ↦ comp f n ω x) atTop (𝓝 (codingMap f ω)) := by
  have h₀ : Tendsto (fun n ↦ comp f n ω (Classical.arbitrary X)) atTop (𝓝 (codingMap f ω)) :=
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_comp hf hK ω _))
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg)
    (fun n ↦ dist_triangle _ (comp f n ω (Classical.arbitrary X)) _) ?_)
  have hKn : Tendsto (fun n ↦ (K : ℝ) ^ n * dist x (Classical.arbitrary X)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one K.2 hK).mul_const
      (dist x (Classical.arbitrary X))
  have := hKn.add (tendsto_iff_dist_tendsto_zero.1 h₀)
  rw [add_zero] at this
  refine squeeze_zero (fun _ ↦ by positivity) (fun n ↦ ?_) this
  gcongr
  simpa using (lipschitzWith_comp hf n ω).dist_le_mul x (Classical.arbitrary X)

/-- The **shift equation**: `π(ω) = f_{ω 0}(π(σ ω))`. -/
theorem codingMap_eq (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1) (ω : ℕ → β) :
    codingMap f ω = f (ω 0) (codingMap f (shift ω)) := by
  have x : X := Classical.arbitrary X
  have h1 := (tendsto_add_atTop_iff_nat 1).2 (tendsto_comp_codingMap hf hK ω x)
  have h2 := ((hf (ω 0)).continuous.tendsto _).comp (tendsto_comp_codingMap hf hK (shift ω) x)
  exact tendsto_nhds_unique h1 (h2.congr fun n ↦ (comp_succ f n ω x).symm)

/-- `π(ω) = F_{ω|n}(π(σⁿ ω))`. -/
theorem codingMap_eq_comp (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1) (n : ℕ)
    (ω : ℕ → β) : codingMap f ω = comp f n ω (codingMap f fun i ↦ ω (i + n)) := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih =>
    rw [codingMap_eq hf hK, ih, comp_succ]
    congr 3

/-- The coding map lies within `D / (1 - K)` of any start `x`, `D` a bound on `dist (f_b x) x`. -/
lemma dist_codingMap_le (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1) {x : X} {D : ℝ}
    (hD : ∀ b, dist (f b x) x ≤ D) (ω : ℕ → β) : dist x (codingMap f ω) ≤ D / (1 - K) := by
  simpa using dist_le_of_le_geometric_of_tendsto₀ (K : ℝ) D hK (dist_comp_succ_le hf hD · ω)
    (tendsto_comp_codingMap hf hK ω x)

/-- `F_{ω|n}(x)` converges to the coding map uniformly in `ω`. -/
theorem tendstoUniformly_comp (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1) (x : X) :
    TendstoUniformly (fun n ω ↦ comp f n ω x) (codingMap f) atTop := by
  obtain ⟨D, hD0, hD⟩ := exists_dist_le (f := f) x
  have hb : ∀ n (ω : ℕ → β), dist (codingMap f ω) (comp f n ω x) ≤ (K : ℝ) ^ n * (D / (1 - K)) := by
    intro n ω
    rw [codingMap_eq_comp hf hK n ω, dist_comm]
    refine ((lipschitzWith_comp hf n ω).dist_le_mul _ _).trans ?_
    rw [NNReal.coe_pow]
    gcongr
    exact dist_codingMap_le hf hK hD _
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim : Tendsto (fun n ↦ (K : ℝ) ^ n * (D / (1 - K))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one K.2 hK).mul_const (D / (1 - K))
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn ω
  exact (hb n ω).trans_lt hn

/-- **Periodic words give fixed points**: if `ω` has period `p`, then `π(ω)` is a fixed point of
`F_{ω|p}`, and it is the only one. -/
theorem comp_codingMap_of_periodic (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1) {p : ℕ}
    {ω : ℕ → β} (hω : ∀ i, ω (i + p) = ω i) : comp f p ω (codingMap f ω) = codingMap f ω := by
  conv_rhs => rw [codingMap_eq_comp hf hK p ω]
  simp only [hω]

theorem eq_codingMap_of_periodic (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1) {p : ℕ}
    (hp : 0 < p) {ω : ℕ → β} (hω : ∀ i, ω (i + p) = ω i) {y : X} (hy : comp f p ω y = y) :
    y = codingMap f ω := by
  have h := (lipschitzWith_comp hf p ω).dist_le_mul y (codingMap f ω)
  rw [hy, comp_codingMap_of_periodic hf hK hω] at h
  have hKp : ((K ^ p : ℝ≥0) : ℝ) < 1 := by
    rw [NNReal.coe_pow]
    exact pow_lt_one₀ K.2 hK hp.ne'
  exact dist_le_zero.1 (by nlinarith [dist_nonneg (x := y) (y := codingMap f ω)])

/-- With injective letters whose images are pairwise disjoint, the coding map is injective. -/
theorem codingMap_injective (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1)
    (hinj : ∀ b, Function.Injective (f b))
    (hdisj : Pairwise fun b b' ↦ Disjoint (range (f b)) (range (f b'))) :
    Function.Injective (codingMap f : (ℕ → β) → X) := by
  have key : ∀ n (ω ω' : ℕ → β), codingMap f ω = codingMap f ω' → ω n = ω' n := by
    intro n
    induction n with
    | zero =>
      intro ω ω' h
      by_contra hne
      rw [codingMap_eq hf hK ω, codingMap_eq hf hK ω'] at h
      exact Set.disjoint_left.1 (hdisj hne) (Set.mem_range_self _)
        (by rw [h]; exact Set.mem_range_self _)
    | succ n ih =>
      intro ω ω' h
      have h0 : ω 0 = ω' 0 := by
        by_contra hne
        rw [codingMap_eq hf hK ω, codingMap_eq hf hK ω'] at h
        exact Set.disjoint_left.1 (hdisj hne) (Set.mem_range_self _)
          (by rw [h]; exact Set.mem_range_self _)
      rw [codingMap_eq hf hK ω, codingMap_eq hf hK ω', h0] at h
      exact ih (shift ω) (shift ω') (hinj _ h)
  exact fun ω ω' h ↦ funext fun n ↦ key n ω ω' h

section Topology

variable [TopologicalSpace β] [DiscreteTopology β]

/-- The coding map is continuous for the product topology on infinite words. -/
theorem continuous_codingMap (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1) :
    Continuous (codingMap f : (ℕ → β) → X) :=
  (tendstoUniformly_comp hf hK (Classical.arbitrary X)).continuous
    (Frequently.of_forall fun n ↦ continuous_comp hf n (Classical.arbitrary X))

/-- **The Cantor embedding**: for finitely many injective uniform contractions with pairwise
disjoint images, the coding map is a closed embedding of the space of infinite words (a Cantor
set when there are at least two letters). -/
theorem isClosedEmbedding_codingMap (hf : ∀ b, LipschitzWith K (f b)) (hK : K < 1)
    (hinj : ∀ b, Function.Injective (f b))
    (hdisj : Pairwise fun b b' ↦ Disjoint (range (f b)) (range (f b'))) :
    Topology.IsClosedEmbedding (codingMap f : (ℕ → β) → X) := by
  have : CompactSpace β := Finite.compactSpace
  exact (continuous_codingMap hf hK).isClosedEmbedding (codingMap_injective hf hK hinj hdisj)

end Topology

end IFS

/-! ### The two-block alphabet -/

namespace Matrix

/-- The count matrix `[[1 + 2bg², 2g], [bg, 1]]` of a block `T₁² T₂^{-b}` of two spherical twists
with `g` arrows between the two centres. -/
def twoTwistBlock (b g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + 2 * b * g ^ 2, 2 * g; b * g, 1]

variable {b g : ℝ}

lemma twoTwistBlock_pos (hb : 0 < b) (hg : 0 < g) (i j : Fin 2) : 0 < twoTwistBlock b g i j := by
  fin_cases i <;> fin_cases j <;> simp [twoTwistBlock] <;> positivity

lemma transpose_twoTwistBlock_pos (hb : 0 < b) (hg : 0 < g) (i j : Fin 2) :
    0 < (twoTwistBlock b g)ᵀ i j :=
  twoTwistBlock_pos hb hg j i

/-- The Birkhoff coefficient of the transpose is that of the matrix. -/
lemma birkhoffCoeff_transpose (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Mᵀ.birkhoffCoeff = M.birkhoffCoeff := by
  simp only [birkhoffCoeff, transpose_apply, mul_comm (M 1 0) (M 0 1)]

/-- The Birkhoff coefficient of a block: `(√(1 + 2bg²) - √(2bg²)) / (√(1 + 2bg²) + √(2bg²))`. -/
lemma birkhoffCoeff_twoTwistBlock :
    (twoTwistBlock b g).birkhoffCoeff =
      (√(1 + 2 * b * g ^ 2) - √(2 * b * g ^ 2)) / (√(1 + 2 * b * g ^ 2) + √(2 * b * g ^ 2)) := by
  have h : √(2 * b * g ^ 2) ≤ √(1 + 2 * b * g ^ 2) := Real.sqrt_le_sqrt (by linarith)
  simp only [birkhoffCoeff, twoTwistBlock, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, mul_one]
  rw [show 2 * g * (b * g) = 2 * b * g ^ 2 by ring, abs_of_nonneg (sub_nonneg.2 h)]

/-- The ratio map of the transposed block is `f_b(x) = bg + x / (2gx + 1)`. -/
lemma ratioMap_transpose_twoTwistBlock (x : ℝ) :
    (twoTwistBlock b g)ᵀ.ratioMap x = (1 + 2 * b * g ^ 2) * x / (2 * g * x + 1) +
      b * g / (2 * g * x + 1) := by
  simp [ratioMap, twoTwistBlock, add_div]

lemma ratioMap_transpose_twoTwistBlock_eq (hg : 0 ≤ g) {x : ℝ} (hx : 0 < x) :
    (twoTwistBlock b g)ᵀ.ratioMap x = b * g + x / (2 * g * x + 1) := by
  rw [ratioMap_transpose_twoTwistBlock]
  have : 0 < 2 * g * x + 1 := by positivity
  field_simp
  ring

/-- The **continued-fraction step**: `f_b(x) = bg + 1 / (2g + 1 / x)`. -/
lemma ratioMap_transpose_twoTwistBlock_eq_cf (hg : 0 ≤ g) {x : ℝ} (hx : 0 < x) :
    (twoTwistBlock b g)ᵀ.ratioMap x = b * g + 1 / (2 * g + 1 / x) := by
  rw [ratioMap_transpose_twoTwistBlock_eq hg hx]
  congr 1
  field_simp

end Matrix

namespace IFS

open Matrix

/-- The block exponents: `b = 2` for `false`, `b = 4` for `true`. -/
def blockExponent : Bool → ℝ
  | false => 2
  | true => 4

lemma blockExponent_pos (c : Bool) : 0 < blockExponent c := by
  cases c <;> norm_num [blockExponent]

/-- The letter of the two-block alphabet in logarithmic coordinates:
`u ↦ log f_b(e^u)`, `f_b(x) = bg + 1 / (2g + 1/x)` the ratio map of the transposed block. -/
noncomputable def twoBlockLetter (g : ℝ) (c : Bool) (u : ℝ) : ℝ :=
  log ((twoTwistBlock (blockExponent c) g)ᵀ.ratioMap (exp u))

/-- The common contraction constant of the two letters, the larger Birkhoff coefficient. -/
noncomputable def twoBlockConst (g : ℝ) : ℝ≥0 :=
  (max (twoTwistBlock 2 g).birkhoffCoeff (twoTwistBlock 4 g).birkhoffCoeff).toNNReal

variable {g : ℝ}

lemma twoBlockConst_lt_one (hg : 0 < g) : twoBlockConst g < 1 := by
  rw [twoBlockConst, Real.toNNReal_lt_one]
  exact max_lt (birkhoffCoeff_lt_one (twoTwistBlock_pos two_pos hg))
    (birkhoffCoeff_lt_one (twoTwistBlock_pos four_pos hg))

lemma ratioMap_pos (hg : 0 < g) (c : Bool) {x : ℝ} (hx : 0 < x) :
    0 < (twoTwistBlock (blockExponent c) g)ᵀ.ratioMap x := by
  rw [ratioMap_transpose_twoTwistBlock_eq hg.le hx]
  have := blockExponent_pos c
  positivity

lemma lipschitzWith_twoBlockLetter (hg : 0 < g) (c : Bool) :
    LipschitzWith (twoBlockConst g) (twoBlockLetter g c) := by
  refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
  rw [Real.dist_eq, Real.dist_eq, twoBlockConst,
    Real.coe_toNNReal _ (le_max_of_le_left birkhoffCoeff_nonneg)]
  have h := abs_log_ratioMap_sub_le (transpose_twoTwistBlock_pos (blockExponent_pos c) hg)
    (exp_pos u) (exp_pos v)
  rw [Real.log_exp, Real.log_exp, birkhoffCoeff_transpose] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  cases c
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma twoBlockLetter_strictMono (hg : 0 < g) (c : Bool) : StrictMono (twoBlockLetter g c) := by
  intro u v huv
  have hx := exp_pos u
  have hy := exp_pos v
  have hxy := Real.exp_lt_exp.2 huv
  refine Real.log_lt_log (ratioMap_pos hg c hx) ?_
  rw [ratioMap_transpose_twoTwistBlock_eq hg.le hx, ratioMap_transpose_twoTwistBlock_eq hg.le hy,
    add_lt_add_iff_left, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The letter `b = 2` takes values below `2g + 1/(2g)` and the letter `b = 4` above `4g`. -/
lemma twoBlockLetter_range_disjoint (hg : 1 / 2 ≤ g) :
    Pairwise fun c c' : Bool ↦
      Disjoint (range (twoBlockLetter g c)) (range (twoBlockLetter g c')) := by
  have hg0 : 0 < g := by linarith
  -- the two ratio maps take values in `(bg, bg + 1/(2g))`
  have hbd : ∀ (c : Bool) (u : ℝ), blockExponent c * g <
      (twoTwistBlock (blockExponent c) g)ᵀ.ratioMap (exp u) ∧
      (twoTwistBlock (blockExponent c) g)ᵀ.ratioMap (exp u) <
        blockExponent c * g + 1 / (2 * g) := by
    intro c u
    have hx := exp_pos u
    rw [ratioMap_transpose_twoTwistBlock_eq hg0.le hx]
    refine ⟨lt_add_of_pos_right _ (by positivity), (add_lt_add_iff_left _).2 ?_⟩
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsep : 2 * g + 1 / (2 * g) ≤ 4 * g := by
    rw [div_le_iff₀ (by positivity)] at *
    have : 1 / (2 * g) ≤ 2 * g := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have key : ∀ u v, twoBlockLetter g false u ≠ twoBlockLetter g true v := by
    intro u v h
    have h' := Real.log_injOn_pos (Set.mem_Ioi.2 (ratioMap_pos hg0 false (exp_pos u)))
      (Set.mem_Ioi.2 (ratioMap_pos hg0 true (exp_pos v))) h
    have h1 := (hbd false u).2
    have h2 := (hbd true v).1
    simp only [blockExponent] at h1 h2 h'
    linarith
  intro c c' hcc'
  rw [Set.disjoint_left]
  rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
  cases c <;> cases c'
  · exact hcc' rfl
  · exact key u v hv.symm
  · exact key v u hv
  · exact hcc' rfl

/-- The **centre ratio** of an infinite word in the two blocks `b ∈ {2, 4}`. -/
noncomputable def centreRatio (g : ℝ) (ω : ℕ → Bool) : ℝ := exp (codingMap (twoBlockLetter g) ω)

lemma centreRatio_pos (ω : ℕ → Bool) : 0 < centreRatio g ω := exp_pos _

/-- **The continued fraction**: `x(ω) = b₀g + 1 / (2g + 1 / x(σω))`, so that
`x(ω) = [b₀g; 2g, b₁g, 2g, b₂g, …]`. -/
theorem centreRatio_eq (hg : 0 < g) (ω : ℕ → Bool) :
    centreRatio g ω = blockExponent (ω 0) * g + 1 / (2 * g + 1 / centreRatio g (shift ω)) := by
  rw [centreRatio, codingMap_eq (lipschitzWith_twoBlockLetter hg) (twoBlockConst_lt_one hg),
    twoBlockLetter, Real.exp_log (ratioMap_pos hg _ (exp_pos _)),
    ratioMap_transpose_twoTwistBlock_eq_cf hg.le (exp_pos _), centreRatio]

/-- The convergents: from any start `x₀ = exp u₀ > 0` the finite continued fractions
`[b₀g; 2g, …, b_{n-1}g, 2g, x₀]` (`exp_comp_succ`) converge to the centre ratio. -/
theorem tendsto_centreRatio (hg : 0 < g) (ω : ℕ → Bool) (u₀ : ℝ) :
    Tendsto (fun n ↦ exp (comp (twoBlockLetter g) n ω u₀)) atTop (𝓝 (centreRatio g ω)) :=
  (continuous_exp.tendsto _).comp
    (tendsto_comp_codingMap (lipschitzWith_twoBlockLetter hg) (twoBlockConst_lt_one hg) ω _)

lemma exp_comp_succ (hg : 0 < g) (n : ℕ) (ω : ℕ → Bool) (u : ℝ) :
    exp (comp (twoBlockLetter g) (n + 1) ω u) = blockExponent (ω 0) * g +
      1 / (2 * g + 1 / exp (comp (twoBlockLetter g) n (shift ω) u)) := by
  rw [comp_succ, twoBlockLetter, Real.exp_log (ratioMap_pos hg _ (exp_pos _)),
    ratioMap_transpose_twoTwistBlock_eq_cf hg.le (exp_pos _)]

/-- **The Cantor embedding of the two-block words**: for `g ≥ 1/2` the centre ratio is a closed
embedding of `{2, 4}^ℕ` into `ℝ`. -/
theorem isClosedEmbedding_centreRatio (hg : 1 / 2 ≤ g) :
    Topology.IsClosedEmbedding (centreRatio g) := by
  have hg0 : 0 < g := by linarith
  have hπ := isClosedEmbedding_codingMap (lipschitzWith_twoBlockLetter hg0)
    (twoBlockConst_lt_one hg0) (fun c ↦ (twoBlockLetter_strictMono hg0 c).injective)
    (twoBlockLetter_range_disjoint hg)
  have : CompactSpace (ℕ → Bool) := inferInstance
  exact (continuous_exp.comp hπ.continuous).isClosedEmbedding
    (Real.exp_injective.comp hπ.injective)

/-- A periodic word of period `p ≥ 1` has the unique positive fixed ratio of its period. -/
theorem centreRatio_periodic (hg : 0 < g) {p : ℕ} {ω : ℕ → Bool} (hω : ∀ i, ω (i + p) = ω i) :
    comp (twoBlockLetter g) p ω (log (centreRatio g ω)) = log (centreRatio g ω) := by
  rw [centreRatio, Real.log_exp]
  exact comp_codingMap_of_periodic (lipschitzWith_twoBlockLetter hg) (twoBlockConst_lt_one hg) hω

end IFS
