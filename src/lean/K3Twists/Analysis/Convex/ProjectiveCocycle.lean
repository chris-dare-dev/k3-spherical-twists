/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import K3Twists.Analysis.Convex.IFS
import K3Twists.Analysis.Matrix.GelfandRadius

/-!
# Projective cocycles of two spherical twists: the count core

Let `T₁, T₂` be the twists along two spherical objects with a `g`-dimensional space of morphisms
between them. On the cell counts `(x, y)` of the two centres in a forward object, `T₁` acts by
the Thurston matrix `U = [[1, g], [0, 1]]` and `T₂⁻¹` by `L = [[1, 0], [g, 1]]`
(`Matrix.thurstonA 1 g`, `Matrix.thurstonB 1 g`), so `T₂` acts by `L⁻¹ = [[1, 0], [-g, 1]]` and
the block `T₁² T₂^{-b}` by `M_b = U² Lᵇ = [[1 + 2bg², 2g], [bg, 1]]` (`Matrix.twoTwistBlock`).
Along an infinite word `ω` in the blocks the count matrices form the cocycle
`Q_n = M_{ω(n-1)} ⋯ M_{ω 0}` (`Matrix.cocycle`), the first block acting first.

This file is the matrix and real-analysis core of the convergence of limiting mass profiles. Its
categorical inputs, that the counts of forward objects transform by the matrices `M_b` and that
the mass of an object for a stability condition is a positive linear form in its counts up to a
bounded error, are statements about twist functors and stability conditions that are not
formalized here, and no statement of this file is about twist functors or masses.

* **The blocks are a representation.** The count matrices of the blocks are the images of the
  block words under the representation `T₁ ↦ U`, `T₂ ↦ L⁻¹` of the free group on the two twists
  (`Matrix.twistCountRep`), so the count matrix of any word in the blocks is the product of the
  count matrices of its letters.
* **The block identity** `x' - 2g y' = x` for `(x', y') = M_b (x, y)` is the arithmetic behind
  the cusp lower bound for these words: from a nonnegative start, every count vector after the
  first block has `x ≥ 2g y`, that is `(x - y) / (3(x + y)) ≥ (2g - 1) / (3(2g + 1))`.
* **The moving-start lemma** is the unconditional core of the moving-start criterion: if
  `u_{k+1} ≥ d u_k - C` with `d > 1` and `u_0 ≥ 0`, then `∑_{k<m} u_k ≤ (u_m + C m) / (d - 1)`.
* **Projective convergence of positive cocycles with a bounded error** is the core of the
  convergence of limiting mass profiles. For finitely many `2 × 2` matrices with positive entries
  the forward products `P_n = Q_nᵀ = M_{ω 0}ᵀ ⋯ M_{ω(n-1)}ᵀ` carry every positive vector `c` to
  rays converging to a ray `u(ω) = (x(ω), 1)` that does not depend on `c`: the ratio map of `P_n`
  is the composite of the ratio maps of the transposed letters, which contract by their Birkhoff
  coefficients (`Analysis/Convex/Birkhoff2.lean`), and `log x(ω)` is the coding map of these
  contractions in logarithmic coordinates (`Analysis/Convex/IFS.lean`). Hence
  `c ⬝ Q_n t_E / c ⬝ Q_n t_P → u(ω) ⬝ t_E / u(ω) ⬝ t_P`, and the same limit holds for real numbers
  within bounded distance of numerator and denominator once the denominator tends to infinity.
  The limit does not depend on `c`, which in the intended application is the vector of masses of
  the two centres for a stability condition. For the blocks `b ∈ {2, 4}` the limit ratio is the
  centre ratio `IFS.centreRatio` and the denominators tend to infinity on their own.

## Main definitions

* `Matrix.twistCountRep g : FreeGroup (Fin 2) →* GL (Fin 2) ℝ`, the count representation, and
  `Matrix.twoTwistBlockWord b = T₁² T₂^{-b}`;
* `Matrix.cocycle M ω n = M (ω (n-1)) * ⋯ * M (ω 0)`, the cocycle of a word, whose transpose is
  the forward product `P_n` (`Matrix.transpose_cocycle_eq_list_prod`);
* `Matrix.logRatioLetter M b`, the ratio map of `(M b)ᵀ` in logarithmic coordinates;
  `Matrix.cocycleRatio M ω`, the limit ratio, and `Matrix.cocycleRay M ω = (x(ω), 1)`;
* `Matrix.twoBlockAlphabet g`, the two blocks `b ∈ {2, 4}` indexed by `Bool`.

## Main results

* `Matrix.twistCountRep_twoTwistBlockWord`, `Matrix.twistCountRep_list_prod`: `M_b = U² Lᵇ` and
  the count matrix of a word in the blocks; `Matrix.twoTwistBlock_eq_thurstonA_mul_thurstonB`:
  `M_b = U² L_b` for real `b`, `L_b = [[1, 0], [bg, 1]]`.
* `Matrix.twoTwistBlock_mulVec_zero_sub`, `Matrix.twoTwistBlock_identity`: the block identity;
  `Matrix.two_mul_le_cocycle_twoTwistBlock_mulVec`, `Matrix.two_mul_sub_one_div_le_iff`,
  `Matrix.two_mul_sub_one_div_le_cocycle_twoTwistBlock`: the cusp bound along block words.
* `sum_range_le_of_mul_sub_le`, `sum_range_le_max_one_div_mul`: the moving-start lemma.
* `Matrix.tendsto_ratio_transpose_cocycle_mulVec`, `Matrix.tendsto_smul_transpose_cocycle_mulVec`,
  `Matrix.tendsto_hilbertEDist_transpose_cocycle_mulVec`: projective convergence of a positive
  cocycle, in ratios, in normalized vectors and in Hilbert's projective metric.
* `Matrix.tendsto_dotProduct_cocycle_mulVec_div`, `Matrix.tendsto_div_of_abs_sub_le_cocycle`,
  `Matrix.tendsto_pi_div_of_abs_sub_le_cocycle`: the limiting profile, with bounded errors.
* `Matrix.exists_transpose_cocycle_mulVec_cocycleRay_eq_smul`,
  `Matrix.eq_smul_cocycleRay_of_periodic`: for a periodic word the limit ray is the Perron
  eigenvector of the product over a period, unique up to scaling among positive vectors.
* `Matrix.tendsto_dotProduct_cocycle_twoTwistBlock_atTop`: for `g > 0` and exponents bounded
  below by a positive number the denominators `c ⬝ Q_n t` tend to infinity;
  `Matrix.tendsto_div_twoBlockAlphabet`: so for the blocks `b ∈ {2, 4}` every infinite word has
  the limit `(x(ω) t_{E,0} + t_{E,1}) / (x(ω) t_{P,0} + t_{P,1})`, `x(ω)` the centre ratio, for
  every positive `c` and bounded errors, with no growth hypothesis.
* `Filter.Tendsto.div_of_isLittleO`, `Filter.Tendsto.div_of_abs_sub_le`: errors that are small
  against the denominator do not move a limit of ratios.

## Conventions

A vector of `ℝ²` is `v : Fin 2 → ℝ` with `x = v 0`, `y = v 1`; it is *positive* when both entries
are, and its ratio is `v 0 / v 1`. Products act on column vectors, `⬝ᵥ` is the dot product, and
`Q_nᵀ c = c ᵥ* Q_n`.

## References

* G. Birkhoff, *Extensions of Jentzsch's theorem*, Trans. Amer. Math. Soc. 85 (1957).
* J. E. Hutchinson, *Fractals and self-similarity*, Indiana Univ. Math. J. 30 (1981).
* W. Thurston, *On the geometry and dynamics of diffeomorphisms of surfaces*, Bull. Amer. Math.
  Soc. 19 (1988).
-/

open Filter Topology Set Real
open scoped NNReal

namespace Matrix

/-! ### The count representation -/

section Representation

variable (a a' μ : ℝ)

/-- Powers of the first twist add:
`[[1, aμ], [0, 1]] [[1, a'μ], [0, 1]] = [[1, (a + a')μ], [0, 1]]`. -/
lemma thurstonA_mul_thurstonA : thurstonA a μ * thurstonA a' μ = thurstonA (a + a') μ := by
  simp [thurstonA, add_mul, add_comm]

/-- Powers of the second twist add:
`[[1, 0], [aμ, 1]] [[1, 0], [a'μ, 1]] = [[1, 0], [(a + a')μ, 1]]`. -/
lemma thurstonB_mul_thurstonB : thurstonB a μ * thurstonB a' μ = thurstonB (a + a') μ := by
  simp [thurstonB, add_mul]

/-- The zeroth power of the first twist is the identity. -/
@[simp]
lemma thurstonA_zero : thurstonA 0 μ = 1 := by
  simp [thurstonA, one_fin_two]

/-- The zeroth power of the second twist is the identity. -/
@[simp]
lemma thurstonB_zero : thurstonB 0 μ = 1 := by
  simp [thurstonB, one_fin_two]

/-- `[[1, aμ], [0, 1]]ⁿ = [[1, naμ], [0, 1]]`. -/
lemma thurstonA_pow (n : ℕ) : thurstonA a μ ^ n = thurstonA (n * a) μ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, thurstonA_mul_thurstonA]; push_cast; ring_nf

/-- `[[1, 0], [aμ, 1]]ⁿ = [[1, 0], [naμ, 1]]`. -/
lemma thurstonB_pow (n : ℕ) : thurstonB a μ ^ n = thurstonB (n * a) μ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, thurstonB_mul_thurstonB]; push_cast; ring_nf

/-- `U² = [[1, 2g], [0, 1]]` for `U = [[1, g], [0, 1]]`, the count matrix of `T₁`. -/
lemma thurstonA_one_sq (g : ℝ) : thurstonA 1 g ^ 2 = !![1, 2 * g; 0, 1] := by
  rw [thurstonA_pow]
  norm_num [thurstonA]

/-- `Lᵇ = [[1, 0], [bg, 1]]` for `L = [[1, 0], [g, 1]]`, the count matrix of `T₂⁻¹`. -/
lemma thurstonB_one_pow (g : ℝ) (b : ℕ) : thurstonB 1 g ^ b = !![1, 0; b * g, 1] := by
  rw [thurstonB_pow, mul_one, thurstonB]

/-- The inverse of `[[1, aμ], [0, 1]]` is `[[1, -aμ], [0, 1]]`. -/
@[simp]
lemma inv_thurstonA : (thurstonA a μ)⁻¹ = thurstonA (-a) μ :=
  inv_eq_left_inv (by rw [thurstonA_mul_thurstonA, neg_add_cancel, thurstonA_zero])

/-- The inverse of `L_a = [[1, 0], [aμ, 1]]` is `[[1, 0], [-aμ, 1]]`; for `a = 1`, `μ = g` it is
`[[1, 0], [-g, 1]]`, the count matrix of `T₂`. -/
@[simp]
lemma inv_thurstonB : (thurstonB a μ)⁻¹ = thurstonB (-a) μ :=
  inv_eq_left_inv (by rw [thurstonB_mul_thurstonB, neg_add_cancel, thurstonB_zero])

/-- The Thurston matrix `[[1, aμ], [0, 1]]` as a unit, with inverse `[[1, -aμ], [0, 1]]`. -/
def thurstonAUnit : GL (Fin 2) ℝ :=
  ⟨thurstonA a μ, thurstonA (-a) μ,
    by rw [thurstonA_mul_thurstonA, add_neg_cancel, thurstonA_zero],
    by rw [thurstonA_mul_thurstonA, neg_add_cancel, thurstonA_zero]⟩

/-- The Thurston matrix `[[1, 0], [aμ, 1]]` as a unit, with inverse `[[1, 0], [-aμ, 1]]`. -/
def thurstonBUnit : GL (Fin 2) ℝ :=
  ⟨thurstonB a μ, thurstonB (-a) μ,
    by rw [thurstonB_mul_thurstonB, add_neg_cancel, thurstonB_zero],
    by rw [thurstonB_mul_thurstonB, neg_add_cancel, thurstonB_zero]⟩

/-- The matrix of the unit `thurstonAUnit a μ`. -/
@[simp]
lemma coe_thurstonAUnit : (thurstonAUnit a μ : Matrix (Fin 2) (Fin 2) ℝ) = thurstonA a μ := rfl

/-- The matrix of the unit `thurstonBUnit a μ`. -/
@[simp]
lemma coe_thurstonBUnit : (thurstonBUnit a μ : Matrix (Fin 2) (Fin 2) ℝ) = thurstonB a μ := rfl

/-- The matrix of the inverse of the unit `thurstonBUnit a μ` is `[[1, 0], [-aμ, 1]]`. -/
lemma coe_inv_thurstonBUnit :
    ((thurstonBUnit a μ)⁻¹ : GL (Fin 2) ℝ) = (thurstonB (-a) μ : Matrix (Fin 2) (Fin 2) ℝ) :=
  rfl

/-- The **count representation** of the free group on the two twists `T₁ = of 0`, `T₂ = of 1`:
`T₁ ↦ U = [[1, g], [0, 1]]` and `T₂ ↦ L⁻¹ = [[1, 0], [-g, 1]]`, so that
`T₂⁻¹ ↦ L = [[1, 0], [g, 1]]`. -/
def twistCountRep (g : ℝ) : FreeGroup (Fin 2) →* GL (Fin 2) ℝ :=
  FreeGroup.lift ![thurstonAUnit 1 g, (thurstonBUnit 1 g)⁻¹]

/-- The count representation sends `T₁` to the unit `U`. -/
@[simp]
lemma twistCountRep_of_zero (g : ℝ) :
    twistCountRep g (FreeGroup.of 0) = thurstonAUnit 1 g := by
  simp [twistCountRep]

/-- The count representation sends `T₂` to the unit `L⁻¹`. -/
@[simp]
lemma twistCountRep_of_one (g : ℝ) :
    twistCountRep g (FreeGroup.of 1) = (thurstonBUnit 1 g)⁻¹ := by
  simp [twistCountRep]

/-- `T₁` acts on counts by `U = [[1, g], [0, 1]]`. -/
lemma coe_twistCountRep_of_zero (g : ℝ) :
    (twistCountRep g (FreeGroup.of 0) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, g; 0, 1] := by
  rw [twistCountRep_of_zero, coe_thurstonAUnit, thurstonA, one_mul]

/-- `T₂` acts on counts by `L⁻¹ = [[1, 0], [-g, 1]]`. -/
lemma coe_twistCountRep_of_one (g : ℝ) :
    (twistCountRep g (FreeGroup.of 1) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; -g, 1] := by
  rw [twistCountRep_of_one, coe_inv_thurstonBUnit, thurstonB, neg_one_mul]

/-- `T₂⁻¹` acts on counts by `L = [[1, 0], [g, 1]]`. -/
lemma coe_twistCountRep_inv_of_one (g : ℝ) :
    (twistCountRep g (FreeGroup.of 1)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; g, 1] := by
  rw [map_inv, twistCountRep_of_one, inv_inv, coe_thurstonBUnit, thurstonB, one_mul]

/-- **The block as a product, for real exponents**: `M_b = U² L_b` with `L_b = [[1, 0], [bg, 1]]`,
an identity of real matrices for every real `b`. -/
theorem twoTwistBlock_eq_thurstonA_mul_thurstonB (b g : ℝ) :
    twoTwistBlock b g = thurstonA 1 g ^ 2 * thurstonB b g := by
  rw [thurstonA_pow]
  simp [twoTwistBlock, thurstonA, thurstonB]
  ring

/-- `M_b = U² Lᵇ` for a natural exponent `b`. -/
theorem twoTwistBlock_natCast (b : ℕ) (g : ℝ) :
    twoTwistBlock b g = thurstonA 1 g ^ 2 * thurstonB 1 g ^ b := by
  rw [thurstonB_pow, mul_one, twoTwistBlock_eq_thurstonA_mul_thurstonB]

/-- The block `T₁² T₂^{-b}` as a word in the free group on the two twists. -/
def twoTwistBlockWord (b : ℕ) : FreeGroup (Fin 2) := FreeGroup.of 0 ^ 2 * (FreeGroup.of 1)⁻¹ ^ b

/-- **The blocks are a representation.** The count representation sends the block word
`T₁² T₂^{-b}` to the count matrix `M_b = U² Lᵇ` of the block. -/
theorem twistCountRep_twoTwistBlockWord (g : ℝ) (b : ℕ) :
    (twistCountRep g (twoTwistBlockWord b) : Matrix (Fin 2) (Fin 2) ℝ) = twoTwistBlock b g := by
  simp [twoTwistBlockWord, twoTwistBlock_natCast]

/-- **The count matrix of a word in the blocks** is the product of the count matrices of its
letters: for exponents `b₁, …, b_k`, the image of `B_{b₁} ⋯ B_{b_k}` is `M_{b₁} ⋯ M_{b_k}`. -/
theorem twistCountRep_list_prod (g : ℝ) (bs : List ℕ) :
    (twistCountRep g (bs.map twoTwistBlockWord).prod : Matrix (Fin 2) (Fin 2) ℝ) =
      (bs.map fun b : ℕ ↦ twoTwistBlock b g).prod := by
  rw [map_list_prod, ← Units.coeHom_apply, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun b _ ↦ ?_
  simp [twistCountRep_twoTwistBlockWord]

/-- The product of the blocks over a list of natural exponents is the product of the
corresponding `U² Lᵇ`. -/
theorem list_prod_map_twoTwistBlock_natCast (g : ℝ) (bs : List ℕ) :
    (bs.map fun b : ℕ ↦ twoTwistBlock b g).prod =
      (bs.map fun b ↦ thurstonA 1 g ^ 2 * thurstonB 1 g ^ b).prod := by
  simp only [twoTwistBlock_natCast]

/-- The product of the blocks over a list of real exponents is the product of the corresponding
`U² L_b`, `L_b = [[1, 0], [bg, 1]]`. -/
theorem list_prod_map_twoTwistBlock (g : ℝ) (bs : List ℝ) :
    (bs.map fun b ↦ twoTwistBlock b g).prod =
      (bs.map fun b ↦ thurstonA 1 g ^ 2 * thurstonB b g).prod := by
  simp only [twoTwistBlock_eq_thurstonA_mul_thurstonB]

end Representation

/-! ### The cocycle of an infinite word -/

section Cocycle

variable {β γ ι R : Type*} [Fintype ι] [DecidableEq ι]

/-- The **cocycle** of an infinite word `ω` in an alphabet of matrices `M`:
`cocycle M ω n = M (ω (n-1)) * ⋯ * M (ω 0)`, the product of the matrices of the first `n` letters,
the first letter acting first. -/
def cocycle [Semiring R] (M : β → Matrix ι ι R) (ω : ℕ → β) : ℕ → Matrix ι ι R
  | 0 => 1
  | n + 1 => M (ω n) * cocycle M ω n

variable [Semiring R] (M : β → Matrix ι ι R) (ω : ℕ → β)

/-- The cocycle of the empty prefix is the identity. -/
@[simp]
lemma cocycle_zero : cocycle M ω 0 = 1 := rfl

/-- `Q_{n+1} = M (ω n) * Q_n`: the next letter acts last. -/
lemma cocycle_succ (n : ℕ) : cocycle M ω (n + 1) = M (ω n) * cocycle M ω n := rfl

/-- `Q_{n+1} v = M (ω n) (Q_n v)`. -/
lemma cocycle_mulVec_succ (n : ℕ) (v : ι → R) :
    cocycle M ω (n + 1) *ᵥ v = M (ω n) *ᵥ (cocycle M ω n *ᵥ v) := by
  rw [cocycle_succ, mulVec_mulVec]

/-- Relabelling the alphabet: the cocycle of `M ∘ e` along `ω` is that of `M` along `e ∘ ω`. -/
lemma cocycle_comp (e : γ → β) (ω : ℕ → γ) (n : ℕ) :
    cocycle (fun s ↦ M (e s)) ω n = cocycle M (fun i ↦ e (ω i)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cocycle_succ, cocycle_succ, ih]

/-- The cocycle as a list product `M (ω (n-1)) * ⋯ * M (ω 0)`. -/
lemma cocycle_eq_list_prod (n : ℕ) :
    cocycle M ω n = ((List.range n).reverse.map fun i ↦ M (ω i)).prod := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cocycle_succ, ih, List.range_succ, List.reverse_append]; simp

/-- The transposed cocycle grows on the right: `Q_{n+1}ᵀ = Q_nᵀ * (M (ω n))ᵀ`. -/
lemma transpose_cocycle_succ {R : Type*} [CommSemiring R] (M : β → Matrix ι ι R) (n : ℕ) :
    (cocycle M ω (n + 1))ᵀ = (cocycle M ω n)ᵀ * (M (ω n))ᵀ :=
  transpose_mul _ _

/-- The transposed cocycle is the forward product `P_n = (M (ω 0))ᵀ * ⋯ * (M (ω (n-1)))ᵀ`. -/
lemma transpose_cocycle_eq_list_prod {R : Type*} [CommSemiring R] (M : β → Matrix ι ι R)
    (n : ℕ) : (cocycle M ω n)ᵀ = ((List.range n).map fun i ↦ (M (ω i))ᵀ).prod := by
  induction n with
  | zero => simp
  | succ n ih => rw [transpose_cocycle_succ, ih, List.range_succ]; simp

/-- The cocycle of a word in the blocks with natural exponents `ω` is the count matrix of the word
`B_{ω(n-1)} ⋯ B_{ω 0}` under the count representation. -/
theorem coe_twistCountRep_eq_cocycle (g : ℝ) (ω : ℕ → ℕ) (n : ℕ) :
    (twistCountRep g ((List.range n).reverse.map fun i ↦ twoTwistBlockWord (ω i)).prod :
      Matrix (Fin 2) (Fin 2) ℝ) = cocycle (fun b : ℕ ↦ twoTwistBlock b g) ω n := by
  have h : ((List.range n).reverse.map fun i ↦ twoTwistBlockWord (ω i)) =
      ((List.range n).reverse.map ω).map twoTwistBlockWord := by
    rw [List.map_map]
    rfl
  rw [h, twistCountRep_list_prod, List.map_map, cocycle_eq_list_prod]
  rfl

end Cocycle

/-! ### The block identity and the cusp bound -/

section BlockIdentity

/-- **The block identity**, on the explicit formulas: for `x' = (1 + 2bg²) x + 2g y` and
`y' = bg x + y`, `x' - 2g y' = x`. -/
theorem twoTwistBlock_identity {R : Type*} [CommRing R] (b g x y : R) :
    (1 + 2 * b * g ^ 2) * x + 2 * g * y - 2 * g * (b * g * x + y) = x := by
  ring

/-- The first count after a block: `x' = (1 + 2bg²) x + 2g y`. -/
lemma twoTwistBlock_mulVec_zero (b g : ℝ) (v : Fin 2 → ℝ) :
    (twoTwistBlock b g *ᵥ v) 0 = (1 + 2 * b * g ^ 2) * v 0 + 2 * g * v 1 := by
  simp [twoTwistBlock, mulVec, dotProduct, Fin.sum_univ_two]

/-- The second count after a block: `y' = bg x + y`. -/
lemma twoTwistBlock_mulVec_one (b g : ℝ) (v : Fin 2 → ℝ) :
    (twoTwistBlock b g *ᵥ v) 1 = b * g * v 0 + v 1 := by
  simp [twoTwistBlock, mulVec, dotProduct, Fin.sum_univ_two]

/-- **The block identity**: `(M_b v)₀ - 2g (M_b v)₁ = v₀`, for all `b`, `g`. -/
theorem twoTwistBlock_mulVec_zero_sub (b g : ℝ) (v : Fin 2 → ℝ) :
    (twoTwistBlock b g *ᵥ v) 0 - 2 * g * (twoTwistBlock b g *ᵥ v) 1 = v 0 := by
  rw [twoTwistBlock_mulVec_zero, twoTwistBlock_mulVec_one, twoTwistBlock_identity]

variable {b g : ℝ} {v : Fin 2 → ℝ}

/-- After one block, `x' ≥ 2g y'` as soon as `x ≥ 0`. -/
theorem two_mul_le_twoTwistBlock_mulVec (hv : 0 ≤ v 0) :
    2 * g * (twoTwistBlock b g *ᵥ v) 1 ≤ (twoTwistBlock b g *ᵥ v) 0 := by
  linarith [twoTwistBlock_mulVec_zero_sub b g v]

/-- For `b, g ≥ 0` a block does not decrease the counts of a nonnegative vector. -/
lemma le_twoTwistBlock_mulVec (hb : 0 ≤ b) (hg : 0 ≤ g) (hv : ∀ i, 0 ≤ v i) (i : Fin 2) :
    v i ≤ (twoTwistBlock b g *ᵥ v) i := by
  have h0 := hv 0
  have h1 := hv 1
  fin_cases i
  · simp only [Fin.zero_eta, twoTwistBlock_mulVec_zero]
    nlinarith [mul_nonneg (mul_nonneg hb (sq_nonneg g)) h0, mul_nonneg hg h1]
  · simp only [Fin.mk_one, twoTwistBlock_mulVec_one]
    nlinarith [mul_nonneg (mul_nonneg hb hg) h0]

variable {ω : ℕ → ℝ}

/-- Along a word of nonnegative exponents, the counts of a nonnegative vector do not decrease. -/
lemma le_cocycle_twoTwistBlock_mulVec (hω : ∀ k, 0 ≤ ω k) (hg : 0 ≤ g) (hv : ∀ i, 0 ≤ v i)
    (n : ℕ) (i : Fin 2) : v i ≤ (cocycle (twoTwistBlock · g) ω n *ᵥ v) i := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [cocycle_mulVec_succ]
    exact (ih i).trans (le_twoTwistBlock_mulVec (hω n) hg (fun j ↦ (hv j).trans (ih j)) i)

/-- **The cusp bound along a block word.** From a nonnegative start, every count vector after
the first block of a word of nonnegative exponents has `x ≥ 2g y`. -/
theorem two_mul_le_cocycle_twoTwistBlock_mulVec (hω : ∀ k, 0 ≤ ω k) (hg : 0 ≤ g)
    (hv : ∀ i, 0 ≤ v i) (n : ℕ) :
    2 * g * (cocycle (twoTwistBlock · g) ω (n + 1) *ᵥ v) 1 ≤
      (cocycle (twoTwistBlock · g) ω (n + 1) *ᵥ v) 0 := by
  rw [cocycle_mulVec_succ]
  exact two_mul_le_twoTwistBlock_mulVec
    ((hv 0).trans (le_cocycle_twoTwistBlock_mulVec hω hg hv n 0))

/-- The arithmetic of the cusp ratio: `(2g + 1)(x - y) - (2g - 1)(x + y) = 2(x - 2g y)`. -/
theorem two_mul_add_one_mul_sub_sub {R : Type*} [CommRing R] (g x y : R) :
    (2 * g + 1) * (x - y) - (2 * g - 1) * (x + y) = 2 * (x - 2 * g * y) := by
  ring

/-- **The cusp ratio.** For `x + y > 0` and `g ≥ 0`,
`(x - y) / (3(x + y)) ≥ (2g - 1) / (3(2g + 1))` if and only if `x ≥ 2g y`. -/
theorem two_mul_sub_one_div_le_iff {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {g x y : 𝕜} (hg : 0 ≤ g) (hxy : 0 < x + y) :
    (2 * g - 1) / (3 * (2 * g + 1)) ≤ (x - y) / (3 * (x + y)) ↔ 2 * g * y ≤ x := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith [two_mul_add_one_mul_sub_sub g x y]

/-- **The cusp ratio along a block word.** From a nonnegative nonzero start, every count vector
`(x, y)` after the first block of a word of nonnegative exponents has
`(x - y) / (3(x + y)) ≥ (2g - 1) / (3(2g + 1))`. -/
theorem two_mul_sub_one_div_le_cocycle_twoTwistBlock (hω : ∀ k, 0 ≤ ω k) (hg : 0 ≤ g)
    (hv : ∀ i, 0 ≤ v i) (hv' : 0 < v 0 + v 1) (n : ℕ) :
    (2 * g - 1) / (3 * (2 * g + 1)) ≤
      ((cocycle (twoTwistBlock · g) ω (n + 1) *ᵥ v) 0 -
        (cocycle (twoTwistBlock · g) ω (n + 1) *ᵥ v) 1) /
      (3 * ((cocycle (twoTwistBlock · g) ω (n + 1) *ᵥ v) 0 +
        (cocycle (twoTwistBlock · g) ω (n + 1) *ᵥ v) 1)) := by
  refine (two_mul_sub_one_div_le_iff hg ?_).2 (two_mul_le_cocycle_twoTwistBlock_mulVec hω hg hv n)
  linarith [le_cocycle_twoTwistBlock_mulVec hω hg hv (n + 1) 0,
    le_cocycle_twoTwistBlock_mulVec hω hg hv (n + 1) 1]

end BlockIdentity

end Matrix

/-! ### The moving-start lemma -/

section MovingStart

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {u : ℕ → 𝕜} {d C : 𝕜}

/-- Iterating `d u_k - C ≤ u_{k+1}`: for `d ≥ 0`,
`dʲ u_k ≤ u_{k+j} + C (1 + d + ⋯ + d^{j-1})`, that is
`u_k ≤ d^{-j} u_{k+j} + C (1 - d^{-j}) / (d - 1)` for `d > 1`. -/
lemma pow_mul_le_add_mul_geom_sum (hd : 0 ≤ d) (h : ∀ k, d * u k - C ≤ u (k + 1)) (k j : ℕ) :
    d ^ j * u k ≤ u (k + j) + C * ∑ i ∈ Finset.range j, d ^ i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', geom_sum_succ, ← add_assoc]
    have h1 := mul_le_mul_of_nonneg_left ih hd
    linarith [h (k + j)]

/-- The moving-start lemma without division: `(d - 1) ∑_{k<m} u_k ≤ u_m + C m`, for any `d`. -/
lemma mul_sum_range_le_of_mul_sub_le (hu : 0 ≤ u 0) (h : ∀ k, d * u k - C ≤ u (k + 1))
    (m : ℕ) : (d - 1) * ∑ k ∈ Finset.range m, u k ≤ u m + C * m := by
  induction m with
  | zero => simpa using hu
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linarith [h m]

/-- **The moving-start lemma.** If `u_0 ≥ 0` and `u_{k+1} ≥ d u_k - C` for every `k`, with
`d > 1`, then `∑_{k<m} u_k ≤ (u_m + C m) / (d - 1)` for every `m`. -/
theorem sum_range_le_of_mul_sub_le (hd : 1 < d) (hu : 0 ≤ u 0)
    (h : ∀ k, d * u k - C ≤ u (k + 1)) (m : ℕ) :
    ∑ k ∈ Finset.range m, u k ≤ (u m + C * m) / (d - 1) := by
  rw [le_div_iff₀ (sub_pos.2 hd), mul_comm]
  exact mul_sum_range_le_of_mul_sub_le hu h m

/-- **The moving-start lemma**, linear form: for `u ≥ 0`,
`∑_{k<m} u_k ≤ C₁ (u_m + m)` with `C₁ = max 1 C / (d - 1)`. -/
theorem sum_range_le_max_one_div_mul (hd : 1 < d) (hu : ∀ k, 0 ≤ u k)
    (h : ∀ k, d * u k - C ≤ u (k + 1)) (m : ℕ) :
    ∑ k ∈ Finset.range m, u k ≤ max 1 C / (d - 1) * (u m + m) := by
  refine (sum_range_le_of_mul_sub_le hd (hu 0) h m).trans ?_
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (sub_nonneg.2 hd.le)
  rw [mul_add]
  exact add_le_add (le_mul_of_one_le_left (hu m) (le_max_left _ _))
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))

end MovingStart

/-! ### Limits of ratios with small errors -/

/-- **Small errors do not move a limit of ratios.** If `a / p → L` and the errors `x - a`,
`y - p` are `o(p)`, then `x / y → L`. -/
theorem Filter.Tendsto.div_of_isLittleO {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α}
    {a p x y : α → 𝕜} {L : 𝕜} (h : Tendsto (fun n ↦ a n / p n) l (𝓝 L))
    (hx : (fun n ↦ x n - a n) =o[l] p) (hy : (fun n ↦ y n - p n) =o[l] p) :
    Tendsto (fun n ↦ x n / y n) l (𝓝 L) := by
  have key := (h.add hx.tendsto_div_nhds_zero).div
    (tendsto_const_nhds.add hy.tendsto_div_nhds_zero) (by simp : (1 : 𝕜) + 0 ≠ 0)
  rw [add_zero, add_zero, div_one] at key
  refine key.congr' ?_
  filter_upwards [hy.def (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  simp only [Pi.div_apply]
  rcases eq_or_ne (p n) 0 with hp | hp
  · have hy0 : y n = 0 := by
      rwa [hp, norm_zero, mul_zero, norm_le_zero_iff, sub_zero] at hn
    simp [hp, hy0]
  · rw [← add_div, add_sub_cancel, ← div_self hp, ← add_div, add_sub_cancel,
      div_div_div_cancel_right₀ hp]

/-- **Bounded errors do not move a limit of ratios** whose denominator tends to infinity: if
`a / p → L`, `p → ∞` and `|x - a|`, `|y - p|` are eventually bounded, then `x / y → L`. -/
theorem Filter.Tendsto.div_of_abs_sub_le {α : Type*} {l : Filter α} {a p x y : α → ℝ}
    {L Dx Dy : ℝ} (h : Tendsto (fun n ↦ a n / p n) l (𝓝 L)) (hp : Tendsto p l atTop)
    (hx : ∀ᶠ n in l, |x n - a n| ≤ Dx) (hy : ∀ᶠ n in l, |y n - p n| ≤ Dy) :
    Tendsto (fun n ↦ x n / y n) l (𝓝 L) := by
  have h1 : (fun _ ↦ (1 : ℝ)) =o[l] p :=
    (Asymptotics.isLittleO_one_left_iff ℝ).2 (tendsto_abs_atTop_atTop.comp hp)
  refine h.div_of_isLittleO ((Asymptotics.IsBigO.of_bound Dx ?_).trans_isLittleO h1)
    ((Asymptotics.IsBigO.of_bound Dy ?_).trans_isLittleO h1)
  · filter_upwards [hx] with n hn
    simpa using hn
  · filter_upwards [hy] with n hn
    simpa using hn

namespace Matrix

/-! ### Projective convergence of positive cocycles -/

section Projective

variable {β : Type*} {M : β → Matrix (Fin 2) (Fin 2) ℝ}

/-- A matrix with positive entries maps positive vectors to positive vectors. -/
lemma mulVec_pos {ι κ R : Type*} [Fintype κ] [Nonempty κ] [Semiring R] [PartialOrder R]
    [IsStrictOrderedRing R] {A : Matrix ι κ R} (hA : ∀ i j, 0 < A i j) {v : κ → R}
    (hv : ∀ j, 0 < v j) (i : ι) : 0 < (A *ᵥ v) i :=
  Finset.sum_pos (fun j _ ↦ mul_pos (hA i j) (hv j)) Finset.univ_nonempty

/-- A positive vector has positive dot product with a nonnegative nonzero vector. -/
lemma dotProduct_pos_of_nonneg {ι R : Type*} [Fintype ι] [Semiring R] [PartialOrder R]
    [IsStrictOrderedRing R] {u t : ι → R} (hu : ∀ i, 0 < u i) (ht : ∀ i, 0 ≤ t i)
    (ht' : t ≠ 0) : 0 < u ⬝ᵥ t := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 ht'
  exact Finset.sum_pos' (fun i _ ↦ mul_nonneg (hu i).le (ht i))
    ⟨j, Finset.mem_univ j, mul_pos (hu j) (lt_of_le_of_ne (ht j) (Ne.symm hj))⟩

/-- The transposes of positive matrices are positive. -/
lemma transpose_pos (hM : ∀ b i j, 0 < M b i j) (b : β) (i j : Fin 2) : 0 < (M b)ᵀ i j :=
  hM b j i

/-- The transposed cocycle of positive matrices maps positive vectors to positive vectors. -/
lemma transpose_cocycle_mulVec_pos (hM : ∀ b i j, 0 < M b i j) (ω : ℕ → β) {c : Fin 2 → ℝ}
    (hc : ∀ i, 0 < c i) (n : ℕ) (i : Fin 2) : 0 < ((cocycle M ω n)ᵀ *ᵥ c) i := by
  induction n generalizing c with
  | zero => simpa using hc i
  | succ n ih =>
    rw [transpose_cocycle_succ, ← mulVec_mulVec]
    exact ih (mulVec_pos (transpose_pos hM (ω n)) hc)

variable (M) in
/-- The ratio map of `(M b)ᵀ` in logarithmic coordinates, `u ↦ log R_b(eᵘ)`. -/
noncomputable def logRatioLetter (b : β) (u : ℝ) : ℝ :=
  log ((M b)ᵀ.ratioMap (exp u))

/-- For finitely many positive matrices, the logarithmic ratio maps are uniform contractions:
they are Lipschitz with the largest Birkhoff coefficient, which is less than one. -/
lemma exists_lipschitzWith_logRatioLetter [Finite β] (hM : ∀ b i j, 0 < M b i j) :
    ∃ K : ℝ≥0, K < 1 ∧ ∀ b, LipschitzWith K (logRatioLetter M b) := by
  obtain ⟨K, hK0, hK1, hKb⟩ : ∃ K : ℝ, 0 ≤ K ∧ K < 1 ∧ ∀ b, (M b).birkhoffCoeff ≤ K := by
    rcases isEmpty_or_nonempty β with hβ | hβ
    · exact ⟨0, le_rfl, one_pos, fun b ↦ (IsEmpty.false b).elim⟩
    · obtain ⟨b₀, hb₀⟩ := Finite.exists_max fun b ↦ (M b).birkhoffCoeff
      exact ⟨_, birkhoffCoeff_nonneg, birkhoffCoeff_lt_one (hM b₀), hb₀⟩
  refine ⟨K.toNNReal, by rwa [Real.toNNReal_lt_one], fun b ↦
    LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
  have h := abs_log_ratioMap_sub_le (transpose_pos hM b) (exp_pos u) (exp_pos v)
  rw [Real.log_exp, Real.log_exp, birkhoffCoeff_transpose] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hKb b) (abs_nonneg _))

/-- **The ratio of the transposed cocycle** is the composite of the ratio maps of the transposed
letters: `ratio (P_n c) = R_{ω 0} ∘ ⋯ ∘ R_{ω(n-1)} (ratio c)`, in logarithmic coordinates. -/
theorem ratio_transpose_cocycle_mulVec (hM : ∀ b i j, 0 < M b i j) (ω : ℕ → β)
    {c : Fin 2 → ℝ} (hc : ∀ i, 0 < c i) (n : ℕ) :
    ((cocycle M ω n)ᵀ *ᵥ c) 0 / ((cocycle M ω n)ᵀ *ᵥ c) 1 =
      exp (IFS.comp (logRatioLetter M) n ω (log (c 0 / c 1))) := by
  induction n generalizing c with
  | zero => simp [Real.exp_log (div_pos (hc 0) (hc 1))]
  | succ n ih =>
    have hc' := mulVec_pos (transpose_pos hM (ω n)) hc
    have hlog : log (((M (ω n))ᵀ *ᵥ c) 0 / ((M (ω n))ᵀ *ᵥ c) 1) =
        logRatioLetter M (ω n) (log (c 0 / c 1)) := by
      rw [logRatioLetter, Real.exp_log (div_pos (hc 0) (hc 1)), mulVec_fin_two_ratio (hc 1)]
    rw [transpose_cocycle_succ, ← mulVec_mulVec, ih hc', hlog, IFS.comp_succ']

variable (M) in
/-- The **limit ratio** `x(ω)` of the cocycle along `ω`: the exponential of the coding map of the
logarithmic ratio maps of the transposed letters. -/
noncomputable def cocycleRatio (ω : ℕ → β) : ℝ :=
  exp (IFS.codingMap (logRatioLetter M) ω)

variable (M) in
/-- The **limit ray** `u(ω) = (x(ω), 1)` of the cocycle along `ω`. -/
noncomputable def cocycleRay (ω : ℕ → β) : Fin 2 → ℝ := ![cocycleRatio M ω, 1]

variable {ω : ℕ → β}

/-- The limit ratio is positive. -/
lemma cocycleRatio_pos : 0 < cocycleRatio M ω := exp_pos _

/-- The first entry of the limit ray is the limit ratio. -/
@[simp]
lemma cocycleRay_zero : cocycleRay M ω 0 = cocycleRatio M ω := rfl

/-- The second entry of the limit ray is one. -/
@[simp]
lemma cocycleRay_one : cocycleRay M ω 1 = 1 := rfl

variable (M ω) in
/-- The limit ray is positive. -/
lemma cocycleRay_pos (i : Fin 2) : 0 < cocycleRay M ω i := by
  fin_cases i
  · exact cocycleRatio_pos
  · exact one_pos

/-- `u(ω) ⬝ t = x(ω) t₀ + t₁`. -/
lemma cocycleRay_dotProduct (t : Fin 2 → ℝ) :
    cocycleRay M ω ⬝ᵥ t = cocycleRatio M ω * t 0 + t 1 := by
  simp [dotProduct, Fin.sum_univ_two]

variable {c : Fin 2 → ℝ}

/-- **Projective convergence of a positive cocycle.** For finitely many matrices with positive
entries, an infinite word `ω` and a positive vector `c`, the ratio of `P_n c`, where
`P_n = (M (ω 0))ᵀ * ⋯ * (M (ω (n-1)))ᵀ`, converges to the limit ratio `x(ω)`, which does not
depend on `c`. -/
theorem tendsto_ratio_transpose_cocycle_mulVec [Finite β] (hM : ∀ b i j, 0 < M b i j)
    (ω : ℕ → β) (hc : ∀ i, 0 < c i) :
    Tendsto (fun n ↦ ((cocycle M ω n)ᵀ *ᵥ c) 0 / ((cocycle M ω n)ᵀ *ᵥ c) 1) atTop
      (𝓝 (cocycleRatio M ω)) := by
  obtain ⟨K, hK, hf⟩ := exists_lipschitzWith_logRatioLetter hM
  simp_rw [ratio_transpose_cocycle_mulVec hM ω hc]
  exact (continuous_exp.tendsto _).comp (IFS.tendsto_comp_codingMap hf hK ω _)

/-- **The rays converge**: normalized by its second entry, `P_n c` converges to the limit ray
`u(ω) = (x(ω), 1)`. -/
theorem tendsto_smul_transpose_cocycle_mulVec [Finite β] (hM : ∀ b i j, 0 < M b i j)
    (ω : ℕ → β) (hc : ∀ i, 0 < c i) :
    Tendsto (fun n ↦ (((cocycle M ω n)ᵀ *ᵥ c) 1)⁻¹ • ((cocycle M ω n)ᵀ *ᵥ c)) atTop
      (𝓝 (cocycleRay M ω)) := by
  have hpos := transpose_cocycle_mulVec_pos hM ω hc
  refine tendsto_pi_nhds.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simpa [inv_mul_eq_div] using tendsto_ratio_transpose_cocycle_mulVec hM ω hc
  · refine tendsto_const_nhds.congr fun n ↦ ?_
    simp [inv_mul_cancel₀ (hpos n 1).ne']

/-- **Convergence in Hilbert's projective metric**: `d_H(P_n c, u(ω)) → 0`. -/
theorem tendsto_hilbertEDist_transpose_cocycle_mulVec [Finite β] (hM : ∀ b i j, 0 < M b i j)
    (ω : ℕ → β) (hc : ∀ i, 0 < c i) :
    Tendsto (fun n ↦ hilbertEDist univ ((cocycle M ω n)ᵀ *ᵥ c) (cocycleRay M ω)) atTop
      (𝓝 0) := by
  have hpos := transpose_cocycle_mulVec_pos hM ω hc
  have h := (((tendsto_ratio_transpose_cocycle_mulVec hM ω hc).log
    cocycleRatio_pos.ne').sub_const (log (cocycleRatio M ω))).abs
  rw [sub_self, abs_zero] at h
  refine (ENNReal.ofReal_zero ▸ ENNReal.tendsto_ofReal h).congr fun n ↦ ?_
  rw [hilbertEDist_univ_fin_two (hpos n) (cocycleRay_pos M ω), cocycleRay_zero, cocycleRay_one,
    div_one]

/-- **The limiting profile of a positive cocycle.** For an infinite word `ω`, a positive `c`, any
`t_E` and a nonnegative nonzero `t_P`,
`(c ⬝ Q_n t_E) / (c ⬝ Q_n t_P) → (u(ω) ⬝ t_E) / (u(ω) ⬝ t_P)`, with `Q_n` the cocycle. -/
theorem tendsto_dotProduct_cocycle_mulVec_div [Finite β] (hM : ∀ b i j, 0 < M b i j)
    (ω : ℕ → β) (hc : ∀ i, 0 < c i) (tE : Fin 2 → ℝ) {tP : Fin 2 → ℝ} (htP : ∀ i, 0 ≤ tP i)
    (htP' : tP ≠ 0) :
    Tendsto (fun n ↦ c ⬝ᵥ (cocycle M ω n *ᵥ tE) / c ⬝ᵥ (cocycle M ω n *ᵥ tP)) atTop
      (𝓝 (cocycleRay M ω ⬝ᵥ tE / cocycleRay M ω ⬝ᵥ tP)) := by
  have hpos := transpose_cocycle_mulVec_pos hM ω hc
  have hr := tendsto_ratio_transpose_cocycle_mulVec hM ω hc
  have key : ∀ n t, c ⬝ᵥ (cocycle M ω n *ᵥ t) = ((cocycle M ω n)ᵀ *ᵥ c) 1 *
      (((cocycle M ω n)ᵀ *ᵥ c) 0 / ((cocycle M ω n)ᵀ *ᵥ c) 1 * t 0 + t 1) := by
    intro n t
    have h1 := (hpos n 1).ne'
    rw [dotProduct_mulVec, ← mulVec_transpose]
    simp only [dotProduct, Fin.sum_univ_two]
    field_simp
  have hden : cocycleRay M ω ⬝ᵥ tP ≠ 0 :=
    (dotProduct_pos_of_nonneg (cocycleRay_pos M ω) htP htP').ne'
  simp_rw [key, mul_div_mul_left _ _ (hpos _ 1).ne']
  simp only [cocycleRay_dotProduct] at hden ⊢
  exact ((hr.mul_const _).add_const _).div ((hr.mul_const _).add_const _) hden

/-- **The limiting profile with bounded errors.** If the real numbers `m_E n`, `m_P n` stay within
bounded distance of `c ⬝ Q_n t_E` and `c ⬝ Q_n t_P`, and `c ⬝ Q_n t_P → ∞`, then
`m_E n / m_P n → (u(ω) ⬝ t_E) / (u(ω) ⬝ t_P)`, a limit that does not depend on `c`. -/
theorem tendsto_div_of_abs_sub_le_cocycle [Finite β] (hM : ∀ b i j, 0 < M b i j)
    (ω : ℕ → β) (hc : ∀ i, 0 < c i) {tE tP : Fin 2 → ℝ} (htP : ∀ i, 0 ≤ tP i)
    (htP' : tP ≠ 0) {mE mP : ℕ → ℝ} {DE DP : ℝ}
    (hE : ∀ᶠ n in atTop, |mE n - c ⬝ᵥ (cocycle M ω n *ᵥ tE)| ≤ DE)
    (hP : ∀ᶠ n in atTop, |mP n - c ⬝ᵥ (cocycle M ω n *ᵥ tP)| ≤ DP)
    (hdiv : Tendsto (fun n ↦ c ⬝ᵥ (cocycle M ω n *ᵥ tP)) atTop atTop) :
    Tendsto (fun n ↦ mE n / mP n) atTop
      (𝓝 (cocycleRay M ω ⬝ᵥ tE / cocycleRay M ω ⬝ᵥ tP)) :=
  (tendsto_dotProduct_cocycle_mulVec_div hM ω hc tE htP htP').div_of_abs_sub_le hdiv hE hP

/-- **The limiting profile over a family**: for count vectors `t E` indexed by any type and real
numbers `m n E` within bounded distance of `c ⬝ Q_n t E`, normalized by an index `P` with `t P`
nonnegative and nonzero and `c ⬝ Q_n t P → ∞`, the normalized profiles `E ↦ m n E / m n P`
converge pointwise to `E ↦ (u(ω) ⬝ t E) / (u(ω) ⬝ t P)`. -/
theorem tendsto_pi_div_of_abs_sub_le_cocycle [Finite β] {Obj : Type*}
    (hM : ∀ b i j, 0 < M b i j) (ω : ℕ → β) (hc : ∀ i, 0 < c i) (t : Obj → Fin 2 → ℝ)
    {P : Obj} (htP : ∀ i, 0 ≤ t P i) (htP' : t P ≠ 0) {m : ℕ → Obj → ℝ} {D : Obj → ℝ}
    (hm : ∀ E, ∀ᶠ n in atTop, |m n E - c ⬝ᵥ (cocycle M ω n *ᵥ t E)| ≤ D E)
    (hdiv : Tendsto (fun n ↦ c ⬝ᵥ (cocycle M ω n *ᵥ t P)) atTop atTop) :
    Tendsto (fun n E ↦ m n E / m n P) atTop
      (𝓝 fun E ↦ cocycleRay M ω ⬝ᵥ t E / cocycleRay M ω ⬝ᵥ t P) :=
  tendsto_pi_nhds.2 fun E ↦
    tendsto_div_of_abs_sub_le_cocycle hM ω hc htP htP' (hm E) (hm P) hdiv

/-- **Periodic words: the Perron eigenvector.** If `ω` has period `p`, the limit ray `u(ω)` is an
eigenvector with positive eigenvalue of the product `P_p = Q_pᵀ` over a period. -/
theorem exists_transpose_cocycle_mulVec_cocycleRay_eq_smul [Finite β]
    (hM : ∀ b i j, 0 < M b i j) {p : ℕ} (hω : ∀ i, ω (i + p) = ω i) :
    ∃ l : ℝ, 0 < l ∧ (cocycle M ω p)ᵀ *ᵥ cocycleRay M ω = l • cocycleRay M ω := by
  obtain ⟨K, hK, hf⟩ := exists_lipschitzWith_logRatioLetter hM
  have hpos := transpose_cocycle_mulVec_pos hM ω (cocycleRay_pos M ω) p
  have hratio := ratio_transpose_cocycle_mulVec hM ω (cocycleRay_pos M ω) p
  rw [cocycleRay_zero, cocycleRay_one, div_one, cocycleRatio, Real.log_exp,
    IFS.comp_codingMap_of_periodic hf hK hω, ← cocycleRatio,
    div_eq_iff (hpos 1).ne'] at hratio
  refine ⟨_, hpos 1, ?_⟩
  ext i
  fin_cases i
  · simp [hratio, mul_comm]
  · simp

/-- **Uniqueness of the Perron eigenvector.** If `ω` has period `p ≥ 1`, every positive eigenvector
of `P_p = Q_pᵀ` is a multiple of the limit ray `u(ω)`. -/
theorem eq_smul_cocycleRay_of_periodic [Finite β] (hM : ∀ b i j, 0 < M b i j) {p : ℕ}
    (hp : 0 < p) (hω : ∀ i, ω (i + p) = ω i) {v : Fin 2 → ℝ} (hv : ∀ i, 0 < v i) {l : ℝ}
    (hl : (cocycle M ω p)ᵀ *ᵥ v = l • v) : v = v 1 • cocycleRay M ω := by
  obtain ⟨K, hK, hf⟩ := exists_lipschitzWith_logRatioLetter hM
  have hpos := transpose_cocycle_mulVec_pos hM ω hv p 1
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [hl, zero_smul] at hpos
    exact lt_irrefl _ hpos
  have hratio := ratio_transpose_cocycle_mulVec hM ω hv p
  rw [hl, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_div_mul_left _ _ hl0] at hratio
  have hfix := congrArg log hratio
  rw [Real.log_exp] at hfix
  have hr : v 0 / v 1 = cocycleRatio M ω := by
    rw [cocycleRatio, ← IFS.eq_codingMap_of_periodic hf hK hp hω hfix.symm,
      Real.exp_log (div_pos (hv 0) (hv 1))]
  rw [div_eq_iff (hv 1).ne'] at hr
  ext i
  fin_cases i
  · simp [hr, mul_comm]
  · simp

end Projective

/-! ### The two-block alphabet -/

section TwoBlock

open IFS

/-- The two blocks `b ∈ {2, 4}`, `M_2` for `false` and `M_4` for `true`. -/
def twoBlockAlphabet (g : ℝ) (s : Bool) : Matrix (Fin 2) (Fin 2) ℝ :=
  twoTwistBlock (blockExponent s) g

variable {g : ℝ}

/-- For `g > 0` the two blocks have positive entries. -/
lemma twoBlockAlphabet_pos (hg : 0 < g) (s : Bool) (i j : Fin 2) :
    0 < twoBlockAlphabet g s i j :=
  twoTwistBlock_pos (blockExponent_pos s) hg i j

/-- The cocycle of a word in the two blocks is the cocycle of its sequence of exponents. -/
lemma cocycle_twoBlockAlphabet (ω : ℕ → Bool) (n : ℕ) :
    cocycle (twoBlockAlphabet g) ω n =
      cocycle (twoTwistBlock · g) (fun i ↦ blockExponent (ω i)) n :=
  cocycle_comp (twoTwistBlock · g) blockExponent ω n

/-- The logarithmic ratio maps of the two blocks are the letters `IFS.twoBlockLetter`. -/
lemma logRatioLetter_twoBlockAlphabet : logRatioLetter (twoBlockAlphabet g) = twoBlockLetter g :=
  rfl

/-- The limit ratio of a word in the two blocks is its centre ratio
`x(ω) = [b₀g; 2g, b₁g, 2g, …]`. -/
lemma cocycleRatio_twoBlockAlphabet (ω : ℕ → Bool) :
    cocycleRatio (twoBlockAlphabet g) ω = centreRatio g ω :=
  rfl

/-- **Projective convergence for the two blocks.** For `g > 0`, every infinite word `ω` in the
blocks `b ∈ {2, 4}` and every positive `c`, the ratio of `P_n c` converges to the centre ratio
`x(ω)`. -/
theorem tendsto_ratio_transpose_cocycle_twoBlockAlphabet (hg : 0 < g) (ω : ℕ → Bool)
    {c : Fin 2 → ℝ} (hc : ∀ i, 0 < c i) :
    Tendsto (fun n ↦ ((cocycle (twoBlockAlphabet g) ω n)ᵀ *ᵥ c) 0 /
      ((cocycle (twoBlockAlphabet g) ω n)ᵀ *ᵥ c) 1) atTop (𝓝 (centreRatio g ω)) :=
  tendsto_ratio_transpose_cocycle_mulVec (twoBlockAlphabet_pos hg) ω hc

/-- **The counts grow.** For `g > 0` and exponents at least `b₀ > 0`, the first count of a
nonnegative nonzero vector grows at least geometrically along the word, so
`c ⬝ Q_n t → ∞` for every positive `c`. -/
theorem tendsto_dotProduct_cocycle_twoTwistBlock_atTop {b₀ : ℝ} (hb₀ : 0 < b₀) (hg : 0 < g)
    {ω : ℕ → ℝ} (hω : ∀ k, b₀ ≤ ω k) {c t : Fin 2 → ℝ} (hc : ∀ i, 0 < c i)
    (ht : ∀ i, 0 ≤ t i) (ht' : t ≠ 0) :
    Tendsto (fun n ↦ c ⬝ᵥ (cocycle (twoTwistBlock · g) ω n *ᵥ t)) atTop atTop := by
  have hω0 : ∀ k, 0 ≤ ω k := fun k ↦ hb₀.le.trans (hω k)
  set v := fun n ↦ cocycle (twoTwistBlock · g) ω n *ᵥ t with hv
  have hnn : ∀ n i, 0 ≤ v n i := fun n i ↦
    (ht i).trans (le_cocycle_twoTwistBlock_mulVec hω0 hg.le ht n i)
  set d := 1 + 2 * b₀ * g ^ 2 with hd
  have hd1 : 1 < d := by
    have := mul_pos (mul_pos two_pos hb₀) (pow_pos hg 2)
    linarith
  have hstep : ∀ n, d * v n 0 ≤ v (n + 1) 0 := by
    intro n
    simp only [hv, cocycle_mulVec_succ, twoTwistBlock_mulVec_zero]
    have h0 := hnn n 0
    have h1 := hnn n 1
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hω n) zero_le_two) (sq_nonneg g)) h0
    nlinarith [mul_nonneg hg.le h1]
  have hv1 : 0 < v 1 0 := by
    simp only [hv, cocycle_mulVec_succ, cocycle_zero, one_mulVec, twoTwistBlock_mulVec_zero]
    have hb : 0 < 1 + 2 * ω 0 * g ^ 2 := by have := hω0 0; positivity
    rcases (ht 0).lt_or_eq with h | h
    · have := mul_pos hb h
      nlinarith [mul_nonneg hg.le (ht 1)]
    · have h1 : t 1 ≠ 0 := fun h1 ↦ ht' (by ext i; fin_cases i <;> simp [← h, h1])
      have := mul_pos (mul_pos two_pos hg) (lt_of_le_of_ne (ht 1) (Ne.symm h1))
      rw [← h, mul_zero, zero_add]
      exact this
  have hpow : ∀ n, d ^ n * v 1 0 ≤ v (n + 1) 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih (by linarith)).trans (hstep _)
  have hdot : ∀ n, c 0 * v n 0 ≤ c ⬝ᵥ v n := by
    intro n
    simp only [dotProduct, Fin.sum_univ_two]
    nlinarith [mul_nonneg (hc 1).le (hnn n 1)]
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_atTop_mono (fun n ↦ (mul_le_mul_of_nonneg_left (hpow n) (hc 0).le).trans
    (hdot (n + 1))) ?_
  exact ((tendsto_pow_atTop_atTop_of_one_lt hd1).atTop_mul_const hv1).const_mul_atTop (hc 0)

/-- **The count core of the limiting profiles of two spherical twists.** For `g > 0`, every
infinite word `ω` in the blocks `b ∈ {2, 4}`, every positive `c` and real numbers `m_E n`, `m_P n`
within bounded distance of `c ⬝ Q_n t_E` and `c ⬝ Q_n t_P` (`t_P` nonnegative and nonzero),
`m_E n / m_P n → (x(ω) t_{E,0} + t_{E,1}) / (x(ω) t_{P,0} + t_{P,1})`, with `x(ω)` the centre
ratio; the limit does not depend on `c`. -/
theorem tendsto_div_twoBlockAlphabet (hg : 0 < g) (ω : ℕ → Bool) {c : Fin 2 → ℝ}
    (hc : ∀ i, 0 < c i) {tE tP : Fin 2 → ℝ} (htP : ∀ i, 0 ≤ tP i) (htP' : tP ≠ 0)
    {mE mP : ℕ → ℝ} {DE DP : ℝ}
    (hE : ∀ᶠ n in atTop, |mE n - c ⬝ᵥ (cocycle (twoBlockAlphabet g) ω n *ᵥ tE)| ≤ DE)
    (hP : ∀ᶠ n in atTop, |mP n - c ⬝ᵥ (cocycle (twoBlockAlphabet g) ω n *ᵥ tP)| ≤ DP) :
    Tendsto (fun n ↦ mE n / mP n) atTop
      (𝓝 ((centreRatio g ω * tE 0 + tE 1) / (centreRatio g ω * tP 0 + tP 1))) := by
  have hdiv : Tendsto (fun n ↦ c ⬝ᵥ (cocycle (twoBlockAlphabet g) ω n *ᵥ tP)) atTop atTop := by
    have h := tendsto_dotProduct_cocycle_twoTwistBlock_atTop two_pos hg
      (ω := fun i ↦ blockExponent (ω i)) (fun k ↦ ?_) hc htP htP'
    · simpa only [cocycle_twoBlockAlphabet] using h
    · cases ω k <;> norm_num [blockExponent]
  have h := tendsto_div_of_abs_sub_le_cocycle (twoBlockAlphabet_pos hg) ω hc htP htP' hE hP hdiv
  rwa [cocycleRay_dotProduct, cocycleRay_dotProduct, cocycleRatio_twoBlockAlphabet] at h

end TwoBlock

end Matrix
