/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.HarderNarasimhan
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The wall group that carries the point

Let a spherical object `S` and an isotropic object `U` (`v(U)² = 0`) become stable of one phase on
a wall, with `g = ⟨v(S), v(U)⟩ = ext¹(S, U) = ext¹(U, S)`. By formality of the `Ext`-algebra of
`S` and `U` (Davison, arXiv:2106.07692, Proposition 7.8), the iterated extensions of `S` and `U`
are the nilpotent modules over the preprojective algebra of their `Ext`-quiver: vertex `0` for
`S`, vertex `1` for `U` with two loops (a basis of `Ext¹(U, U)`), and `g` arrows each way between
them. An iterated extension `M` in which `U` occurs once and `S` occurs `p` times has dimension
vector `(p, 1)`; the loops act nilpotently on the line at vertex `1`, hence by zero, and `M` is a
nilpotent representation `M : DoubledRep k ι V k` with the preprojective relations, `|ι| = g`,
`dim V = p`. The arrows `A_i : V → k` are the classes in `Ext¹(S, U)` and `B_i : k → V` those in
`Ext¹(U, S)`.

The model reads `e(M) = dim Ext¹(M, M)` through Riemann–Roch, `e(M) = 2 dim End M + v(M)²` with
`v(M)² = 2p(g - p)` (`AlgebraicGeometry.K3.PicardRankOne.square_roots_plus_isotropic`). The lemma
on the wall group that carries the point assumes `e(M) = 2`, that is
`dim End M + p(g - p) = 1`.

## Main results

* `IsNilpotent.A_comp_B_eq_zero`: in a nilpotent representation with a line at vertex `1`, every
  `A_j B_i` vanishes;
* `evalA`, `sumB`: the maps `V → k^ι`, `v ↦ (A_i v)_i`, and `k^ι → V`, `t ↦ ∑ tᵢ B_i 1`; the
  preprojective relation at vertex `0` is `sumB ∘ evalA = 0`, so the ranks satisfy
  `rk A + rk B ≤ g` (the orthogonality of the two spaces of classes for the Serre pairing), and
  nilpotence gives `evalA ∘ sumB = 0`, so `rk A + rk B ≤ p`;
* `endOf_surjective'`, `finrank_End_eq`: every endomorphism is a scalar plus a map
  `V/⟨B_i 1⟩ → ⋂ ker A_i`, so `dim End M = 1 + (p - rk B)(p - rk A)` exactly, for every
  representation with a line at vertex `1` and no relation at all; `finrank_End_ge` is a
  corollary;
* `oneCopy_identity`: **the one-copy identity** `dim End M + p(g - p) = 1 + ab + p(g - a - b)`
  with `a = rk A`, `b = rk B`, again with no relation; `oneCopy`: with the preprojective relation,
  `dim End M + p(g - p) = c` splits as `ab + p(g - a - b) = c - 1` with both terms nonnegative;
* `oneCopy_one` (`c = 1`, `U` isotropic): `ab = 0` and `a + b = g`, from the preprojective
  relation alone; `twoExtensions_rank'`, `twoExtensions'`: the rank dichotomy and the
  classification of the classes without nilpotence, which enters only for `p ≥ g`;
* `oneCopy_two` (`c = 2`, `U` spherical, `p ≥ 2`): `a = b = 1` and `g = 2`, with no nilpotence;
  `oneCopy_two_rankOne`: then `A_i = α_i φ`, `B_i 1 = β_i w` with `∑ α_i β_i = 0` and `φ(w) = 0`;
  `oneCopy_of_rankOne`: conversely such data give `e(M) = 2` at `g = 2`;
  `oneCopy_two_range_evalA`: the classes `A_i` span a line `kα`, an invariant of `M`;
* `oneCopy_riemannRoch`: `e(M) - e(U) = 2(ab + p(g - a - b))` from Riemann–Roch for `U` and `M`,
  a ring identity in free integers (see its docstring for how it differs from the HN defect);
* `twoExtensions_rank`, `twoExtensions`: **the lemma on the wall group that carries the
  point.** If `dim End M + p(g - p) = 1` and `p > 0`, then `p ≥ g` and either every `B_i` vanishes
  and the `A_i` are linearly independent, so that `M = S^{p-g} ⊕ T_S U` (`T_S U` the universal
  extension `0 → U → T_S U → S^g → 0`), or every `A_i` vanishes and the `B_i 1` are linearly
  independent, so that `M = S^{p-g} ⊕ T_S⁻¹ U` (`0 → S^g → T_S⁻¹ U → U → 0`);
* `hnUHigher`, `hnSHigher`: for every wall object in which `U` occurs once, the HN filtration on
  the side where `U` has the higher phase (`wallSlope`) is `0 ⊂ (⟨B_i 1⟩, k) ⊂ M`, the first
  factor stable (`isStable_bot_subSpan`) and the second `S^{p - rk B}`; on the side where `S` is
  higher (`wallSlope.neg`) it is `0 ⊂ (⋂ ker A_i, 0) ⊂ M`, the first factor `S^{p - rk A}` and the
  second stable (`isStable_subKer_top`);
* `twoExtensions_table`: the table of the lemma. For `S^k ⊕ T_S U` the HN quotients are `U, S^p`
  where `U` is higher and `S^k, T_S U` where `S` is higher; for `S^k ⊕ T_S⁻¹ U` they are
  `T_S⁻¹ U, S^k` and `S^p, U`. Zero terms are omitted when `k = p - g = 0`.

## One copy of a spherical simple

When `U` is spherical (`v(U)² = -2`), Riemann–Roch reads `e(M) = 2` as
`dim End M + p(g - p) = 2`, the case `c = 2` of `oneCopy`. The same model then describes a wall
with two spherical simples `S`, `U` of one phase and `dim Ext¹(U, S) = 2`, and the wall objects in
which `U` occurs once. For `p ≥ 2` the semirigid ones have `g = 2` and classes of rank one, a line
`kα` of classes `A_i` and the orthogonal line of classes `B_i` (`oneCopy_two_rankOne`); conversely
every such rank-one datum is semirigid (`oneCopy_of_rankOne`). Not formalized here: that such an
`M` is `M_α ⊕ S^{p-2}` with `M_α` the length-three object of the line, and that its isomorphism
class is determined by the line (the transitivity of `GL(V)` on pairs `(φ, w)` with `φ(w) = 0`);
and the absence of semirigid wall objects with multiplicities `(2, 2)`.

## Compared with the article's proof

The article splits off the summands `S` and filters the rest as `S^a, U, S^b`; here the ranks
`rk A` and `rk B` of the two families of classes play the roles of `b` and `a`, and
`dim End M ≥ 1 + (p - rk A)(p - rk B)` replaces `dim End N ≥ 1 + ab`. The orthogonality of the
two spaces of classes for the Serre pairing is the relation `sumB ∘ evalA = 0`.
-/

namespace Quiver.Kronecker.DoubledRep

open Module Order

variable {k ι V : Type*} [Field k] [AddCommGroup V] [Module k V] (M : DoubledRep k ι V k)

lemma B_apply (i : ι) (t : k) : M.B i t = t • M.B i 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

/-- In a nilpotent representation whose vertex-one space is a line, every path `A_j B_i` of
length two from vertex one vanishes: it is a scalar whose powers are paths. -/
theorem IsNilpotent.A_comp_B_eq_zero {M : DoubledRep k ι V k} (hM : M.IsNilpotent) (i j : ι) :
    M.A j ∘ₗ M.B i = 0 := by
  obtain ⟨n, hn⟩ := hM
  set c : k := M.A j (M.B i 1)
  have hword : ∀ m : ℕ,
      ((List.flatten (List.replicate m [Sum.inl j, Sum.inr i])).map M.arrow).prod (0, 1) =
        (0, c ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append,
        mul_apply_eq_comp, ih]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_apply_eq_comp, arrow_inl_apply, arrow_inr_apply]
      rw [M.B_apply i (c ^ m), map_smul, smul_eq_mul, pow_succ]
  have hlen : n ≤ (List.flatten (List.replicate n [Sum.inl j, Sum.inr i])).length := by
    simp only [List.length_flatten, List.map_replicate, List.length_cons, List.length_nil,
      List.sum_replicate, smul_eq_mul]
    omega
  have h0 := congrArg (fun f ↦ (f (0, 1)).2) (hn _ hlen)
  simp only [hword, LinearMap.zero_apply, Prod.snd_zero] at h0
  have hc : c = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at h0
    · exact (pow_eq_zero_iff hpos.ne').mp h0
  refine LinearMap.ext fun t ↦ ?_
  rw [LinearMap.comp_apply, M.B_apply i t, map_smul, LinearMap.zero_apply]
  change t • c = 0
  rw [hc, smul_zero]

/-- The map `v ↦ (A_i v)_i`, whose rank is the dimension of the span of the classes `A_i`. -/
def evalA : V →ₗ[k] (ι → k) := LinearMap.pi M.A

@[simp] lemma evalA_apply (v : V) (i : ι) : M.evalA v i = M.A i v := rfl

variable [Fintype ι]

/-- The map `t ↦ ∑ tᵢ B_i 1`, whose rank is the dimension of the span of the classes `B_i`. -/
noncomputable def sumB : (ι → k) →ₗ[k] V := Fintype.linearCombination k fun i ↦ M.B i 1

lemma sumB_apply (t : ι → k) : M.sumB t = ∑ i, t i • M.B i 1 :=
  Fintype.linearCombination_apply k _ t

/-- The preprojective relation at vertex zero, `∑ B_i A_i = 0`, is `sumB ∘ evalA = 0`. -/
lemma sumB_comp_evalA {M : DoubledRep k ι V k} (hM : M.IsPreprojective) :
    M.sumB ∘ₗ M.evalA = 0 := by
  refine LinearMap.ext fun v ↦ ?_
  have := LinearMap.congr_fun hM.1 v
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.zero_apply] at this
  simp only [LinearMap.comp_apply, sumB_apply, evalA_apply, LinearMap.zero_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun i _ ↦ (M.B_apply i _).symm

/-- Nilpotence gives `evalA ∘ sumB = 0`. -/
lemma evalA_comp_sumB {M : DoubledRep k ι V k} (hM : M.IsNilpotent) : M.evalA ∘ₗ M.sumB = 0 := by
  refine LinearMap.ext fun t ↦ funext fun j ↦ ?_
  simp only [LinearMap.comp_apply, evalA_apply, sumB_apply, map_sum, map_smul,
    LinearMap.zero_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have := LinearMap.congr_fun (hM.A_comp_B_eq_zero i j) 1
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
  rw [this, smul_zero]

lemma B_mem_range_sumB (i : ι) (t : k) : M.B i t ∈ LinearMap.range M.sumB := by
  classical
  refine ⟨Pi.single i t, ?_⟩
  rw [sumB_apply, M.B_apply i t]
  refine (Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)).trans ?_
  simp

/-! ### The endomorphisms -/

section Endomorphisms

/-- The endomorphisms `(c + f, c)` where `f : V → V` vanishes on the span of the `B_i 1` and takes
values in the common kernel of the `A_i`. -/
noncomputable def endOf :
    k × ((V ⧸ LinearMap.range M.sumB) →ₗ[k] LinearMap.ker M.evalA) →ₗ[k]
      Module.End k V × Module.End k k :=
  (LinearMap.fst k k _).smulRight (LinearMap.id, LinearMap.id) +
    LinearMap.inl k _ _ ∘ₗ (LinearMap.compRight k (LinearMap.ker M.evalA).subtype ∘ₗ
      LinearMap.lcomp k (LinearMap.ker M.evalA) (LinearMap.range M.sumB).mkQ) ∘ₗ
      LinearMap.snd k k _

lemma endOf_fst_apply (p : k × ((V ⧸ LinearMap.range M.sumB) →ₗ[k] LinearMap.ker M.evalA))
    (v : V) : (M.endOf p).1 v = p.1 • v + (p.2 (Submodule.Quotient.mk v) : V) := by
  simp [endOf, LinearMap.compRight, LinearMap.lcomp]

lemma endOf_snd_apply (p : k × ((V ⧸ LinearMap.range M.sumB) →ₗ[k] LinearMap.ker M.evalA))
    (t : k) : (M.endOf p).2 t = p.1 • t := by
  simp [endOf]

lemma endOf_mem (p : k × ((V ⧸ LinearMap.range M.sumB) →ₗ[k] LinearMap.ker M.evalA)) :
    M.endOf p ∈ Hom M M := by
  refine fun i ↦ ⟨LinearMap.ext fun v ↦ ?_, LinearMap.ext fun t ↦ ?_⟩
  · have hker := (p.2 (Submodule.Quotient.mk v)).2
    rw [LinearMap.mem_ker] at hker
    have := congrFun hker i
    simp only [evalA_apply, Pi.zero_apply] at this
    simp [M.endOf_fst_apply, M.endOf_snd_apply, this]
  · have : (Submodule.Quotient.mk (M.B i t) : V ⧸ LinearMap.range M.sumB) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (M.B_mem_range_sumB i t)
    simp only [LinearMap.comp_apply, M.endOf_fst_apply, M.endOf_snd_apply, this,
      LinearMap.map_zero, ZeroMemClass.coe_zero, add_zero]
    rw [map_smul]

lemma endOf_injective : Function.Injective M.endOf := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro p hp
  rw [LinearMap.mem_ker] at hp
  have h₁ : p.1 = 0 := by
    have := LinearMap.congr_fun (congrArg Prod.snd hp) 1
    simpa [M.endOf_snd_apply] using this
  refine Prod.ext h₁ (LinearMap.ext fun x ↦ ?_)
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    have := LinearMap.congr_fun (congrArg Prod.fst hp) v
    simp only [M.endOf_fst_apply, h₁, zero_smul, zero_add, Prod.fst_zero,
      LinearMap.zero_apply] at this
    exact Subtype.ext this

/-- **Every endomorphism is `(c + f, c)`** with `c` a scalar and `f : V/⟨B_i 1⟩ → ⋂ ker A_i`.
No relation is used, neither the preprojective relations nor nilpotence: the vertex-one space is a
line, so an endomorphism acts there by a scalar `c`, and `f₀ - c` kills every `B_i 1` and lands in
every `ker A_i`. -/
theorem endOf_surjective' (f : (V →ₗ[k] V) × (k →ₗ[k] k)) (hf : f ∈ Hom M M) :
    ∃ p, M.endOf p = f := by
  obtain ⟨f₀, f₁⟩ := f
  set c : k := f₁ 1 with hc
  have hf₁ : ∀ t, f₁ t = c * t := fun t ↦ by
    rw [show t = t • (1 : k) by simp, map_smul, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
  let g : V →ₗ[k] V := f₀ - c • LinearMap.id
  have hA : ∀ i v, M.A i (g v) = 0 := fun i v ↦ by
    have := LinearMap.congr_fun (hf i).1 v
    simp only [LinearMap.comp_apply] at this
    simp only [g, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, ← this, hf₁, smul_eq_mul, sub_self]
  have hB : ∀ i t, g (M.B i t) = 0 := fun i t ↦ by
    have := LinearMap.congr_fun (hf i).2 t
    simp only [LinearMap.comp_apply] at this
    simp only [g, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, this, hf₁]
    rw [← smul_eq_mul, map_smul, sub_self]
  have hker : ∀ v, g v ∈ LinearMap.ker M.evalA := fun v ↦ by
    rw [LinearMap.mem_ker]; funext i; simp [hA]
  have hrange : LinearMap.range M.sumB ≤ LinearMap.ker (LinearMap.codRestrict _ g hker) := by
    rw [LinearMap.ker_codRestrict]
    rintro _ ⟨t, rfl⟩
    rw [LinearMap.mem_ker, sumB_apply, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [map_smul, hB, smul_zero]
  refine ⟨(c, (LinearMap.range M.sumB).liftQ (LinearMap.codRestrict _ g hker) hrange), ?_⟩
  refine Prod.ext (LinearMap.ext fun v ↦ ?_) (LinearMap.ext fun t ↦ ?_)
  · rw [endOf_fst_apply]
    simp [g]
  · rw [endOf_snd_apply, smul_eq_mul, hf₁]

/-- **The exact endomorphism count**: `dim End M = 1 + (p - rk B)(p - rk A)` for every
representation with a line at vertex one and `V` finite-dimensional, with no relation. -/
theorem finrank_End_eq [FiniteDimensional k V] : finrank k (Hom M M) =
    1 + finrank k (V ⧸ LinearMap.range M.sumB) * finrank k (LinearMap.ker M.evalA) := by
  let φ := LinearMap.codRestrict (Hom M M) M.endOf M.endOf_mem
  have hinj : Function.Injective φ := fun x y h ↦ M.endOf_injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective φ := fun ⟨f, hf⟩ ↦ by
    obtain ⟨p, hp⟩ := M.endOf_surjective' f hf
    exact ⟨p, Subtype.ext hp⟩
  have := (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self, Module.finrank_linearMap] at this
  omega

/-- `dim End M ≥ 1 + (p - rk B)(p - rk A)`: the scalars, and the maps `V/⟨B_i 1⟩ → ⋂ ker A_i`.
A corollary of the exact count `finrank_End_eq`. -/
theorem finrank_End_ge [FiniteDimensional k V] : 1 + finrank k (V ⧸ LinearMap.range M.sumB) *
    finrank k (LinearMap.ker M.evalA) ≤ finrank k (Hom M M) :=
  M.finrank_End_eq.ge

end Endomorphisms

/-! ### The classification -/

section Classification

variable [FiniteDimensional k V]

omit [FiniteDimensional k V] in
lemma rank_add_le_card (hM : M.IsPreprojective) :
    finrank k (LinearMap.range M.evalA) + finrank k (LinearMap.range M.sumB) ≤ Fintype.card ι := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M.sumB
  have h2 : LinearMap.range M.evalA ≤ LinearMap.ker M.sumB := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.congr_fun (sumB_comp_evalA hM) v
  have h3 := Submodule.finrank_mono h2
  rw [Module.finrank_pi] at h1
  omega

lemma rank_add_le_finrank (hM : M.IsNilpotent) :
    finrank k (LinearMap.range M.evalA) + finrank k (LinearMap.range M.sumB) ≤ finrank k V := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M.evalA
  have h2 : LinearMap.range M.sumB ≤ LinearMap.ker M.evalA := by
    rintro _ ⟨t, rfl⟩
    exact LinearMap.congr_fun (evalA_comp_sumB hM) t
  have h3 := Submodule.finrank_mono h2
  omega

/-- **The one-copy identity**: with `a = rk A`, `b = rk B`, `p = dim V` and `g = |ι|`,
`dim End M + p(g - p) = 1 + ab + p(g - a - b)`. No relation is used. The left side is
`e(M)/2` up to the constant `c_U - 1` (see `oneCopy`). -/
theorem oneCopy_identity :
    (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) =
      1 + finrank k (LinearMap.range M.evalA) * finrank k (LinearMap.range M.sumB) +
        finrank k V * (Fintype.card ι - finrank k (LinearMap.range M.evalA) -
          finrank k (LinearMap.range M.sumB)) := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range M.sumB)
  have hk := LinearMap.finrank_range_add_finrank_ker M.evalA
  have hq₁ : (finrank k (V ⧸ LinearMap.range M.sumB) : ℤ) =
      finrank k V - finrank k (LinearMap.range M.sumB) := by omega
  have hq₂ : (finrank k (LinearMap.ker M.evalA) : ℤ) =
      finrank k V - finrank k (LinearMap.range M.evalA) := by omega
  rw [M.finrank_End_eq]
  push_cast
  rw [hq₁, hq₂]
  ring

/-- **The one-copy lemma for any `c`.** Let `U` occur once and `S` `p` times, with
`dim End M + p(g - p) = c`. By Riemann–Roch this is `e(M) = 2` for `c = 1 - v(U)²/2`, so
`c = 1` for `U` isotropic and `c = 2` for `U` spherical. With the
preprojective relation, both terms of `ab + p(g - a - b) = c - 1` are nonnegative. -/
theorem oneCopy (hpre : M.IsPreprojective) (c : ℤ)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = c) :
    (finrank k (LinearMap.range M.evalA) : ℤ) * finrank k (LinearMap.range M.sumB) +
        finrank k V * (Fintype.card ι - finrank k (LinearMap.range M.evalA) -
          finrank k (LinearMap.range M.sumB)) = c - 1 ∧
      0 ≤ (Fintype.card ι : ℤ) - finrank k (LinearMap.range M.evalA) -
          finrank k (LinearMap.range M.sumB) := by
  have := M.oneCopy_identity
  have h1 := M.rank_add_le_card hpre
  exact ⟨by linarith, by omega⟩

/-- **`c = 1`** (`U` isotropic): `ab = 0` and `a + b = g` when `p > 0`, from the preprojective
relation alone; nilpotence is not used. -/
theorem oneCopy_one (hpre : M.IsPreprojective)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 1)
    (hp : 0 < finrank k V) :
    finrank k (LinearMap.range M.evalA) * finrank k (LinearMap.range M.sumB) = 0 ∧
      finrank k (LinearMap.range M.evalA) + finrank k (LinearMap.range M.sumB) =
        Fintype.card ι := by
  obtain ⟨h, hg⟩ := M.oneCopy hpre 1 he
  set a := finrank k (LinearMap.range M.evalA)
  set b := finrank k (LinearMap.range M.sumB)
  set p := finrank k V
  set g := Fintype.card ι
  have hab : (0 : ℤ) ≤ a * b := by positivity
  have hpg : (0 : ℤ) ≤ p * (g - a - b) := mul_nonneg (by positivity) hg
  have h0 : (a : ℤ) * b = 0 := by linarith
  have h0' : (p : ℤ) * (g - a - b) = 0 := by linarith
  refine ⟨by exact_mod_cast h0, ?_⟩
  rcases mul_eq_zero.mp h0' with h | h
  · omega
  · omega

/-- **`c = 2`, `p ≥ 2`** (`U` spherical, at least two copies of `S`): `a = b = 1` and `g = 2`,
with no nilpotence. The exact count is needed here: the inequality `finrank_End_ge` leaves
`ab + p(g - a - b) ≤ 1`, which `(a, b, g, p) = (2, 0, 2, 2)` satisfies. -/
theorem oneCopy_two (hpre : M.IsPreprojective)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 2)
    (hp : 2 ≤ finrank k V) :
    finrank k (LinearMap.range M.evalA) = 1 ∧ finrank k (LinearMap.range M.sumB) = 1 ∧
      Fintype.card ι = 2 := by
  obtain ⟨h, hg⟩ := M.oneCopy hpre 2 he
  set a := finrank k (LinearMap.range M.evalA)
  set b := finrank k (LinearMap.range M.sumB)
  set p := finrank k V
  set g := Fintype.card ι
  have hab : (0 : ℤ) ≤ a * b := by positivity
  have hpg : (0 : ℤ) ≤ p * (g - a - b) := mul_nonneg (by positivity) hg
  -- `p(g - a - b) ≤ 1` and `p ≥ 2` force `g = a + b`, then `ab = 1`.
  have hgab : (g : ℤ) - a - b = 0 := by
    by_contra hne
    have : (1 : ℤ) ≤ g - a - b := by omega
    have : (2 : ℤ) ≤ p * (g - a - b) := by
      calc (2 : ℤ) ≤ p * 1 := by omega
        _ ≤ p * (g - a - b) := by gcongr
    linarith
  rw [hgab, mul_zero, add_zero] at h
  have hab1 : a * b = 1 := by
    have : (a : ℤ) * b = 1 := by linarith
    exact_mod_cast this
  refine ⟨Nat.eq_one_of_mul_eq_one_right hab1, Nat.eq_one_of_mul_eq_one_left hab1, ?_⟩
  have := Nat.eq_one_of_mul_eq_one_right hab1
  have := Nat.eq_one_of_mul_eq_one_left hab1
  omega

/-- **Riemann–Roch for the one-copy object, as a ring identity.** If `e(U) = 2 + u²` and
`e(M) = 2 dim End M + v(M)²` with `v(M)² = u² + 2p(g - p)`, then
`e(M) - e(U) = 2(ab + p(g - a - b))`. The integers `eM`, `eU`, `u2` are free and the two
Riemann–Roch equations are assumptions; no triangle and no budget enters. This is the Mukai
defect of the two-step tower `(U, S^p)` only when `U` is a subobject (`b = 0`) or a quotient
(`a = 0`) of `M`, the case `c = 1`. In general the HN defect differs: on the side where `U` is
higher the HN filtration is `hnUHigher`, with first factor of dimension `(b, 1)`, and Riemann–Roch
for the factors gives `2(ab + p(g - a - b) - b(g - b))`; on the side where `S` is higher it is
`2(ab + p(g - a - b) - a(g - a))`. At `c = 2` both vanish (`a = b = 1`, `g = 2`). -/
theorem oneCopy_riemannRoch (eM eU u2 : ℤ) (hU : eU = 2 + u2)
    (hM : eM = 2 * finrank k (Hom M M) + (u2 + 2 * finrank k V * (Fintype.card ι - finrank k V))) :
    eM - eU = 2 * (finrank k (LinearMap.range M.evalA) * finrank k (LinearMap.range M.sumB) +
        finrank k V * (Fintype.card ι - finrank k (LinearMap.range M.evalA) -
          finrank k (LinearMap.range M.sumB))) := by
  have := M.oneCopy_identity
  rw [hM, hU]
  linear_combination 2 * this

/-- **The rank dichotomy without nilpotence.** If `dim End M + p(g - p) = 1` and `p > 0`, the
classes `A_i` and `B_i` have ranks `(g, 0)` or `(0, g)`; only the preprojective relation is
used. -/
theorem twoExtensions_rank' (hpre : M.IsPreprojective)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 1)
    (hp : 0 < finrank k V) :
    (finrank k (LinearMap.range M.sumB) = 0 ∧
        finrank k (LinearMap.range M.evalA) = Fintype.card ι) ∨
      (finrank k (LinearMap.range M.evalA) = 0 ∧
        finrank k (LinearMap.range M.sumB) = Fintype.card ι) := by
  obtain ⟨h0, hg⟩ := M.oneCopy_one hpre he hp
  rcases Nat.mul_eq_zero.mp h0 with ha | hb
  · exact Or.inr ⟨ha, by omega⟩
  · exact Or.inl ⟨hb, by omega⟩

/-- **The numerical core of the lemma on the wall group that carries the point.** For a
nilpotent representation with the preprojective relations, of dimension vector `(p, 1)` with
`p > 0` and `e(M) = 2`, that is `dim End M + p(g - p) = 1`: `p ≥ g`, and the classes `A_i` and
`B_i` have ranks `(g, 0)` or `(0, g)`. The rank dichotomy is `twoExtensions_rank'`, from the
preprojective relation alone; nilpotence enters only for `p ≥ g`, through `a + b ≤ p`. -/
theorem twoExtensions_rank (hpre : M.IsPreprojective) (hnil : M.IsNilpotent)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 1)
    (hp : 0 < finrank k V) :
    Fintype.card ι ≤ finrank k V ∧
      ((finrank k (LinearMap.range M.sumB) = 0 ∧
          finrank k (LinearMap.range M.evalA) = Fintype.card ι) ∨
        (finrank k (LinearMap.range M.evalA) = 0 ∧
          finrank k (LinearMap.range M.sumB) = Fintype.card ι)) := by
  obtain ⟨_, hg⟩ := M.oneCopy_one hpre he hp
  have h2 := M.rank_add_le_finrank hnil
  exact ⟨by omega, M.twoExtensions_rank' hpre he hp⟩

/-- **The classes of the lemma on the wall group that carries the point, without nilpotence.**
If `dim End M + p(g - p) = 1` and `p > 0`, either every `B_i` vanishes and the `A_i` are linearly
independent, or every `A_i` vanishes and the `B_i 1` are linearly independent. -/
theorem twoExtensions' (hpre : M.IsPreprojective)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 1)
    (hp : 0 < finrank k V) :
    ((∀ i, M.B i = 0) ∧ LinearIndependent k M.A) ∨
      ((∀ i, M.A i = 0) ∧ LinearIndependent k fun i ↦ M.B i 1) := by
  classical
  have h := M.twoExtensions_rank' hpre he hp
  have hk' := LinearMap.finrank_range_add_finrank_ker M.sumB
  rw [Module.finrank_pi] at hk'
  rcases h with ⟨hb, ha⟩ | ⟨ha, hb⟩
  · -- No `B`: the classes `A_i` span a `g`-dimensional space.
    left
    have hb' : LinearMap.range M.sumB = ⊥ := Submodule.finrank_eq_zero.mp hb
    refine ⟨fun i ↦ LinearMap.ext fun t ↦ ?_, ?_⟩
    · have := M.B_mem_range_sumB i t
      rw [hb', Submodule.mem_bot] at this
      rw [this, LinearMap.zero_apply]
    · have htop : LinearMap.range M.evalA = ⊤ := Submodule.eq_top_of_finrank_eq (by
        rw [Module.finrank_pi]; exact ha)
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      obtain ⟨v, hv⟩ : (Pi.single i (1 : k) : ι → k) ∈ LinearMap.range M.evalA :=
        htop ▸ Submodule.mem_top
      have := LinearMap.congr_fun hc v
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        smul_eq_mul] at this
      have hA : ∀ j, M.A j v = (Pi.single i (1 : k) : ι → k) j := fun j ↦ by
        rw [← evalA_apply, hv]
      simpa [hA, Pi.single_apply] using this
  · -- No `A`: the classes `B_i` span a `g`-dimensional space.
    right
    have ha' : LinearMap.range M.evalA = ⊥ := Submodule.finrank_eq_zero.mp ha
    refine ⟨fun i ↦ LinearMap.ext fun v ↦ ?_, ?_⟩
    · have : M.evalA v ∈ LinearMap.range M.evalA := LinearMap.mem_range_self _ v
      rw [ha', Submodule.mem_bot] at this
      exact congrFun this i
    · have hker : LinearMap.ker M.sumB = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have : c ∈ LinearMap.ker M.sumB := by rw [LinearMap.mem_ker, sumB_apply]; exact hc
      rw [hker, Submodule.mem_bot] at this
      exact fun i ↦ congrFun this i

/-- **The lemma on the wall group that carries the point.** Let `M` be a nilpotent
representation with the preprojective relations, of dimension vector `(p, 1)` with `p > 0`,
satisfying `e(M) = 2`, that is `dim End M + p(g - p) = 1`. Then `p ≥ g`, and either every `B_i`
vanishes and the `A_i` are linearly independent (`M = S^{p-g} ⊕ T_S U`), or every `A_i` vanishes
and the `B_i 1` are linearly independent (`M = S^{p-g} ⊕ T_S⁻¹ U`). Nilpotence is used only for
`p ≥ g` (`twoExtensions'`). -/
theorem twoExtensions (hpre : M.IsPreprojective) (hnil : M.IsNilpotent)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 1)
    (hp : 0 < finrank k V) :
    Fintype.card ι ≤ finrank k V ∧
      (((∀ i, M.B i = 0) ∧ LinearIndependent k M.A) ∨
        ((∀ i, M.A i = 0) ∧ LinearIndependent k fun i ↦ M.B i 1)) :=
  ⟨(M.twoExtensions_rank hpre hnil he hp).1, M.twoExtensions' hpre he hp⟩

end Classification

/-! ### One copy of a spherical simple: the rank-one normal form -/

section RankOne

variable [FiniteDimensional k V]

/-- **The rank-one normal form at `c = 2`.** Let `U` be spherical, occurring once, and `S` occur
`p ≥ 2` times, with `e(M) = 2`, that is `dim End M + p(g - p) = 2`. Then `g = 2`, and there are a
nonzero functional `φ` on `V`, a nonzero vector `w ∈ V` and nonzero `α, β : ι → k` with
`A_i = α_i φ`, `B_i 1 = β_i w`, `∑ α_i β_i = 0` (the preprojective relation) and `φ(w) = 0`
(nilpotence). So the classes `A_i` span the line `kα` and the `B_i` the line `kβ`, with
`β ⊥ α`. -/
theorem oneCopy_two_rankOne (hpre : M.IsPreprojective) (hnil : M.IsNilpotent)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 2)
    (hp : 2 ≤ finrank k V) :
    Fintype.card ι = 2 ∧ ∃ (φ : V →ₗ[k] k) (α : ι → k) (w : V) (β : ι → k),
      φ ≠ 0 ∧ α ≠ 0 ∧ w ≠ 0 ∧ β ≠ 0 ∧ (∀ i v, M.A i v = α i * φ v) ∧
        (∀ i, M.B i 1 = β i • w) ∧ ∑ i, α i * β i = 0 ∧ φ w = 0 := by
  classical
  obtain ⟨ha, hb, hg⟩ := M.oneCopy_two hpre he hp
  refine ⟨hg, ?_⟩
  -- the classes `A_i`: a line `kα`
  obtain ⟨⟨α, hαr⟩, hα0, hαspan⟩ := finrank_eq_one_iff'.mp ha
  have hα : α ≠ 0 := fun h ↦ hα0 (Subtype.ext h)
  obtain ⟨i₀, hi₀⟩ : ∃ i, α i ≠ 0 := by
    by_contra h
    push Not at h
    exact hα (funext h)
  let φ : V →ₗ[k] k := (α i₀)⁻¹ • M.A i₀
  have hA : ∀ i v, M.A i v = α i * φ v := by
    intro i v
    obtain ⟨c, hc⟩ := hαspan ⟨M.evalA v, LinearMap.mem_range_self _ v⟩
    have hc' : c • α = M.evalA v := congrArg Subtype.val hc
    have hi := congrFun hc' i
    have hi₀' := congrFun hc' i₀
    simp only [Pi.smul_apply, smul_eq_mul, evalA_apply] at hi hi₀'
    simp only [φ, LinearMap.smul_apply, smul_eq_mul, ← hi, ← hi₀']
    field_simp
  -- the classes `B_i`: a line `kw`
  obtain ⟨⟨w, hwr⟩, hw0, hwspan⟩ := finrank_eq_one_iff'.mp hb
  have hw : w ≠ 0 := fun h ↦ hw0 (Subtype.ext h)
  have hβex : ∀ i, ∃ c : k, c • w = M.B i 1 := fun i ↦ by
    obtain ⟨c, hc⟩ := hwspan ⟨M.B i 1, M.B_mem_range_sumB i 1⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose β hβ using hβex
  have hB : ∀ i, M.B i 1 = β i • w := fun i ↦ (hβ i).symm
  -- `φ ≠ 0` and `β ≠ 0`, since the ranks are one
  obtain ⟨v₀, hv₀⟩ : ∃ v, φ v ≠ 0 := by
    obtain ⟨v, hv⟩ := hαr
    by_contra h
    push Not at h
    exact hα (by rw [← hv]; funext i; simp [hA, h])
  have hφ : φ ≠ 0 := fun h ↦ hv₀ (by rw [h, LinearMap.zero_apply])
  obtain ⟨j₀, hj₀⟩ : ∃ i, β i ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨t, ht⟩ := hwr
    exact hw (by rw [← ht, sumB_apply]; simp [hB, h])
  have hβ0 : β ≠ 0 := fun h ↦ hj₀ (by rw [h, Pi.zero_apply])
  refine ⟨φ, α, w, β, hφ, hα, hw, hβ0, hA, hB, ?_, ?_⟩
  · -- the preprojective relation at vertex zero, evaluated at `v₀`
    have := LinearMap.congr_fun hpre.1 v₀
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.zero_apply] at this
    have hsum : (φ v₀ * ∑ i, α i * β i) • w = 0 := by
      rw [← this, Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [M.B_apply, hB, hA, smul_smul]
      ring_nf
    rcases smul_eq_zero.mp hsum with h | h
    · exact (mul_eq_zero.mp h).resolve_left hv₀
    · exact absurd h hw
  · -- nilpotence: `A_{i₀} B_{j₀} = 0`
    have := LinearMap.congr_fun (hnil.A_comp_B_eq_zero j₀ i₀) 1
    rw [LinearMap.comp_apply, hB, map_smul, hA, LinearMap.zero_apply, smul_eq_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hj₀
    · exact (mul_eq_zero.mp h).resolve_left hi₀

/-- **The converse count.** A representation in rank-one form, `A_i = α_i φ` and `B_i 1 = β_i w`
with `φ`, `α`, `w`, `β` nonzero, has `dim End M + p(g - p) = 2 + p(g - 2)`; for `g = 2` this is
`e(M) = 2` with `U` spherical. No relation is used. -/
theorem oneCopy_of_rankOne (φ : V →ₗ[k] k) (α : ι → k) (w : V) (β : ι → k) (hφ : φ ≠ 0)
    (hα : α ≠ 0) (hw : w ≠ 0) (hβ : β ≠ 0) (hA : ∀ i v, M.A i v = α i * φ v)
    (hB : ∀ i, M.B i 1 = β i • w) :
    (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) =
      2 + finrank k V * (Fintype.card ι - 2) := by
  classical
  have hrA : LinearMap.range M.evalA = k ∙ α := by
    obtain ⟨v₀, hv₀⟩ : ∃ v, φ v ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, rfl⟩
      exact Submodule.mem_span_singleton.mpr ⟨φ v, funext fun i ↦ by simp [hA, mul_comm]⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨(φ v₀)⁻¹ • v₀, funext fun i ↦ ?_⟩
      simp [hA, hv₀]
  have hrB : LinearMap.range M.sumB = k ∙ w := by
    obtain ⟨j₀, hj₀⟩ : ∃ i, β i ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ (funext h)
    refine le_antisymm ?_ ?_
    · rintro _ ⟨t, rfl⟩
      rw [sumB_apply]
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
        (by rw [hB]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
    · rw [Submodule.span_singleton_le_iff_mem]
      have := M.B_mem_range_sumB j₀ (β j₀)⁻¹
      rwa [M.B_apply, hB, smul_smul, inv_mul_cancel₀ hj₀, one_smul] at this
  have ha : finrank k (LinearMap.range M.evalA) = 1 := by rw [hrA, finrank_span_singleton hα]
  have hb : finrank k (LinearMap.range M.sumB) = 1 := by rw [hrB, finrank_span_singleton hw]
  have := M.oneCopy_identity
  rw [ha, hb] at this
  push_cast at this
  linarith

/-- **The line of a semirigid object.** At `c = 2` with `p ≥ 2`, the classes `A_i` span a line in
`k^ι`: the image of `evalA`. An isomorphism of representations scales `evalA` by the scalar at
vertex one, so the line is an invariant of `M`, and the line of the classes `B_i` is its
orthogonal for `∑ α_i β_i` (`oneCopy_two_rankOne`). -/
theorem oneCopy_two_range_evalA (hpre : M.IsPreprojective) (hnil : M.IsNilpotent)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 2)
    (hp : 2 ≤ finrank k V) :
    ∃ α : ι → k, α ≠ 0 ∧ LinearMap.range M.evalA = k ∙ α := by
  obtain ⟨-, φ, α, w, β, hφ, hα, hw, hβ, hA, hB, -, -⟩ := M.oneCopy_two_rankOne hpre hnil he hp
  refine ⟨α, hα, le_antisymm ?_ ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨φ v, funext fun i ↦ by simp [hA, mul_comm]⟩
  · obtain ⟨v₀, hv₀⟩ : ∃ v, φ v ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨(φ v₀)⁻¹ • v₀, funext fun i ↦ ?_⟩
    simp [hA, hv₀]

end RankOne

/-! ### The two sides of the wall -/

section HarderNarasimhan

omit [Fintype ι] in
lemma submodule_eq_bot_or_top (U : Submodule k k) : U = ⊥ ∨ U = ⊤ := Ideal.eq_bot_or_top U

/-- The subrepresentation `(⋂ ker A_i, 0)`: the largest one in which `U` does not occur, a sum of
`p - rk A` copies of `S`. -/
def subKer : M.subreps :=
  ⟨(LinearMap.ker M.evalA, ⊥), fun i ↦ ⟨fun v hv ↦ by
    rw [LinearMap.mem_ker] at hv
    simpa using congrFun hv i, bot_le⟩⟩

/-- The subrepresentation `(⟨B_i 1⟩, k)`: the smallest one in which `U` occurs. -/
noncomputable def subSpan : M.subreps :=
  ⟨(LinearMap.range M.sumB, ⊤), fun i ↦ ⟨fun _ _ ↦ Submodule.mem_top,
    fun t _ ↦ M.B_mem_range_sumB i t⟩⟩

omit [Fintype ι] in
/-- A subrepresentation without `U` lies in `(⋂ ker A_i, 0)`. -/
lemma le_subKer {z : M.subreps} (hz : (z : Submodule k V × Submodule k k).2 = ⊥) :
    z ≤ M.subKer := by
  refine Prod.mk_le_mk.mpr ⟨fun v hv ↦ ?_, hz.le⟩
  rw [LinearMap.mem_ker]
  funext i
  have := DoubledRep.A_mem z i hv
  rw [hz, Submodule.mem_bot] at this
  exact this

/-- A subrepresentation containing `U` contains `(⟨B_i 1⟩, k)`. -/
lemma subSpan_le {z : M.subreps} (hz : (z : Submodule k V × Submodule k k).2 = ⊤) :
    M.subSpan ≤ z := by
  refine Prod.mk_le_mk.mpr ⟨?_, hz.ge⟩
  rintro _ ⟨t, rfl⟩
  rw [sumB_apply]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (DoubledRep.B_mem z i (hz ▸ Submodule.mem_top))

lemma dimVec_subSpan : DoubledRep.dimVec M.subSpan =
    (finrank k (LinearMap.range M.sumB), 1) := by
  show (finrank k (LinearMap.range M.sumB), finrank k (⊤ : Submodule k k)) = _
  rw [finrank_top, Module.finrank_self]

omit [Fintype ι] in
lemma dimVec_subKer : DoubledRep.dimVec M.subKer = (finrank k (LinearMap.ker M.evalA), 0) := by
  show (finrank k (LinearMap.ker M.evalA), finrank k (⊥ : Submodule k k)) = _
  rw [finrank_bot]

variable [FiniteDimensional k V] (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The side where `U` has the higher phase, first factor.** `(⟨B_i 1⟩, k)` is stable for
`wallSlope`: a nonzero proper subrepresentation of it does not contain `U`, so has slope `0`. -/
theorem isStable_bot_subSpan : (wallSlope K M).IsStable ⊥ M.subSpan := by
  have hlt : (⊥ : M.subreps) < M.subSpan := bot_lt_iff_ne_bot.mpr fun h ↦ by
    have := congrArg (fun z : M.subreps ↦ (z : Submodule k V × Submodule k k).2) h
    simp [subSpan] at this
  refine ⟨hlt, fun z h₁ h₂ ↦ ?_⟩
  rcases submodule_eq_bot_or_top (z : Submodule k V × Submodule k k).2 with hz | hz
  · rw [SlopeFunction.weight_slope_lt_iff _ hlt]
    have h0 : (z : Submodule k V × Submodule k k).1 ≠ ⊥ := fun h ↦ h₁.ne' (Subtype.ext
      (Prod.ext h hz))
    have hpos : 0 < finrank k (z : Submodule k V × Submodule k k).1 :=
      Nat.pos_of_ne_zero fun h ↦ h0 (Submodule.finrank_eq_zero.mp h)
    have hj : finrank k (z : Submodule k V × Submodule k k).2 = 0 := by
      rw [hz]
      exact finrank_bot k k
    simp only [wallSlope_rk, wallSlope_deg, DoubledRep.dimVec_bot, M.dimVec_subSpan]
    simp only [DoubledRep.dimVec, hj]
    have : (0 : K) < finrank k (z : Submodule k V × Submodule k k).1 := by exact_mod_cast hpos
    push_cast
    linarith
  · exact absurd (le_antisymm h₂.le (M.subSpan_le hz)) h₂.ne

/-- **The side where `U` has the higher phase, second factor.** Above `(⟨B_i 1⟩, k)` every
subrepresentation contains `U`, so the quotient `S^{p - rk B}` has slope `0`. -/
theorem isSemistable_subSpan_top (h : M.subSpan < ⊤) :
    (wallSlope K M).IsSemistable M.subSpan ⊤ := by
  refine ⟨h, fun z h₁ _ ↦ ?_⟩
  rw [SlopeFunction.weight_slope_le_iff _ h]
  have hz : (z : Submodule k V × Submodule k k).2 = ⊤ := top_le_iff.mp (Prod.mk_le_mk.mp h₁).2
  have hj : finrank k (z : Submodule k V × Submodule k k).2 = 1 := by
    rw [hz, finrank_top, Module.finrank_self]
  simp only [wallSlope_rk, wallSlope_deg, M.dimVec_subSpan, DoubledRep.dimVec_top,
    Module.finrank_self]
  simp only [DoubledRep.dimVec, hj]
  simp

lemma slope_subSpan :
    (wallSlope K M).slope M.subSpan ⊤ < (wallSlope K M).slope ⊥ M.subSpan := by
  simp only [SlopeFunction.slope, wallSlope_rk, wallSlope_deg, M.dimVec_subSpan,
    DoubledRep.dimVec_bot, DoubledRep.dimVec_top]
  simp only [Module.finrank_self, Nat.cast_one, sub_self, zero_div, Nat.cast_zero, sub_zero,
    add_zero]
  positivity

/-- **The HN filtration on the side where `U` has the higher phase**: `0 ⊂ (⟨B_i 1⟩, k) ⊂ M`,
with first factor stable of dimension `(rk B, 1)` and second factor `S^{p - rk B}`. -/
noncomputable def hnUHigher (h : M.subSpan < ⊤) : (wallSlope K M).HNFiltration :=
  SlopeFunction.HNFiltration.two (M.isStable_bot_subSpan K).isSemistable
    (M.isSemistable_subSpan_top K h) (M.slope_subSpan K)

omit [Fintype ι] in
/-- **The side where `S` has the higher phase, first factor.** `(⋂ ker A_i, 0)` is a sum of
copies of `S`: all its subrepresentations have slope `0` for `wallSlope.neg`. -/
theorem isSemistable_bot_subKer (h : ⊥ < M.subKer) :
    (wallSlope K M).neg.IsSemistable ⊥ M.subKer := by
  refine ⟨h, fun z _ h₂ ↦ ?_⟩
  rw [SlopeFunction.weight_slope_le_iff _ h]
  have hz : (z : Submodule k V × Submodule k k).2 = ⊥ := le_bot_iff.mp (Prod.mk_le_mk.mp h₂).2
  have hj : finrank k (z : Submodule k V × Submodule k k).2 = 0 := by
    rw [hz]
    exact finrank_bot k k
  simp only [SlopeFunction.neg_rk, SlopeFunction.neg_deg, wallSlope_rk, wallSlope_deg,
    M.dimVec_subKer, DoubledRep.dimVec_bot]
  simp only [DoubledRep.dimVec, hj]
  simp

omit [Fintype ι] in
/-- **The side where `S` has the higher phase, second factor.** `M/(⋂ ker A_i, 0)` is stable
for `wallSlope.neg`: a subrepresentation strictly between contains `U`, and a proper one has
fewer copies of `S`. -/
theorem isStable_subKer_top : (wallSlope K M).neg.IsStable M.subKer ⊤ := by
  have hlt : M.subKer < ⊤ := lt_top_iff_ne_top.mpr fun h ↦ by
    have := congrArg (fun z : M.subreps ↦ (z : Submodule k V × Submodule k k).2) h
    simp [subKer] at this
  refine ⟨hlt, fun z h₁ h₂ ↦ ?_⟩
  rcases submodule_eq_bot_or_top (z : Submodule k V × Submodule k k).2 with hz | hz
  · exact absurd (le_antisymm (M.le_subKer hz) h₁.le) h₁.ne'
  · rw [SlopeFunction.weight_slope_lt_iff _ hlt]
    have h1 : (z : Submodule k V × Submodule k k).1 ≠ ⊤ := fun h ↦ h₂.ne (Subtype.ext
      (Prod.ext h hz))
    have hlt' := Submodule.finrank_lt h1
    have hj : finrank k (z : Submodule k V × Submodule k k).2 = 1 := by
      rw [hz, finrank_top, Module.finrank_self]
    simp only [SlopeFunction.neg_rk, SlopeFunction.neg_deg, wallSlope_rk, wallSlope_deg,
      M.dimVec_subKer, DoubledRep.dimVec_top, Module.finrank_self]
    simp only [DoubledRep.dimVec, hj]
    have : (finrank k (z : Submodule k V × Submodule k k).1 : K) < finrank k V := by
      exact_mod_cast hlt'
    push_cast
    linarith

omit [Fintype ι] in
lemma slope_subKer :
    (wallSlope K M).neg.slope M.subKer ⊤ < (wallSlope K M).neg.slope ⊥ M.subKer := by
  have hlt := (M.isStable_subKer_top K).1
  have hrk := (wallSlope K M).neg.rk_strictMono hlt
  simp only [SlopeFunction.slope, SlopeFunction.neg_rk, SlopeFunction.neg_deg, wallSlope_rk,
    wallSlope_deg, M.dimVec_subKer, DoubledRep.dimVec_bot, DoubledRep.dimVec_top,
    Module.finrank_self] at hrk ⊢
  simp only [Nat.cast_zero, Nat.cast_one, add_zero, neg_zero, sub_self, zero_div] at hrk ⊢
  exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

omit [Fintype ι] in
/-- **The HN filtration on the side where `S` has the higher phase**: `0 ⊂ (⋂ ker A_i, 0) ⊂ M`,
with first factor `S^{p - rk A}` and second factor stable of dimension `(rk A, 1)`. -/
noncomputable def hnSHigher (h : ⊥ < M.subKer) : (wallSlope K M).neg.HNFiltration :=
  SlopeFunction.HNFiltration.two (M.isSemistable_bot_subKer K h)
    (M.isStable_subKer_top K).isSemistable (M.slope_subKer K)

/-- **The table of the lemma on the wall group that carries the point.** For `M` with
`e(M) = 2`, `p > 0` and `k = p - g`, one of the two rows holds.

* `S^k ⊕ T_S U`: the smallest subrepresentation containing `U` is `U` itself, of dimension
  `(0, 1)`, so on the side where `U` has the higher phase the HN quotients are `U, S^p`; the
  largest one without `U` is `S^k`, so on the side where `S` is higher they are `S^k, T_S U`.
* `S^k ⊕ T_S⁻¹ U`: the smallest subrepresentation containing `U` is `T_S⁻¹ U`, of dimension
  `(g, 1)`, so where `U` is higher the HN quotients are `T_S⁻¹ U, S^k`; the largest one without
  `U` is `S^p`, so where `S` is higher they are `S^p, U`.

The HN filtrations are `hnUHigher` and `hnSHigher`, with stable factors `isStable_bot_subSpan`
and `isStable_subKer_top`; a zero term (`k = 0`) means that `M` itself is the stable factor. -/
theorem twoExtensions_table (hpre : M.IsPreprojective) (hnil : M.IsNilpotent)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 1)
    (hp : 0 < finrank k V) :
    Fintype.card ι ≤ finrank k V ∧
      ((DoubledRep.dimVec M.subSpan = (0, 1) ∧
          DoubledRep.dimVec M.subKer = (finrank k V - Fintype.card ι, 0)) ∨
        (DoubledRep.dimVec M.subSpan = (Fintype.card ι, 1) ∧
          DoubledRep.dimVec M.subKer = (finrank k V, 0))) := by
  obtain ⟨hgp, h⟩ := M.twoExtensions_rank hpre hnil he hp
  have hk := LinearMap.finrank_range_add_finrank_ker M.evalA
  refine ⟨hgp, ?_⟩
  rw [M.dimVec_subSpan, M.dimVec_subKer]
  rcases h with ⟨hb, ha⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨by rw [hb], by rw [Prod.mk.injEq]; omega⟩
  · exact Or.inr ⟨by rw [hb], by rw [Prod.mk.injEq]; omega⟩

end HarderNarasimhan

end Quiver.Kronecker.DoubledRep
