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
* `finrank_End_ge`: `dim End M ≥ 1 + (p - rk B)(p - rk A)`;
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

/-- `dim End M ≥ 1 + (p - rk B)(p - rk A)`: the scalars, and the maps `V/⟨B_i 1⟩ → ⋂ ker A_i`. -/
theorem finrank_End_ge [FiniteDimensional k V] : 1 + finrank k (V ⧸ LinearMap.range M.sumB) *
    finrank k (LinearMap.ker M.evalA) ≤ finrank k (Hom M M) := by
  have := LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.codRestrict (Hom M M) M.endOf M.endOf_mem) (fun x y h ↦
      M.endOf_injective (congrArg Subtype.val h))
  rwa [Module.finrank_prod, Module.finrank_self, Module.finrank_linearMap] at this

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

/-- **The numerical core of the lemma on the wall group that carries the point.** For a
nilpotent representation with the preprojective relations, of dimension vector `(p, 1)` with
`p > 0` and `e(M) = 2`, that is `dim End M + p(g - p) = 1`: `p ≥ g`, and the classes `A_i` and
`B_i` have ranks `(g, 0)` or `(0, g)`. With `a = rk A`, `b = rk B`, the bound
`dim End M ≥ 1 + (p - a)(p - b)` and the identity `(p - a)(p - b) + p(g - p) = ab + p(g - a - b)`
leave `ab = 0` and `a + b = g`, as `twoExtensions_numerics` does in the draft's notation. -/
theorem twoExtensions_rank (hpre : M.IsPreprojective) (hnil : M.IsNilpotent)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 1)
    (hp : 0 < finrank k V) :
    Fintype.card ι ≤ finrank k V ∧
      ((finrank k (LinearMap.range M.sumB) = 0 ∧
          finrank k (LinearMap.range M.evalA) = Fintype.card ι) ∨
        (finrank k (LinearMap.range M.evalA) = 0 ∧
          finrank k (LinearMap.range M.sumB) = Fintype.card ι)) := by
  have h1 := M.rank_add_le_card hpre
  have h2 := M.rank_add_le_finrank hnil
  have h3 := M.finrank_End_ge
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range M.sumB)
  have hk := LinearMap.finrank_range_add_finrank_ker M.evalA
  set p := finrank k V
  set g := Fintype.card ι
  set a := finrank k (LinearMap.range M.evalA)
  set b := finrank k (LinearMap.range M.sumB)
  set q₁ := finrank k (V ⧸ LinearMap.range M.sumB)
  set q₂ := finrank k (LinearMap.ker M.evalA)
  -- `(p - b)(p - a) + p(g - p) = ab + p(g - a - b)`, and both terms are nonnegative.
  have hE : (1 : ℤ) + q₁ * q₂ ≤ finrank k (Hom M M) := by exact_mod_cast h3
  have hq₁ : (q₁ : ℤ) = p - b := by omega
  have hq₂ : (q₂ : ℤ) = p - a := by omega
  have hsum : (a : ℤ) * b + p * (g - a - b) ≤ 0 := by
    rw [hq₁, hq₂] at hE
    nlinarith
  have hpos : (0 : ℤ) ≤ p * (g - a - b) := mul_nonneg (by positivity) (by omega)
  have hab : (a : ℤ) * b = 0 := by
    have : (0 : ℤ) ≤ a * b := by positivity
    linarith
  have hg : a + b = g := by
    have : (0 : ℤ) ≤ a * b := by positivity
    have h' : (p : ℤ) * (g - a - b) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h | h
    · omega
    · omega
  refine ⟨by omega, ?_⟩
  rcases mul_eq_zero.mp hab with ha | hb
  · exact Or.inr ⟨by exact_mod_cast ha, by omega⟩
  · exact Or.inl ⟨by exact_mod_cast hb, by omega⟩

/-- **The lemma on the wall group that carries the point.** Let `M` be a nilpotent
representation with the preprojective relations, of dimension vector `(p, 1)` with `p > 0`,
satisfying `e(M) = 2`, that is `dim End M + p(g - p) = 1`. Then `p ≥ g`, and either every `B_i`
vanishes and the `A_i` are linearly independent (`M = S^{p-g} ⊕ T_S U`), or every `A_i` vanishes
and the `B_i 1` are linearly independent (`M = S^{p-g} ⊕ T_S⁻¹ U`). -/
theorem twoExtensions (hpre : M.IsPreprojective) (hnil : M.IsNilpotent)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 1)
    (hp : 0 < finrank k V) :
    Fintype.card ι ≤ finrank k V ∧
      (((∀ i, M.B i = 0) ∧ LinearIndependent k M.A) ∨
        ((∀ i, M.A i = 0) ∧ LinearIndependent k fun i ↦ M.B i 1)) := by
  classical
  obtain ⟨hgp, h⟩ := M.twoExtensions_rank hpre hnil he hp
  have hk' := LinearMap.finrank_range_add_finrank_ker M.sumB
  rw [Module.finrank_pi] at hk'
  refine ⟨hgp, ?_⟩
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

end Classification

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
