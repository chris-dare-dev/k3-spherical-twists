/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.IntervalClass
import K3Twists.RepresentationTheory.Quiver.Kronecker.TwoExtensions

/-!
# The radical of the representations supported at vertex zero

A representation of the doubled Kronecker quiver whose space at vertex one is zero has all its
arrows zero: it is a sum of copies of the simple representation `S` at vertex zero. These
representations form a class closed under subrepresentations, quotients and extensions. For a
representation `M`, "the subquotient `N' / N` is supported at vertex zero" reads
`N'₁ ≤ N₁` on the vertex-one parts, and it is an interval class on the lattice of
subrepresentations (`vertexZeroClass M`). Its order theory computes:

* `sat_vertexZeroClass`: the saturation of `N = (N₀, N₁)` is `(⋂ᵢ Aᵢ⁻¹(N₁), N₁)`;
* `rad_vertexZeroClass`: the radical is `(⋂ᵢ ker Aᵢ, 0)`, the largest subrepresentation that is
  a sum of copies of `S`;
* `vertexZeroClass_hereditary`: the class is hereditary, so the nested formula holds.

At a wall where `U` (the simple at vertex one) occurs once, the radical is the subrepresentation
`subKer` (`rad_vertexZeroClass_eq_subKer`), which is the first step of the HN filtration on the
side where `S` has the higher phase (`hnSHigher_chain_one`): the top HN factor is the evaluation
of the top phase, the largest subobject in the class `add S` of semistable objects of that phase.

## Tags

quiver representation, radical, saturation, socle, interval class
-/

namespace Quiver.Kronecker.DoubledRep

open Module

variable {k ι V₀ V₁ : Type*} [Field k] [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
  [Module k V₁] {M : DoubledRep k ι V₀ V₁}

lemma fst_le_fst {N N' : M.subreps} (h : N ≤ N') :
    (N : Submodule k V₀ × Submodule k V₁).1 ≤ (N' : Submodule k V₀ × Submodule k V₁).1 :=
  (show (N : Submodule k V₀ × Submodule k V₁) ≤ N' from h).1

lemma snd_le_snd {N N' : M.subreps} (h : N ≤ N') :
    (N : Submodule k V₀ × Submodule k V₁).2 ≤ (N' : Submodule k V₀ × Submodule k V₁).2 :=
  (show (N : Submodule k V₀ × Submodule k V₁) ≤ N' from h).2

variable (M) in
/-- The interval class of the representations supported at vertex zero: `N' / N` has zero space
at vertex one, `N'₁ ≤ N₁`. -/
def vertexZeroClass : IntervalClass M.subreps where
  Q N N' := (N' : Submodule k V₀ × Submodule k V₁).2 ≤ (N : Submodule k V₀ × Submodule k V₁).2
  refl _ := le_rfl
  trans _ _ h₁ h₂ := h₂.trans h₁
  push {_ _ _} h₁ _ h := by
    rw [coe_sup_snd]
    exact sup_le le_rfl (h.trans (snd_le_snd h₁))

@[simp]
lemma vertexZeroClass_Q (N N' : M.subreps) :
    (vertexZeroClass M).Q N N' ↔
      (N' : Submodule k V₀ × Submodule k V₁).2 ≤ (N : Submodule k V₀ × Submodule k V₁).2 :=
  Iff.rfl

/-- The class of representations supported at vertex zero is closed under subrepresentations. -/
theorem vertexZeroClass_hereditary : (vertexZeroClass M).Hereditary :=
  fun _ _ _ _ hbc h => (snd_le_snd hbc).trans h

variable (M) in
/-- The subrepresentation `(⋂ᵢ Aᵢ⁻¹(N₁), N₁)` of a subrepresentation `N = (N₀, N₁)`. -/
def vertexZeroSat (N : M.subreps) : M.subreps :=
  ⟨(⨅ i, (N : Submodule k V₀ × Submodule k V₁).2.comap (M.A i),
      (N : Submodule k V₀ × Submodule k V₁).2),
    fun i => ⟨iInf_le (fun j => (N : Submodule k V₀ × Submodule k V₁).2.comap (M.A j)) i,
      fun _ hy => Submodule.mem_iInf _ |>.mpr fun j => A_mem N j (B_mem N i hy)⟩⟩

@[simp]
lemma coe_vertexZeroSat (N : M.subreps) :
    (M.vertexZeroSat N : Submodule k V₀ × Submodule k V₁) =
      (⨅ i, (N : Submodule k V₀ × Submodule k V₁).2.comap (M.A i),
        (N : Submodule k V₀ × Submodule k V₁).2) :=
  rfl

/-- `(⋂ᵢ Aᵢ⁻¹(N₁), N₁)` is the greatest subrepresentation `N' ≥ N` with `N' / N` supported at
vertex zero. -/
theorem isGreatest_vertexZeroSat (N : M.subreps) :
    IsGreatest ((vertexZeroClass M).cands N ⊤) (M.vertexZeroSat N) := by
  refine ⟨⟨?_, le_top, le_rfl⟩, ?_⟩
  · refine Prod.mk_le_mk.mpr ⟨le_iInf fun i x hx => A_mem N i hx, le_rfl⟩
  · rintro N' ⟨-, -, hQ⟩
    refine Prod.mk_le_mk.mpr ⟨le_iInf fun i x hx => hQ (A_mem N' i hx), hQ⟩

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁]

/-- **The saturation** of `N = (N₀, N₁)` for the class supported at vertex zero is
`(⋂ᵢ Aᵢ⁻¹(N₁), N₁)`. -/
theorem sat_vertexZeroClass (N : M.subreps) :
    (vertexZeroClass M).sat N = M.vertexZeroSat N :=
  (vertexZeroClass M).sat_eq_of_isGreatest (isGreatest_vertexZeroSat N)

/-- **The radical** of the class supported at vertex zero is `(⋂ᵢ ker Aᵢ, 0)`: the largest
subrepresentation that is a sum of copies of the simple at vertex zero. -/
theorem rad_vertexZeroClass :
    ((vertexZeroClass M).rad : Submodule k V₀ × Submodule k V₁) =
      (⨅ i, LinearMap.ker (M.A i), ⊥) := by
  rw [IntervalClass.rad, sat_vertexZeroClass, coe_vertexZeroSat]
  simp [Submodule.comap_bot]

/-- **The nested formula** for the class supported at vertex zero: for `N ≤ N'`, the greatest
subrepresentation between `N` and `N'` whose quotient by `N` is supported at vertex zero is
`N' ⊓ (⋂ᵢ Aᵢ⁻¹(N₁), N₁)`. -/
theorem isGreatest_inf_vertexZeroSat {N N' : M.subreps} (h : N ≤ N') :
    IsGreatest ((vertexZeroClass M).cands N N') (N' ⊓ M.vertexZeroSat N) := by
  rw [← sat_vertexZeroClass]
  exact (vertexZeroClass M).isGreatest_inf_sat vertexZeroClass_hereditary h

end Quiver.Kronecker.DoubledRep

namespace Quiver.Kronecker.DoubledRep

open Module

variable {k ι V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (M : DoubledRep k ι V k)

/-- At a wall where the simple `U` at vertex one occurs once, the radical of the class supported
at vertex zero is `subKer = (⋂ ker Aᵢ, 0)`. -/
theorem rad_vertexZeroClass_eq_subKer : (vertexZeroClass M).rad = M.subKer :=
  (vertexZeroClass M).rad_eq_of_isGreatest
    ⟨by simp [subKer], fun _ hz => M.le_subKer (le_bot_iff.mp (by simpa using hz))⟩

variable [Fintype ι] (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [Fintype ι] in
/-- **The top HN step is a radical.** On the side of the wall where the simple `S` at vertex
zero has the higher phase, the first step of the HN filtration `0 ⊂ (⋂ ker Aᵢ, 0) ⊂ M` is the
radical of the class of representations supported at vertex zero: the largest subobject in the
class `add S` of semistable objects of the top phase. -/
theorem hnSHigher_chain_one (h : ⊥ < M.subKer) :
    (M.hnSHigher K h).chain 1 = (vertexZeroClass M).rad := by
  rw [rad_vertexZeroClass_eq_subKer]
  rfl

end Quiver.Kronecker.DoubledRep
