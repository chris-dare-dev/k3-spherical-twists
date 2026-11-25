/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Covers by constructible sets

In a quasi-compact, quasi-sober, prespectral, quasi-separated space (a spectral space, for
instance the underlying space of a quasi-compact quasi-separated scheme), constructible sets are
clopen in the constructible topology, and that topology is quasi-compact (Mathlib's
`compactSpace_withConstructibleTopology`; Stacks 0901). Hence:

* a cover by constructible sets has a finite subcover
  (`Topology.exists_finite_subcover_of_isConstructible`);
* a directed family of constructible sets that covers the space has a member equal to the space
  (`Topology.exists_eq_univ_of_directed_of_isConstructible`).

The second statement turns a stratification by constructible pieces, or an increasing family of
constructible loci, into a finite one: the loci stabilize at the whole space.

## Main results

* `Topology.IsConstructible.isClopen_constructibleTopology`
* `Topology.exists_finite_subcover_of_isConstructible`
* `Topology.exists_eq_univ_of_directed_of_isConstructible`

## Tags

constructible set, constructible topology, spectral space, compactness
-/

open Set

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- The sets that are clopen in the constructible topology, as a Boolean subalgebra. -/
private def clopenConstructible (X : Type*) [TopologicalSpace X] : BooleanSubalgebra (Set X) where
  carrier := {s | IsClopen[constructibleTopology X] s}
  supClosed' _ hs _ ht := @IsClopen.union X (constructibleTopology X) _ _ hs ht
  infClosed' _ hs _ ht := @IsClopen.inter X (constructibleTopology X) _ _ hs ht
  compl_mem' hs := @IsClopen.compl X (constructibleTopology X) _ hs
  bot_mem' := @isClopen_empty X (constructibleTopology X)

/-- In a quasi-compact space, a constructible set is clopen in the constructible topology. -/
theorem IsConstructible.isClopen_constructibleTopology [CompactSpace X] {s : Set X}
    (hs : IsConstructible s) : IsClopen[constructibleTopology X] s := by
  have : BooleanSubalgebra.closure {U : Set X | IsOpen U ∧ IsRetrocompact U} ≤
      clopenConstructible X :=
    BooleanSubalgebra.closure_le.2 fun U ⟨hU, hU'⟩ ↦
      hU'.isCompact.isClopen_constructibleTopology_of_isOpen hU
  exact this hs

private theorem univ_subset_iUnion_preimage {ι : Type*} {s : ι → Set X}
    (hcov : ⋃ i, s i = univ) :
    (univ : Set (WithConstructibleTopology X)) ⊆ ⋃ i, WithTopology.ofTopology ⁻¹' s i := by
  intro y _
  have : WithTopology.ofTopology y ∈ ⋃ i, s i := hcov ▸ mem_univ _
  simpa using this

variable [CompactSpace X] [QuasiSober X] [PrespectralSpace X] [QuasiSeparatedSpace X]

omit [QuasiSober X] [PrespectralSpace X] [QuasiSeparatedSpace X] in
/-- The preimages of constructible sets in `WithConstructibleTopology X` are open. -/
private theorem isOpen_preimage_ofTopology {s : Set X} (hs : IsConstructible s) :
    IsOpen (WithTopology.ofTopology ⁻¹' s : Set (WithConstructibleTopology X)) :=
  WithConstructibleTopology.isOpen_iff.2 hs.isClopen_constructibleTopology.2

/-- **A cover by constructible sets has a finite subcover.** -/
theorem exists_finite_subcover_of_isConstructible {ι : Type*} (s : ι → Set X)
    (hs : ∀ i, IsConstructible (s i)) (hcov : ⋃ i, s i = univ) :
    ∃ t : Finset ι, ⋃ i ∈ t, s i = univ := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
    (fun i ↦ isOpen_preimage_ofTopology (hs i)) (univ_subset_iUnion_preimage hcov)
  refine ⟨t, eq_univ_of_forall fun x ↦ ?_⟩
  simpa using ht (mem_univ (WithTopology.toTopology (constructibleTopology X) x))

/-- **A directed cover by constructible sets has a member equal to the space.** -/
theorem exists_eq_univ_of_directed_of_isConstructible {ι : Type*} [Nonempty ι] (s : ι → Set X)
    (hs : ∀ i, IsConstructible (s i)) (hdir : Directed (· ⊆ ·) s) (hcov : ⋃ i, s i = univ) :
    ∃ i, s i = univ := by
  obtain ⟨i, hi⟩ := isCompact_univ.elim_directed_cover _
    (fun i ↦ isOpen_preimage_ofTopology (hs i)) (univ_subset_iUnion_preimage hcov)
    fun i j ↦ by
      obtain ⟨l, hil, hjl⟩ := hdir i j
      exact ⟨l, preimage_mono hil, preimage_mono hjl⟩
  refine ⟨i, eq_univ_of_forall fun x ↦ ?_⟩
  simpa using hi (mem_univ (WithTopology.toTopology (constructibleTopology X) x))

end Topology
