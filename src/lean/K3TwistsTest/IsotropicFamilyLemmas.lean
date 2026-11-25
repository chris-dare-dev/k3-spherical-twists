/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.PoincareDuality
import K3Twists.Topology.Spectral.ConstructibleCover
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The isotropic-family lemmas: examples

* **Constructible covers of a spectrum.** `Spec ℤ` is spectral, so a directed cover of it by
  constructible sets has a member equal to it, and any constructible cover has a finite subcover.
* **The degree-two lemma for multiplication.** For the pairing `k × k → k`, `(a, b) ↦ ab`, any
  nonzero linear map `k → X'` is injective; the lemma applies with `φ₁ = φ₁' = id`.

Built by `lake test`.
-/

namespace IsotropicFamilyLemmas

open Set Topology

example (s : ℕ → Set (PrimeSpectrum ℤ)) (hs : ∀ i, IsConstructible (s i))
    (hdir : Directed (· ⊆ ·) s) (hcov : ⋃ i, s i = univ) : ∃ i, s i = univ :=
  exists_eq_univ_of_directed_of_isConstructible s hs hdir hcov

example {ι : Type*} (s : ι → Set (PrimeSpectrum ℤ)) (hs : ∀ i, IsConstructible (s i))
    (hcov : ⋃ i, s i = univ) : ∃ t : Finset ι, ⋃ i ∈ t, s i = univ :=
  exists_finite_subcover_of_isConstructible s hs hcov

example (f : ℚ →ₗ[ℚ] ℚ) (hf : ∀ a b : ℚ, f (a * b) = a * f b) (hf1 : f 1 ≠ 0) :
    Function.Injective f :=
  LinearMap.injective_of_pairing_of_finrank_le_one (fun a b : ℚ ↦ a * b) (fun a b : ℚ ↦ a * f b)
    id id f (fun a b ↦ hf a b) (by simp) ⟨1, one_ne_zero⟩ Function.surjective_id
    fun a ha ↦ by simpa [hf1] using ha 1

end IsotropicFamilyLemmas
