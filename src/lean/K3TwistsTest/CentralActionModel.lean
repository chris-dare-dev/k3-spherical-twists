/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.CentralAction
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# A model of the annihilator obstruction

`CentralAnnihilatorHypotheses` on the derived category of `R`-modules, from
`CentralAnnihilatorHypotheses.ofLinear`: `z` is multiplication by `t ≠ 0`, the letters are the
shift functors, the seed is `R/(t)` and the target is `R`, both in degree zero. The seed is killed
by `t` and the target is not, so the fields are not satisfied by trivial data: the target is a
nonzero object on which `z` is nonzero.

For `R = k[t]/(t²)` the target `R` is a nonsplit extension of `R/(t)` by itself, killed by `t²`
but not by `t`, the shape of the curve with an embedded point at a wall.
-/

open CategoryTheory DerivedCategory

variable {R : Type} [CommRing R] [HasDerivedCategory (ModuleCat R)]

omit [HasDerivedCategory (ModuleCat R)] in
/-- `t` kills `R/(t)`. -/
lemma smul_quotient_span_eq_zero (t : R) (n : R ⧸ Ideal.span {t}) : t • n = 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective n
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right r _ (Ideal.mem_span_singleton_self t)

/-- The model: multiplication by `t ≠ 0`, the shifts as letters, seed `R/(t)`, target `R`. -/
noncomputable def shiftModel (t : R) (ht : t ≠ 0) :
    CentralAnnihilatorHypotheses (DerivedCategory (ModuleCat R)) ℤ :=
  CentralAnnihilatorHypotheses.ofLinear t (fun n ↦ shiftFunctor _ n)
    (ModuleCat.of R (R ⧸ Ideal.span {t})) (ModuleCat.of R R)
    (smul_quotient_span_eq_zero t) ⟨1, by simpa using ht⟩

/-- In the model, every word of shifts keeps the seed killed by `t`. -/
example (t : R) (ht : t ≠ 0) (w : List ℤ) :
    (shiftModel t ht).z.app (((shiftModel t ht).word w).obj (shiftModel t ht).seed) = 0 :=
  (shiftModel t ht).app_word_seed w

/-- In the model, the target is not a factor of any HN filtration of a word applied to the
seed, at any slicing. -/
example (t : R) (ht : t ≠ 0) (w : List ℤ)
    (s : Triangulated.Slicing (DerivedCategory (ModuleCat R)))
    (F : Triangulated.HNFiltration _ s.P (((shiftModel t ht).word w).obj (shiftModel t ht).seed))
    (i : Fin F.n) : IsEmpty ((shiftModel t ht).target ≅ F.factor i) :=
  (shiftModel t ht).not_iso_factor w s F i

/-- Annihilators along a faithful `R`-linear letter: the shift preserves them. -/
example (X : DerivedCategory (ModuleCat R)) (n : ℤ) :
    CatCenter.annihilator (Linear.toCatCenter R _) (X⟦n⟧) =
      CatCenter.annihilator (Linear.toCatCenter R _) X :=
  CatCenter.annihilator_map_eq _
    (fun r ↦ CentralAnnihilatorHypotheses.commutesWithCenter_of_linear r (shiftFunctor _ n)) X
