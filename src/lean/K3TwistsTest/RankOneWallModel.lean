/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WallAlgorithm
import K3TwistsTest.WallStepModel

/-!
# A consistency model of the Picard-rank-one wall inputs

`AlgebraicGeometry.K3.PicardRankOne.RankOneWall` asks that the classes of stable spheres at a wall
be roots and that each phase have at most two sphere types. On the wall step that crosses no wall
(`CategoryTheory.Triangulated.WallStepModel.stayWall`), relative to a pre-stability condition on
which no nonzero semistable object is rigid, there are no stable spheres: the fields hold, and
the wall is anisotropic by `RankOneWall.anisotropic`, and so is the transport step of the trivial
grouping and this wall (`CarrierStep.ofGrouping`), whose Gram matrices are those of the wall. Like
the other wall models it is relative to these variables; an instance from real objects needs the
bounded derived category of a K3 surface of Picard rank one.

Built by `lake test`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Triangulated.WallStepModel

open AlgebraicGeometry.K3.PicardRankOne MukaiVector

universe w u

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {v : K₀ C →+ MukaiVector ℤ}

/-- With no rigid nonzero semistable object, the wall step with no wall has no sphere types. -/
theorem isEmpty_sphereType_stayWall {d : ℤ} (σ : PreStabilityCondition.WithClassMap C v)
    (b : MukaiBudget C) (P : C) (φ₀ : ℝ) (hP : σ.slicing.P φ₀ P) (hP0 : ¬IsZero P)
    (hiso : mukaiForm d (classOf C v P) (classOf C v P) = 0)
    (hrig : ∀ φ M, σ.slicing.P φ M → ¬IsZero M → b.e M ≠ 0) (φ : ℝ) :
    IsEmpty ((stayWall (q := mukaiForm d) σ b P φ₀ hP hP0 hiso).SphereType φ) :=
  ⟨fun x ↦ Quotient.inductionOn x fun S ↦ hrig φ S.1 S.2.1.1 S.2.1.2 S.2.2⟩

/-- **A model of `RankOneWall`**: the wall step with no wall, when no nonzero semistable object is
rigid. -/
theorem rankOneWall_stayWall {d : ℤ} (σ : PreStabilityCondition.WithClassMap C v)
    (b : MukaiBudget C) (P : C) (φ₀ : ℝ) (hP : σ.slicing.P φ₀ P) (hP0 : ¬IsZero P)
    (hiso : mukaiForm d (classOf C v P) (classOf C v P) = 0)
    (hrig : ∀ φ M, σ.slicing.P φ M → ¬IsZero M → b.e M ≠ 0) :
    RankOneWall (stayWall (q := mukaiForm d) σ b P φ₀ hP hP0 hiso) where
  isRoot φ S hS := absurd hS.2 (hrig φ S hS.1.1 hS.1.2)
  finite φ :=
    have := isEmpty_sphereType_stayWall σ b P φ₀ hP hP0 hiso hrig φ
    inferInstance
  card_le_two φ := by
    have := isEmpty_sphereType_stayWall σ b P φ₀ hP hP0 hiso hrig φ
    rw [Nat.card_of_isEmpty]
    omega

/-- The model wall is anisotropic, by the rank-one argument. -/
example {d : ℤ} (hd : 0 < d) (σ : PreStabilityCondition.WithClassMap C v) (b : MukaiBudget C)
    (P : C) (φ₀ : ℝ) (hP : σ.slicing.P φ₀ P) (hP0 : ¬IsZero P)
    (hiso : mukaiForm d (classOf C v P) (classOf C v P) = 0)
    (hrig : ∀ φ M, σ.slicing.P φ M → ¬IsZero M → b.e M ≠ 0) :
    (stayWall (q := mukaiForm d) σ b P φ₀ hP hP0 hiso).Anisotropic :=
  (rankOneWall_stayWall σ b P φ₀ hP hP0 hiso hrig).anisotropic hd

/-- The transport step of the trivial grouping and the model wall is anisotropic. -/
example {d : ℤ} (hd : 0 < d) (σ : PreStabilityCondition.WithClassMap C v) (b : MukaiBudget C)
    (P : C) (φ₀ : ℝ) (hP : σ.slicing.P φ₀ P) (hP0 : ¬IsZero P)
    (hiso : mukaiForm d (classOf C v P) (classOf C v P) = 0)
    (hrig : ∀ φ M, σ.slicing.P φ M → ¬IsZero M → b.e M ≠ 0) :
    (CarrierStep.ofGrouping (t₁ := σ.slicing) (fun _ _ h ↦ h)
      (stayWall (q := mukaiForm d) σ b P φ₀ hP hP0 hiso)).Anisotropic :=
  CarrierStep.anisotropic_ofGrouping _
    ((rankOneWall_stayWall σ b P φ₀ hP hP0 hiso hrig).anisotropic hd)

end CategoryTheory.Triangulated.WallStepModel

end
