/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.DT.Inversion
import K3Twists.GroupTheory.Coxeter.RealRoots

/-!
# The BPS interface of a wall block: `Ω = -A(1)` from inputs

Let `S₁, …, S_s` be stable spherical objects of one phase in a `2`-Calabi–Yau category (the wall
simples), with `Ext`-quiver `Q`: `e i j = dim Ext¹(Sᵢ, Sⱼ)` arrows between distinct vertices, no
loops. This file states the inputs that relate the local BPS invariants of the block to the Kac
polynomials of `Q`, and proves the relation from them.

## The Kac data of the quiver (`Quiver.KacData`)

The Kac polynomial `A_α(q)` counts the absolutely indecomposable representations of `Q` of
dimension `α` over a field with `q` elements. Its published properties enter as fields, stated on
the root form `rootForm e` of `Q` (`GroupTheory/Coxeter/RealRoots.lean`):

* `kac_real`: `A_α = 1` on the positive real roots (Kac, *Infinite root systems, representations
  of graphs and invariant theory*, Invent. Math. 56, 1980);
* `kac_eq_zero`: `A_α = 0` when `q(α) ≥ 2`, since an indecomposable of dimension `α` exists only
  when `α` is a root, and roots have `q(α) ≤ 1` (Kac, same paper; Kac, *Infinite dimensional Lie
  algebras*, Chapter 5);
* `kac_reflect`: `A_{sᵢα} = A_α` at a vertex `i` for `α ≠ eᵢ`, the reflection invariance that
  comes from the reflection functors of Bernstein, Gelfand and Ponomarev and the independence of
  `A_α` from the orientation (Kac, Invent. Math. 56, 1980).

For a sign-coherent root form, which covers finite and connected affine type, `kac_real` follows
from `A_{eᵢ} = 1` and `kac_reflect` by descent on the height (`KacData.ofSignCoherent`): the value
on the real roots is **Weyl descent**, not an input.

At an affine wall the quiver is connected of affine type with `l + 1` vertices, and the value at
the imaginary roots enters as one more field (`KacData.IsAffine`): for `δ` a positive vector in
the radical of the root form, `A_{nδ}(q) = q + l` for `n ≥ 1` (Bozec, Schiffmann and Vasserot,
*On the number of points of nilpotent quiver varieties over finite fields*, arXiv:1701.01797,
§1.6.2, from the classification of the indecomposable representations of Euclidean quivers).

## The BPS interface (`Quiver.BPSHypotheses`)

The fields, with their sources:

* `framed_eq_kac`, **Mozgovoy's formula localized to the nilpotent locus**, one numerical field
  for two statements: the nilpotent numerical framed series of the tripled quiver of `Q`, with
  framing `w ≥ 0`, in the geometric variables, is the multiplier `Z_w` with exponents
  `-(w·α) A_α(1)`. The first statement is Mozgovoy's formula for the framed series of a quiver
  (Mozgovoy, arXiv:1107.6044, Theorem 1.1 = Theorem 5.1, Corollary 2.8 and Remark 2.9). The second
  localizes the Behrend-weighted framed series to the nilpotent locus by the `ℂ*`-action,
  adapting the Behrend–Bryan–Szendrői argument. Davison proves a cohomological form for the
  preprojective algebra, with a torus contracting the coarse space onto the nilpotent locus: its
  BPS cohomology over the whole space is dual to that over the nilpotent locus (arXiv:1602.02110,
  Proposition 8.3), and Theorem B there relates the BPS sheaf of the tripled quiver with its
  potential to that of the preprojective algebra. Bozec, Schiffmann and Vasserot show that the
  nilpotent Kac polynomials agree with the Kac polynomials at `q = 1` (arXiv:1701.01797,
  Proposition 1.2). That the numerical Behrend-weighted form follows from these is not checked
  here. Only numerical values agree, so the field is never stated motivically.
* `framed_eq_bps`, **the framed/unframed identity**: that the same series is the multiplier with
  exponents `(w·α) Ω^Q_α` for the nilpotent BPS invariants `Ω^Q` of the tripled quiver (Mozgovoy,
  arXiv:1104.4335, Corollary 4.17 = arXiv:1107.6044, Proposition 2.7, for all modules). Its
  restriction to the nilpotent Serre subcategory is an adaptation of that statement.
* `localModel`, **the CY3 local model**. The local numerical BPS invariants `Ω_α` of the
  wall block, the Behrend-weighted invariants of the objects of class `α` on the threefold
  `X × 𝔸¹` supported over the block, equal the nilpotent BPS invariants of the tripled quiver of
  `Q` with its potential. The field identifies a formal neighbourhood of the polystable point in
  the moduli stack of the threefold with the critical locus of that potential. **This statement
  has no published proof and no human review.** A theorem over it is only as good as the field.
  A `2`-Calabi–Yau form is published: for a collection of simples of this kind, the stack of
  objects filtered by them is the stack of nilpotent representations of the preprojective algebra
  of a half of the `Ext`-quiver (Davison, Hennecart and Schlegel Mejia, arXiv:2212.07668,
  Corollary 7.2).

Only one framing is used, a framing with every entry positive. No identity in other chambers is
assumed (`framedS_injective`).

## Results

* **`Ω = -A(1)` from the fields** (`BPSHypotheses.omega_eq`, from all four statements), and on the
  quiver side `Ω^Q = -A(1)` (`bpsQ_eq`, without the CY3 local model). It is the injectivity of
  the multiplier at one framing. The sign is that of `Combinatorics/DT/FramedMultiplier.lean`:
  the exponent of `(1 - x^α)` is `(p·α) Ω_α`, with `Ω_α = -A_α(1)` for a quiver.
* From the Kac data, at the level of indices:
  * the simple objects have `Ω = -1` (`omega_single`);
  * mutation at a vertex leaves `Ω` invariant, `Ω_{sᵢα} = Ω_α` (`omega_reflect`);
  * `Ω_α = 0` when `q(α) ≥ 2` (`omega_eq_zero`);
  * at the imaginary roots of a connected affine quiver with `l + 1` vertices,
    `Ω_{nδ} = -(l + 1)` (`omega_eq_neg_card_of_isAffine`; on the quiver side, without the CY3
    local model, `bpsQ_eq_neg_card_of_isAffine`);
  * **Weyl descent**: `Ω = -1` on every positive real root (`omega_eq_neg_one_of_isRealRoot`), in
    particular on the classes of the new simple objects along a Weyl gallery, the prefix roots of
    a word (`omega_eq_neg_one_of_mem_stdPrefixRoots`).
* **The interface says exactly `Ω = -A(1)`** (`exists_iff`): for given Kac data and `Ω`, the
  fields can be met iff `Ω = -A(1)` on the positive classes. The content therefore sits in the
  fields and in Kac data tied to the quiver, as for any interface of this kind.

The theorems about `Ω` use the CY3 local model `localModel` and say so in their docstrings.
There is no geometric instance: the framed moduli of the tripled quiver, the Behrend function and
the moduli of objects of the `2`-Calabi–Yau category are not in the library. The instance from a
quiver is the curve wall of the elliptic K3 surface
(`AlgebraicGeometry/Surface/K3/EllipticWithSection/BPS.lean`), whose `Ext`-quiver is computed from
the classes of its simples and whose Kac data are proved from its Tits form.
-/

open MvPowerSeries MvPowerSeries.FramedMultiplier CoxeterMatrix

namespace Quiver

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The dimension vector of a class in `ℤ^σ`. -/
def dimVec (α : σ →₀ ℕ) : σ → ℤ :=
  fun i => α i

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem dimVec_apply (α : σ →₀ ℕ) (i : σ) : dimVec α i = α i :=
  rfl

omit [Fintype σ] in
theorem dimVec_single (i : σ) : dimVec (Finsupp.single i 1) = stdRoot i := by
  ext j
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

omit [Fintype σ] [DecidableEq σ] in
theorem isPositiveVector_dimVec (α : Pos σ) : IsPositiveVector (dimVec α.1) :=
  ⟨fun i => Int.natCast_nonneg _, fun h => α.2 (Finsupp.ext fun i => by
    have := congrFun h i
    simpa using this)⟩

omit [Fintype σ] [DecidableEq σ] in
theorem dimVec_injective : Function.Injective (dimVec (σ := σ)) := fun α β h =>
  Finsupp.ext fun i => by simpa using congrFun h i

/-- The class of a nonnegative vector. -/
noncomputable def ofVec (v : σ → ℤ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (v i).toNat

omit [DecidableEq σ] in
theorem dimVec_ofVec {v : σ → ℤ} (hv : ∀ i, 0 ≤ v i) : dimVec (ofVec v) = v := by
  ext i
  simp [ofVec, hv i]

omit [DecidableEq σ] in
theorem ofVec_ne_zero {v : σ → ℤ} (hv : IsPositiveVector v) : ofVec v ≠ 0 := by
  intro h
  apply hv.2
  rw [← dimVec_ofVec hv.1, h]
  rfl

variable (e : σ → σ → ℕ)

/-- **The Kac data of a loopless quiver.** The Kac polynomials `A_α(q)` at the dimension vectors
`α ∈ ℤ^σ`, with the published properties stated on the root form of the quiver: `A = 1` on the
positive real roots, `A = 0` where `q ≥ 2`, and invariance under the reflection at a vertex. See
the module docstring for the sources. -/
structure KacData where
  /-- The Kac polynomials `A_α(q)`. -/
  kac : (σ → ℤ) → Polynomial ℤ
  /-- `A_α = 1` on the positive real roots (Kac, Invent. Math. 56, 1980). -/
  kac_real : ∀ v, IsRealRoot e v → IsPositiveVector v → kac v = 1
  /-- `A_α = 0` when `q(α) ≥ 2`, that is `⟨α, α⟩ ≤ -4`: `α` is not a root. -/
  kac_eq_zero : ∀ v, IsPositiveVector v → rootForm e v v ≤ -4 → kac v = 0
  /-- `A_{sᵢα} = A_α` for `α ≠ eᵢ` (reflection functors and independence of the orientation). -/
  kac_reflect : ∀ i v, IsPositiveVector v → v ≠ stdRoot i → IsPositiveVector (stdReflect e i v) →
    kac (stdReflect e i v) = kac v

/-- **Weyl descent for the Kac data.** For a sign-coherent root form, as in finite and connected
affine type, the value `A = 1` on the real roots follows from `A_{eᵢ} = 1` and the reflection
invariance. -/
def KacData.ofSignCoherent (he : ∀ i j, e i j = e j i) (hsc : IsSignCoherent e)
    (kac : (σ → ℤ) → Polynomial ℤ) (kac_simple : ∀ i, kac (stdRoot i) = 1)
    (kac_eq_zero : ∀ v, IsPositiveVector v → rootForm e v v ≤ -4 → kac v = 0)
    (kac_reflect : ∀ i v, IsPositiveVector v → v ≠ stdRoot i →
      IsPositiveVector (stdReflect e i v) → kac (stdReflect e i v) = kac v) : KacData e where
  kac := kac
  kac_real v hv hpos := by
    obtain ⟨j, hj, -⟩ := exists_eq_stdRoot_of_reflect_invariant e he hsc kac kac_reflect v hpos
      (hv.rootForm_self e he)
    rw [hj, kac_simple]
  kac_eq_zero := kac_eq_zero
  kac_reflect := kac_reflect

/-- **The Kac polynomials at the imaginary roots of a connected affine quiver.** The quiver is
connected (`rootMatrix e` is indecomposable), its root form is negative semidefinite, and `δ` is a
positive vector in the radical of the root form; so the quiver has affine type and `δ` is a
positive multiple of its minimal positive imaginary root. The field `kac_smul` is the published
value of the Kac polynomial at the imaginary roots, `A_{nδ}(q) = q + l` for `n ≥ 1`, where
`l + 1 = |σ|` is the number of vertices (Bozec, Schiffmann and Vasserot, *On the number of points
of nilpotent quiver varieties over finite fields*, arXiv:1701.01797, §1.6.2, which derives it
from the classification of the indecomposable representations of Euclidean quivers). -/
structure KacData.IsAffine {e : σ → σ → ℕ} (K : KacData e) (δ : σ → ℤ) : Prop where
  /-- The quiver is connected. -/
  isIndecomposable : (rootMatrix e).IsIndecomposable
  /-- The root form is negative semidefinite. -/
  rootForm_self_nonpos : ∀ v, rootForm e v v ≤ 0
  /-- `δ` is a positive vector. -/
  isPositiveVector : IsPositiveVector δ
  /-- `δ` lies in the radical of the root form. -/
  rootForm_eq_zero : ∀ v, rootForm e δ v = 0
  /-- **`A_{nδ}(q) = q + l`** for `n ≥ 1`, with `l + 1` vertices (Bozec, Schiffmann and
  Vasserot, arXiv:1701.01797, §1.6.2). -/
  kac_smul : ∀ n : ℕ, 0 < n →
    K.kac ((n : ℤ) • δ) = Polynomial.X + Polynomial.C ((Fintype.card σ : ℤ) - 1)

/-- At `q = 1` the Kac polynomial of an imaginary root `nδ` of a connected affine quiver is the
number `l + 1` of vertices. -/
theorem KacData.IsAffine.eval_one_kac_smul {e : σ → σ → ℕ} {K : KacData e} {δ : σ → ℤ}
    (h : K.IsAffine δ) {n : ℕ} (hn : 0 < n) :
    (K.kac ((n : ℤ) • δ)).eval 1 = Fintype.card σ := by
  rw [h.kac_smul n hn]
  simp

/-- **The BPS interface of a wall block** with `Ext`-quiver `e`: the Kac data of the quiver, the
nilpotent BPS invariants `bpsQ` of its tripled quiver, the framed series `framed w` for each
framing, the local BPS invariants `Ω` of the block, Mozgovoy's formula localized to the nilpotent
locus, the framed/unframed identity and the CY3 local model. See the module docstring for the
sources; the CY3 local model `localModel` has no published proof and no human review. -/
structure BPSHypotheses extends KacData e where
  /-- The nilpotent numerical BPS invariants of the tripled quiver. -/
  bpsQ : (σ →₀ ℕ) → ℤ
  /-- The nilpotent numerical framed series of the tripled quiver, in the geometric variables. -/
  framed : (σ → ℕ) → MvPowerSeries σ ℤ
  /-- **Mozgovoy's formula, localized to the nilpotent locus.** -/
  framed_eq_kac : ∀ w, framed w = Z w fun α => -(kac (dimVec α)).eval 1
  /-- **The framed/unframed identity.** -/
  framed_eq_bps : ∀ w, framed w = Z w bpsQ
  /-- The local numerical BPS invariants of the wall block. -/
  Ω : (σ →₀ ℕ) → ℤ
  /-- **The CY3 local model**: the local BPS invariants of the wall block are those of the
  tripled quiver with its potential, through the identification of a formal neighbourhood of the
  polystable point of the moduli stack of `X × 𝔸¹` with the critical locus of the potential.
  **This statement has no published proof and no human review.** -/
  localModel : ∀ α, α ≠ 0 → Ω α = bpsQ α

namespace BPSHypotheses

variable {e} (H : BPSHypotheses e)

/-- **`Ω^Q = -A(1)` on the quiver side**, from `framed_eq_kac` and `framed_eq_bps` at the framing
`w = (1, …, 1)`: the multiplier is injective at a framing with every entry positive. -/
theorem bpsQ_eq (α : Pos σ) : H.bpsQ α.1 = -(H.kac (dimVec α.1)).eval 1 := by
  have h : Z (R := ℤ) (fun _ => 1) H.bpsQ =
      Z (fun _ => 1) fun α => -(H.kac (dimVec α)).eval 1 :=
    (H.framed_eq_bps _).symm.trans (H.framed_eq_kac _)
  have h' := congrArg (rescale (eps (R := ℤ) fun _ => 1)) h
  simp only [Z, rescale_eps_involutive] at h'
  exact framedS_injective (fun α => (pair_pos (fun _ => by norm_num) α).ne') h' α

/-- **`Ω = -A(1)`.** The local BPS invariants of the wall block are minus the Kac
polynomials of its `Ext`-quiver at `q = 1`, in every degree. Uses the CY3 local model
`localModel`, which has no published proof and no human review. -/
theorem omega_eq (α : Pos σ) : H.Ω α.1 = -(H.kac (dimVec α.1)).eval 1 := by
  rw [H.localModel α.1 α.2, H.bpsQ_eq α]

/-- **Weyl descent: `Ω = -1` on every positive real root.** Uses the CY3 local model
`localModel`. -/
theorem omega_eq_neg_one_of_isRealRoot (α : Pos σ) (h : IsRealRoot e (dimVec α.1)) :
    H.Ω α.1 = -1 := by
  rw [H.omega_eq α, H.kac_real _ h (isPositiveVector_dimVec α)]
  simp

/-- **The simple objects have `Ω = -1`.** Uses the CY3 local model `localModel`. -/
theorem omega_single (i : σ) : H.Ω (Finsupp.single i 1) = -1 := by
  have := H.omega_eq_neg_one_of_isRealRoot ⟨Finsupp.single i 1, by simp⟩
    (by rw [dimVec_single]; exact isRealRoot_stdRoot e i)
  exact this

/-- **`Ω_α = 0` when `q(α) ≥ 2`.** Uses the CY3 local model `localModel`. -/
theorem omega_eq_zero (α : Pos σ) (h : rootForm e (dimVec α.1) (dimVec α.1) ≤ -4) :
    H.Ω α.1 = 0 := by
  rw [H.omega_eq α, H.kac_eq_zero _ (isPositiveVector_dimVec α) h]
  simp

/-- **`Ω^Q_{nδ} = -(l + 1)` on the quiver side**: at the imaginary roots `nδ`, `n ≥ 1`, of a
connected affine quiver with `l + 1` vertices, from `bpsQ_eq` and the Kac value `q + l`, without
the CY3 local model. -/
theorem bpsQ_eq_neg_card_of_isAffine {δ : σ → ℤ} (hA : H.toKacData.IsAffine δ) (α : Pos σ)
    {n : ℕ} (hn : 0 < n) (hα : dimVec α.1 = (n : ℤ) • δ) :
    H.bpsQ α.1 = -(Fintype.card σ : ℤ) := by
  rw [H.bpsQ_eq α, hα, hA.eval_one_kac_smul hn]

/-- **`Ω_{nδ} = -(l + 1)`** at the imaginary roots `nδ`, `n ≥ 1`, of a connected affine quiver
with `l + 1` vertices. At an affine ADE wall `l + 1` is the Euler characteristic of the
exceptional fibre, a tree of `l` smooth rational curves; at the curve wall it is `χ(ℙ¹) = 2`.
Uses the CY3 local model `localModel`. -/
theorem omega_eq_neg_card_of_isAffine {δ : σ → ℤ} (hA : H.toKacData.IsAffine δ) (α : Pos σ)
    {n : ℕ} (hn : 0 < n) (hα : dimVec α.1 = (n : ℤ) • δ) :
    H.Ω α.1 = -(Fintype.card σ : ℤ) := by
  rw [H.omega_eq α, hα, hA.eval_one_kac_smul hn]

/-- **Mutation at a vertex leaves `Ω` invariant**: `Ω_{sᵢα} = Ω_α` for a positive class `α ≠ eᵢ`
whose reflection `β = sᵢα` is positive. Uses the CY3 local model `localModel`. -/
theorem omega_reflect {i : σ} (α β : Pos σ) (hne : α.1 ≠ Finsupp.single i 1)
    (hβ : dimVec β.1 = stdReflect e i (dimVec α.1)) : H.Ω β.1 = H.Ω α.1 := by
  have hne' : dimVec α.1 ≠ stdRoot i := fun h =>
    hne (dimVec_injective (h.trans (dimVec_single i).symm))
  have hpos : IsPositiveVector (stdReflect e i (dimVec α.1)) := hβ ▸ isPositiveVector_dimVec β
  rw [H.omega_eq β, H.omega_eq α, hβ, H.kac_reflect i _ (isPositiveVector_dimVec α) hne' hpos]

/-- **Weyl descent along a Weyl gallery**: the prefix roots of any word that are positive
vectors, in particular the classes of the new simple objects along a gallery of a root-positive
word, have `Ω = -1`. Uses the CY3 local model `localModel`. -/
theorem omega_eq_neg_one_of_mem_stdPrefixRoots {ω : List σ} {v : σ → ℤ}
    (hv : v ∈ stdPrefixRoots e ω) (hpos : IsPositiveVector v) :
    H.Ω (ofVec v) = -1 := by
  have := H.omega_eq_neg_one_of_isRealRoot ⟨ofVec v, ofVec_ne_zero hpos⟩
    (by rw [dimVec_ofVec hpos.1]; exact isRealRoot_of_mem_stdPrefixRoots e hv)
  exact this

/-- For a root-positive word, every prefix root is a positive vector, so `Ω = -1` on all of
them. Uses the CY3 local model `localModel`. -/
theorem omega_eq_neg_one_of_isRootPositive {ω : List σ}
    (hω : BilinearForm.IsRootPositive (rootForm e) stdRoot ω) {v : σ → ℤ}
    (hv : v ∈ stdPrefixRoots e ω) : H.Ω (ofVec v) = -1 := by
  refine H.omega_eq_neg_one_of_mem_stdPrefixRoots hv ?_
  rw [isPositiveVector_iff_mem_positiveCone]
  exact hω v (by rw [prefixRoots_rootForm]; exact hv)

end BPSHypotheses

/-- **The interface says exactly `Ω = -A(1)`.** For given Kac data and local invariants `Ω`, the
fields of `BPSHypotheses` can be met iff `Ω = -A(1)` on the positive classes. -/
theorem BPSHypotheses.exists_iff (K : KacData e) (Ω : (σ →₀ ℕ) → ℤ) :
    (∃ H : BPSHypotheses e, H.toKacData = K ∧ H.Ω = Ω) ↔
      ∀ α : Pos σ, Ω α.1 = -(K.kac (dimVec α.1)).eval 1 := by
  constructor
  · rintro ⟨H, rfl, rfl⟩ α
    exact H.omega_eq α
  · intro h
    refine ⟨{ toKacData := K
              bpsQ := Ω
              framed := fun w => Z w Ω
              framed_eq_kac := fun w => ?_
              framed_eq_bps := fun _ => rfl
              Ω := Ω
              localModel := fun _ _ => rfl }, rfl, rfl⟩
    unfold Z framedS
    congr 1
    exact S_congr fun α => by simp [h α]

end Quiver
