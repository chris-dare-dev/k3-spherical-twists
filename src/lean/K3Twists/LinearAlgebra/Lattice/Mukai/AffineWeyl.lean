/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.Eichler
import K3Twists.LinearAlgebra.Matrix.ZMatrix.Isotropic
import K3Twists.LinearAlgebra.Matrix.ZMatrix.SignCoherence

/-!
# Affine simple roots of an exceptional fibre and the fundamental alcove

Let `N` be a lattice with a bilinear form `b` (on a K3 surface, `NS(X)` with the intersection
form) and `MukaiLattice ℤ N` its Mukai lattice, with `⟨(r, c, s), (r', c', s')⟩ = b(c, c') - rs' -
r's`. A contraction of `(-2)`-curves has one **connected exceptional fibre** per singular point:
curves `Cᵢ` with `Cᵢ² = -2`, meeting nonnegatively, spanning a negative definite lattice, with a
**fundamental cycle** `Θ = Σ zᵢ Cᵢ` (Artin, *On isolated rational singularities of surfaces*, 1966):
`zᵢ ≥ 0`, `Θ² = -2` and `Θ·Cᵢ ≤ 0` for every `i`. The structure `Mukai.FundamentalCycle` takes
these as fields, with connectedness of the configuration; full support `zᵢ > 0` follows
(`FundamentalCycle.mult_pos`).

## Affine simple roots

The **affine simple roots** of the fibre are the classes of the simple objects of the wall
where the fibre is contracted:

```
α₀ = v(𝒪_Θ) = (0, Θ, 1),   αᵢ = v(𝒪_{Cᵢ}(-1)[1]) = (0, -Cᵢ, 0),
```

(`FundamentalCycle.affineRoot`, indexed by `Option ι`, with `none` for `α₀`), and
`α₀ + Σ zᵢ αᵢ = (0, 0, 1) = δ`, the class of a point (`sum_nullMult_smul_affineRoot`). Their wall
matrix `G = -Gram(α₀, …, α_l)` is the extended Dynkin matrix of the fibre
(`FundamentalCycle.affineCartan`): symmetric, diagonal `2`, a Z-matrix, with null vector
`(1, z)`. Tensoring with a line bundle moves the affine roots along `δ`:
`⊗𝒪(L) αᵢ = αᵢ - (Cᵢ·L) δ` and `⊗𝒪(L) α₀ = α₀ + (Θ·L) δ` (`tensorLine_affineRoot_some`,
`tensorLine_affineRoot_none`), so `⊗𝒪(L)` fixes every affine root exactly when `L ⊥ Cᵢ` for all
`i` (`tensorLine_fixes_affineRoot_iff`).

## The fundamental-alcove theorem

`xᵀGx = -b(c, c)` for `Σ xₖ αₖ = (0, c, x₀)` (`dotProduct_affineCartan`), so negative
definiteness of the fibre makes `G` positive semidefinite with isotropic vectors `ℤ(1, z)`. These
are the hypotheses of sign coherence (`Matrix.IsZMatrix.signCoherent`), so:

* **(b) roots are positive or negative.** A rank-zero root `(0, c, s)` with `c = Σ dᵢ Cᵢ` has
  coordinates `(s, s zᵢ - dᵢ)` in the affine simple roots, all `≥ 0` or all `≤ 0`
  (`signCoherent_affineCoord`). In particular every root `c` of the fibre lattice has
  `-z ≤ d ≤ z` coefficientwise, so `Θ` is its highest root (`neg_mult_le_of_root`,
  `le_mult_of_root`), and its coefficients are all `≥ 0` or all `≤ 0`
  (`nonneg_or_nonpos_of_root`). No highest-root API and no Coxeter-group positivity are used.
* **(c) the alcove.** For `β : N →+ ℝ`, put `Z(r, c, s) = β(c) - s` (`fibreCharge`): for the
  central charge `Z = ⟨exp(β + iωH), ·⟩` and `H·c = 0`, this is `Z(0, c, s)`. The **fundamental
  alcove** is `β·Cᵢ > 0` for all `i` and `β·Θ < 1` (`IsInFundamentalAlcove`). It holds iff
  `Z < 0` on every positive root of the fibre (`isInFundamentalAlcove_iff`), and then `Z ≠ 0`
  on every rank-zero root `(0, c, s)` with `c ∈ ⊕ ℤCᵢ` (`fibreCharge_ne_zero`). On the boundary
  of the closed alcove some affine simple root lies in `ker Z`
  (`exists_fibreCharge_affineRoot_eq_zero`).
* **The Riemann–Roch membership field.** On a K3 surface with a polarization `H` pulled back from
  the contraction, every `(-2)`-class of `H^⊥ ∩ NS` is effective or anti-effective by
  Riemann–Roch, and it is then supported on the contracted curves. With one contracted fibre this
  is the field `FundamentalCycle.RiemannRochMembership`, and the alcove makes `Z ≠ 0` on every
  rank-zero root orthogonal to `H` (`fibreCharge_ne_zero_of_riemannRochMembership`). Over a
  lattice it is a real hypothesis: an overlattice can carry roots that are not in `⊕ ℤCᵢ`
  (`A₁⁸ ⊂ E₈`).

The converse of "alcove ⇒ no root in `ker Z`" fails: for `A₂` with `β·Cᵢ = 3/4` no root lies in
`ker Z` but `Z(α₀) = 1/2 > 0` (a test).

## Conventions

The Mukai form is `b(c, c') - rs' - r's`, the Eichler transvection
`E(e, x, q)(v) = v + ⟨v, e⟩x - ⟨v, x⟩e - q⟨v, e⟩e`, and `⊗𝒪(D) = E(pt, (0, -D, 0), D²/2)`
(`Mukai.tensorLine_eq_eichler`). The wall matrix is the negated Gram matrix.

## References

* M. Artin, *On isolated rational singularities of surfaces*, Amer. J. Math. 88 (1966).
* V. G. Kac, *Infinite dimensional Lie algebras*, Ch. 4–6.
* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §1–2.
-/

open Matrix

namespace Mukai

variable {N : Type*} [AddCommGroup N]

variable (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ) in
/-- **A connected exceptional fibre with its fundamental cycle**, as lattice data: curves
`Cᵢ ∈ N` with `Cᵢ² = -2`, meeting nonnegatively, connected, spanning a negative definite lattice,
and multiplicities `zᵢ ≥ 0` with `Θ = Σ zᵢ Cᵢ`, `Θ² = -2` and `Θ·Cᵢ ≤ 0`.

On a K3 surface these are the irreducible components of the exceptional fibre of a contraction
over one rational double point, and `Θ` is Artin's fundamental cycle. -/
structure FundamentalCycle (ι : Type*) [Fintype ι] where
  /-- The curves `Cᵢ`. -/
  curve : ι → N
  /-- The multiplicities `zᵢ` of the fundamental cycle `Θ = Σ zᵢ Cᵢ`. -/
  mult : ι → ℤ
  /-- `Cᵢ² = -2`. -/
  curve_self : ∀ i, b (curve i) (curve i) = -2
  /-- Distinct curves meet nonnegatively. -/
  curve_nonneg : ∀ i j, i ≠ j → 0 ≤ b (curve i) (curve j)
  /-- The curves span a negative definite lattice. -/
  negDef : ∀ d : ι → ℤ, d ≠ 0 → b (∑ i, d i • curve i) (∑ i, d i • curve i) < 0
  /-- The fibre is connected. -/
  connected : (Matrix.of fun i j => b (curve i) (curve j)).IsIndecomposable
  /-- `Θ ≥ 0`. -/
  mult_nonneg : ∀ i, 0 ≤ mult i
  /-- `Θ² = -2`. -/
  cycle_self : b (∑ i, mult i • curve i) (∑ i, mult i • curve i) = -2
  /-- `Θ·Cᵢ ≤ 0`. -/
  cycle_curve_nonpos : ∀ i, b (∑ j, mult j • curve j) (curve i) ≤ 0

namespace FundamentalCycle

variable {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {ι : Type*} [Fintype ι] (F : FundamentalCycle b ι)

/-! ### The fibre lattice -/

/-- `d ↦ Σ dᵢ Cᵢ`, the classes supported on the fibre. -/
def combination : (ι → ℤ) →ₗ[ℤ] N :=
  Fintype.linearCombination ℤ F.curve

theorem combination_apply (d : ι → ℤ) : F.combination d = ∑ i, d i • F.curve i :=
  rfl

/-- The lattice `⊕ ℤCᵢ` of classes supported on the fibre. -/
def rootLattice : Submodule ℤ N :=
  LinearMap.range F.combination

theorem mem_rootLattice {c : N} : c ∈ F.rootLattice ↔ ∃ d : ι → ℤ, ∑ i, d i • F.curve i = c :=
  Iff.rfl

/-- The fundamental cycle `Θ = Σ zᵢ Cᵢ`. -/
def cycle : N :=
  ∑ i, F.mult i • F.curve i

theorem cycle_self' : b F.cycle F.cycle = -2 :=
  F.cycle_self

theorem cycle_curve_nonpos' (i : ι) : b F.cycle (F.curve i) ≤ 0 :=
  F.cycle_curve_nonpos i

/-- `Θ·L = Σ zᵢ (Cᵢ·L)`. -/
theorem cycle_apply (L : N) : b F.cycle L = ∑ i, F.mult i * b (F.curve i) L := by
  simp [cycle, map_sum, LinearMap.sum_apply, LinearMap.smul_apply]

/-- The form is nonpositive on classes supported on the fibre. -/
theorem self_combination_nonpos (d : ι → ℤ) :
    b (∑ i, d i • F.curve i) (∑ i, d i • F.curve i) ≤ 0 := by
  by_cases hd : d = 0
  · simp [hd]
  · exact (F.negDef d hd).le

/-- A class supported on the fibre with square zero is zero. -/
theorem eq_zero_of_self_combination {d : ι → ℤ}
    (hd : b (∑ i, d i • F.curve i) (∑ i, d i • F.curve i) = 0) : d = 0 := by
  by_contra h
  exact (F.negDef d h).ne hd

/-- **Full support.** Every curve of a connected fibre occurs in its fundamental cycle:
`zᵢ > 0`. A curve `Cⱼ` with `zⱼ = 0` that meets a curve of the support has `Θ·Cⱼ > 0`. -/
theorem mult_pos (i : ι) : 0 < F.mult i := by
  -- some multiplicity is positive, since `Θ² ≠ 0`
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, 0 < F.mult i₀ := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have h0 : F.mult = 0 := funext fun i => le_antisymm (h i) (F.mult_nonneg i)
    have := F.cycle_self
    simp [h0] at this
  have step : ∀ a c, b (F.curve a) (F.curve c) ≠ 0 → 0 < F.mult a → 0 < F.mult c := by
    intro a c hac ha
    rcases eq_or_ne a c with rfl | hne
    · exact ha
    by_contra hc
    have hc0 : F.mult c = 0 := le_antisymm (not_lt.mp hc) (F.mult_nonneg c)
    have hpos : 0 < b (F.curve a) (F.curve c) :=
      lt_of_le_of_ne (F.curve_nonneg a c hne) (Ne.symm hac)
    have hsum : F.mult a * b (F.curve a) (F.curve c) ≤
        ∑ k, F.mult k * b (F.curve k) (F.curve c) := by
      refine Finset.single_le_sum (f := fun k => F.mult k * b (F.curve k) (F.curve c))
        (fun k _ => ?_) (Finset.mem_univ a)
      rcases eq_or_ne k c with rfl | hkc
      · simp [hc0]
      · exact mul_nonneg (F.mult_nonneg k) (F.curve_nonneg k c hkc)
    have := F.cycle_curve_nonpos' c
    rw [cycle_apply] at this
    nlinarith
  have hreach := (isIndecomposable_iff_reflTransGen _).mp F.connected i₀ i
  induction hreach with
  | refl => exact hi₀
  | tail _ hst ih => exact step _ _ (by simpa using hst) ih

/-! ### Affine simple roots -/

/-- **The affine simple roots**: `α₀ = (0, Θ, 1)`, the class of `𝒪_Θ`, at `none`, and
`αᵢ = (0, -Cᵢ, 0)`, the class of `𝒪_{Cᵢ}(-1)[1]`, at `some i`. -/
def affineRoot : Option ι → MukaiLattice ℤ N
  | none => (0, F.cycle, 1)
  | some i => (0, -F.curve i, 0)

@[simp] theorem affineRoot_none : F.affineRoot none = (0, F.cycle, 1) := rfl

@[simp] theorem affineRoot_some (i : ι) : F.affineRoot (some i) = (0, -F.curve i, 0) := rfl

/-- The marks of the extended diagram: `1` at `α₀`, `zᵢ` at `αᵢ`. -/
def nullMult : Option ι → ℤ
  | none => 1
  | some i => F.mult i

@[simp] theorem nullMult_none : F.nullMult none = 1 := rfl

@[simp] theorem nullMult_some (i : ι) : F.nullMult (some i) = F.mult i := rfl

theorem nullMult_pos (k : Option ι) : 0 < F.nullMult k := by
  cases k with
  | none => exact one_pos
  | some i => exact F.mult_pos i

/-- **Coordinates in the affine simple roots.** `Σ xₖ αₖ = (0, Σ (x₀ zᵢ - xᵢ) Cᵢ, x₀)`. -/
theorem sum_smul_affineRoot (x : Option ι → ℤ) :
    ∑ k, x k • F.affineRoot k =
      (0, ∑ i, (x none * F.mult i - x (some i)) • F.curve i, x none) := by
  rw [Fintype.sum_option]
  ext
  · simp [Prod.fst_sum]
  · simp only [affineRoot_none, affineRoot_some, Prod.smul_mk, Prod.snd_add, Prod.fst_add,
      Prod.snd_sum, Prod.fst_sum, cycle, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    module
  · simp [Prod.snd_sum]

/-- **The null root**: `α₀ + Σ zᵢ αᵢ = (0, 0, 1)`, the class `δ` of a point. -/
theorem sum_nullMult_smul_affineRoot :
    ∑ k, F.nullMult k • F.affineRoot k = corankUnit := by
  rw [sum_smul_affineRoot]
  simp [corankUnit]

/-- The Mukai form on rank-zero classes is the form of the fibre. -/
theorem mukaiForm_rankZero (c c' : N) (s s' : ℤ) :
    mukaiForm b ((0, c, s) : MukaiLattice ℤ N) (0, c', s') = b c c' := by
  simp

theorem mukaiForm_affineRoot_corankUnit (k : Option ι) :
    mukaiForm b (F.affineRoot k) corankUnit = 0 := by
  cases k <;> simp [corankUnit]

/-- Each affine simple root is spherical. -/
theorem isSpherical_affineRoot (k : Option ι) : IsSpherical b (F.affineRoot k) := by
  cases k with
  | none => simpa [IsSpherical] using F.cycle_self'
  | some i => simpa [IsSpherical] using F.curve_self i

/-! ### Line bundles on the affine roots -/

/-- `⊗𝒪(L) αᵢ = αᵢ - (Cᵢ·L) δ`, for every value of the parameter `q`. -/
theorem tensorLine_affineRoot_some (L : N) (q : ℤ) (i : ι) :
    tensorLine b L q (F.affineRoot (some i)) =
      F.affineRoot (some i) - b (F.curve i) L • corankUnit := by
  ext <;> simp [corankUnit]

/-- `⊗𝒪(L) α₀ = α₀ + (Θ·L) δ`. -/
theorem tensorLine_affineRoot_none (L : N) (q : ℤ) :
    tensorLine b L q (F.affineRoot none) = F.affineRoot none + b F.cycle L • corankUnit := by
  ext <;> simp [corankUnit]

/-- **The kernel of the action on affine roots.** `⊗𝒪(L)` fixes every affine simple root exactly
when `L ⊥ Cᵢ` for every `i`. -/
theorem tensorLine_fixes_affineRoot_iff (L : N) (q : ℤ) :
    (∀ k, tensorLine b L q (F.affineRoot k) = F.affineRoot k) ↔ ∀ i, b (F.curve i) L = 0 := by
  constructor
  · intro h i
    have := congrArg (fun v : MukaiLattice ℤ N => v.2.2) (h (some i))
    simpa using this
  · intro h k
    cases k with
    | none => simp [cycle_apply, h]
    | some i => simp [h]

/-! ### The extended Dynkin matrix -/

/-- **The extended Dynkin matrix** of the fibre: the wall matrix `-⟨αₖ, αₗ⟩` of the affine simple
roots. -/
def affineCartan : Matrix (Option ι) (Option ι) ℤ :=
  (mukaiForm b).wallMatrix F.affineRoot

@[simp] theorem affineCartan_none_none : F.affineCartan none none = 2 := by
  simp [affineCartan, F.cycle_self']

@[simp] theorem affineCartan_some_some (i j : ι) :
    F.affineCartan (some i) (some j) = -b (F.curve i) (F.curve j) := by
  simp [affineCartan]

@[simp] theorem affineCartan_none_some (i : ι) :
    F.affineCartan none (some i) = b F.cycle (F.curve i) := by
  simp [affineCartan]

@[simp] theorem affineCartan_some_none (i : ι) :
    F.affineCartan (some i) none = b (F.curve i) F.cycle := by
  simp [affineCartan]

theorem affineCartan_diag (k : Option ι) : F.affineCartan k k = 2 := by
  cases k with
  | none => exact F.affineCartan_none_none
  | some i => simp [F.curve_self i]

theorem affineCartan_isSymm (hb : ∀ x y, b x y = b y x) : F.affineCartan.IsSymm :=
  LinearMap.BilinForm.wallMatrix_isSymm (mukaiForm_comm b hb) _

theorem affineCartan_isZMatrix (hb : ∀ x y, b x y = b y x) : F.affineCartan.IsZMatrix := by
  intro k l hkl
  cases k with
  | none =>
    cases l with
    | none => exact absurd rfl hkl
    | some j => simpa using F.cycle_curve_nonpos' j
  | some i =>
    cases l with
    | none => simpa [hb (F.curve i)] using F.cycle_curve_nonpos' i
    | some j =>
      simpa using F.curve_nonneg i j fun h => hkl (by rw [h])

/-- `G (1, z) = 0`: the marks are a null vector. -/
theorem affineCartan_mulVec_nullMult : F.affineCartan *ᵥ F.nullMult = 0 := by
  ext k
  have h := F.mukaiForm_affineRoot_corankUnit k
  rw [← F.sum_nullMult_smul_affineRoot, map_sum] at h
  simp only [map_smul, smul_eq_mul] at h
  simp only [mulVec, dotProduct, affineCartan, LinearMap.BilinForm.wallMatrix_apply, Pi.zero_apply]
  rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← h]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **The Tits identity for the affine roots.** `xᵀGx = -b(c, c)` for `c = Σ (x₀ zᵢ - xᵢ) Cᵢ`, the
middle coordinate of `Σ xₖ αₖ`. -/
theorem dotProduct_affineCartan (x : Option ι → ℤ) :
    x ⬝ᵥ F.affineCartan *ᵥ x =
      -b (∑ i, (x none * F.mult i - x (some i)) • F.curve i)
        (∑ i, (x none * F.mult i - x (some i)) • F.curve i) := by
  have h := LinearMap.BilinForm.apply_sum_smul_self (mukaiForm b) F.affineRoot x
  rw [F.sum_smul_affineRoot, mukaiForm_rankZero] at h
  rw [affineCartan, h, neg_neg]

/-- **`G` is positive semidefinite.** -/
theorem dotProduct_affineCartan_nonneg (x : Option ι → ℤ) : 0 ≤ x ⬝ᵥ F.affineCartan *ᵥ x := by
  rw [dotProduct_affineCartan, neg_nonneg]
  exact F.self_combination_nonpos _

/-- **The isotropic vectors of `G` are the multiples of the marks.** -/
theorem eq_smul_nullMult_of_isotropic {x : Option ι → ℤ} (hx : x ⬝ᵥ F.affineCartan *ᵥ x = 0) :
    x = x none • F.nullMult := by
  rw [dotProduct_affineCartan, neg_eq_zero] at hx
  have h := congrFun (F.eq_zero_of_self_combination hx)
  ext k
  cases k with
  | none => simp
  | some i =>
    have := h i
    simp only [Pi.zero_apply, sub_eq_zero] at this
    simp [this]

/-- Every isotropic vector of `G` is zero or has full support. -/
theorem isotropic_eq_zero_or_full {x : Option ι → ℤ} (hx : x ⬝ᵥ F.affineCartan *ᵥ x = 0) :
    x = 0 ∨ ∀ k, x k ≠ 0 := by
  rw [F.eq_smul_nullMult_of_isotropic hx]
  by_cases h0 : x none = 0
  · left
    simp [h0]
  · right
    intro k
    simpa using And.intro h0 (F.nullMult_pos k).ne'

/-! ### (b) Roots are positive or negative -/

/-- The coordinates `(s, s zᵢ - dᵢ)` of the rank-zero class `(0, Σ dᵢ Cᵢ, s)` in the affine simple
roots. -/
def affineCoord (s : ℤ) (d : ι → ℤ) : Option ι → ℤ
  | none => s
  | some i => s * F.mult i - d i

theorem sum_affineCoord_smul_affineRoot (s : ℤ) (d : ι → ℤ) :
    ∑ k, F.affineCoord s d k • F.affineRoot k = (0, ∑ i, d i • F.curve i, s) := by
  rw [sum_smul_affineRoot]
  simp [affineCoord]

/-- **Sign coherence of the affine roots.** A rank-zero root `(0, c, s)` with `c = Σ dᵢ Cᵢ`, that
is `c² = -2`, has coordinates `(s, s zᵢ - dᵢ)` in the affine simple roots all `≥ 0` or all
`≤ 0`. -/
theorem signCoherent_affineCoord (hb : ∀ x y, b x y = b y x) (s : ℤ) {d : ι → ℤ}
    (hd : b (∑ i, d i • F.curve i) (∑ i, d i • F.curve i) = -2) :
    (∀ k, 0 ≤ F.affineCoord s d k) ∨ ∀ k, F.affineCoord s d k ≤ 0 := by
  classical
  refine (F.affineCartan_isZMatrix hb).signCoherent (F.affineCartan_isSymm hb)
    (fun k => by rw [F.affineCartan_diag]; exact even_two) F.dotProduct_affineCartan_nonneg
    (fun x hx => F.isotropic_eq_zero_or_full hx) ?_
  rw [dotProduct_affineCartan]
  simp only [affineCoord, sub_sub_cancel]
  rw [hd, neg_neg]

/-- **The roots of the fibre lattice are positive or negative** in the basis `Cᵢ`. -/
theorem nonneg_or_nonpos_of_root (hb : ∀ x y, b x y = b y x) {d : ι → ℤ}
    (hd : b (∑ i, d i • F.curve i) (∑ i, d i • F.curve i) = -2) :
    (∀ i, 0 ≤ d i) ∨ ∀ i, d i ≤ 0 := by
  rcases F.signCoherent_affineCoord hb 0 hd with h | h
  · right
    intro i
    simpa [affineCoord] using h (some i)
  · left
    intro i
    simpa [affineCoord] using h (some i)

/-- **`Θ` is the highest root.** Every root `c = Σ dᵢ Cᵢ` of the fibre lattice has `dᵢ ≤ zᵢ`. The
proof applies sign coherence to the affine root `(0, c, 1)`. -/
theorem le_mult_of_root (hb : ∀ x y, b x y = b y x) {d : ι → ℤ}
    (hd : b (∑ i, d i • F.curve i) (∑ i, d i • F.curve i) = -2) (i : ι) : d i ≤ F.mult i := by
  rcases F.signCoherent_affineCoord hb 1 hd with h | h
  · simpa [affineCoord] using h (some i)
  · exact absurd (h none) (by simp [affineCoord])

/-- Every root `c = Σ dᵢ Cᵢ` of the fibre lattice has `-zᵢ ≤ dᵢ`. -/
theorem neg_mult_le_of_root (hb : ∀ x y, b x y = b y x) {d : ι → ℤ}
    (hd : b (∑ i, d i • F.curve i) (∑ i, d i • F.curve i) = -2) (i : ι) : -F.mult i ≤ d i := by
  have hneg : ∑ i, (-d) i • F.curve i = -∑ i, d i • F.curve i := by
    simp [Finset.sum_neg_distrib]
  have hd' : b (∑ i, (-d) i • F.curve i) (∑ i, (-d) i • F.curve i) = -2 := by
    rw [hneg, map_neg, map_neg, LinearMap.neg_apply, neg_neg, hd]
  have := F.le_mult_of_root hb hd' i
  simp only [Pi.neg_apply] at this
  omega

/-! ### (c) The fundamental alcove -/

/-- **The charge on rank-zero classes**, `Z(r, c, s) = β(c) - s`. For a central charge
`Z = ⟨exp(β + iωH), ·⟩` with the Mukai form, a rank-zero class `(0, c, s)` with `H·c = 0` has
`Z(0, c, s) = β·c - s`. -/
def fibreCharge (β : N →+ ℝ) (v : MukaiLattice ℤ N) : ℝ :=
  β v.2.1 - v.2.2

@[simp] theorem fibreCharge_mk (β : N →+ ℝ) (r : ℤ) (c : N) (s : ℤ) :
    fibreCharge β (r, c, s) = β c - s :=
  rfl

theorem fibreCharge_neg (β : N →+ ℝ) (v : MukaiLattice ℤ N) :
    fibreCharge β (-v) = -fibreCharge β v := by
  simp [fibreCharge]
  ring

theorem fibreCharge_affineRoot_none (β : N →+ ℝ) :
    fibreCharge β (F.affineRoot none) = β F.cycle - 1 := by
  simp

theorem fibreCharge_affineRoot_some (β : N →+ ℝ) (i : ι) :
    fibreCharge β (F.affineRoot (some i)) = -β (F.curve i) := by
  simp

/-- `Z` is additive in the coordinates: `Z(Σ xₖ αₖ) = Σ xₖ Z(αₖ)`. -/
theorem fibreCharge_sum_smul_affineRoot (β : N →+ ℝ) (x : Option ι → ℤ) :
    fibreCharge β (∑ k, x k • F.affineRoot k) = ∑ k, x k * fibreCharge β (F.affineRoot k) := by
  rw [sum_smul_affineRoot, Fintype.sum_option, fibreCharge_mk, fibreCharge_affineRoot_none, cycle]
  simp only [fibreCharge_affineRoot_some, map_sum, map_zsmul, zsmul_eq_mul, Int.cast_sub,
    Int.cast_mul, sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, mul_neg,
    Finset.sum_neg_distrib, mul_one, mul_assoc]
  ring

/-- **The fundamental alcove**: `β·Cᵢ > 0` for every `i` and `β·Θ < 1`. -/
def IsInFundamentalAlcove (β : N →+ ℝ) : Prop :=
  (∀ i, 0 < β (F.curve i)) ∧ β F.cycle < 1

/-- **The closed fundamental alcove**: `β·Cᵢ ≥ 0` for every `i` and `β·Θ ≤ 1`. -/
def IsInClosedFundamentalAlcove (β : N →+ ℝ) : Prop :=
  (∀ i, 0 ≤ β (F.curve i)) ∧ β F.cycle ≤ 1

/-- The alcove inequalities say that `Z` is negative on every affine simple root. -/
theorem isInFundamentalAlcove_iff_affineRoot (β : N →+ ℝ) :
    F.IsInFundamentalAlcove β ↔ ∀ k, fibreCharge β (F.affineRoot k) < 0 := by
  constructor
  · rintro ⟨h1, h2⟩ k
    cases k with
    | none => simpa using h2
    | some i => simpa using h1 i
  · intro h
    exact ⟨fun i => by simpa using h (some i), by simpa using h none⟩

/-- **A rank-zero root of the fibre**: `(0, c, s)` with `c ∈ ⊕ ℤCᵢ` and `c² = -2`. -/
def IsRoot (v : MukaiLattice ℤ N) : Prop :=
  v.1 = 0 ∧ v.2.1 ∈ F.rootLattice ∧ b v.2.1 v.2.1 = -2

/-- **A positive root of the fibre**: a rank-zero root of the fibre with nonnegative coordinates
in the affine simple roots. -/
def IsPositiveRoot (v : MukaiLattice ℤ N) : Prop :=
  F.IsRoot v ∧ ∃ x : Option ι → ℤ, (∀ k, 0 ≤ x k) ∧ ∑ k, x k • F.affineRoot k = v

theorem isRoot_neg {v : MukaiLattice ℤ N} (hv : F.IsRoot v) : F.IsRoot (-v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  exact ⟨by simp [h1], F.rootLattice.neg_mem h2, by simpa using h3⟩

theorem isRoot_affineRoot (k : Option ι) : F.IsRoot (F.affineRoot k) := by
  classical
  cases k with
  | none =>
    exact ⟨rfl, ⟨F.mult, rfl⟩, F.cycle_self'⟩
  | some i =>
    refine ⟨rfl, ⟨-Pi.single i 1, ?_⟩, by simpa using F.curve_self i⟩
    simp [combination]

theorem isPositiveRoot_affineRoot (k : Option ι) : F.IsPositiveRoot (F.affineRoot k) := by
  classical
  refine ⟨F.isRoot_affineRoot k, Pi.single k 1, fun l => ?_, ?_⟩
  · by_cases h : l = k <;> simp [h]
  · simp

/-- **Every root of the fibre is positive or negative.** -/
theorem isPositiveRoot_or_neg (hb : ∀ x y, b x y = b y x) {v : MukaiLattice ℤ N}
    (hv : F.IsRoot v) : F.IsPositiveRoot v ∨ F.IsPositiveRoot (-v) := by
  obtain ⟨r, c, s⟩ := v
  obtain ⟨hr, ⟨d, hdc⟩, hc⟩ := hv
  simp only at hr hdc hc
  subst hr
  have hd : b (∑ i, d i • F.curve i) (∑ i, d i • F.curve i) = -2 := by
    rw [← combination_apply, hdc, hc]
  have hsum := F.sum_affineCoord_smul_affineRoot s d
  rw [← combination_apply, hdc] at hsum
  rcases F.signCoherent_affineCoord hb s hd with h | h
  · exact Or.inl ⟨⟨rfl, ⟨d, hdc⟩, hc⟩, _, h, hsum⟩
  · refine Or.inr ⟨F.isRoot_neg ⟨rfl, ⟨d, hdc⟩, hc⟩, -F.affineCoord s d, fun k => ?_, ?_⟩
    · simpa using h k
    · simp [neg_smul, Finset.sum_neg_distrib, hsum]

/-- **Part of the fundamental-alcove theorem.** The alcove inequalities hold iff `Z < 0` on every
positive root of the fibre. -/
theorem isInFundamentalAlcove_iff (β : N →+ ℝ) :
    F.IsInFundamentalAlcove β ↔ ∀ v, F.IsPositiveRoot v → fibreCharge β v < 0 := by
  classical
  constructor
  · intro hβ v ⟨hroot, x, hx, hxv⟩
    have hneg := (F.isInFundamentalAlcove_iff_affineRoot β).mp hβ
    -- some coordinate is positive, since `v ≠ 0`
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, 0 < x k₀ := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have hx0 : x = 0 := funext fun k => le_antisymm (h k) (hx k)
      have := hroot.2.2
      simp [← hxv, hx0] at this
    rw [← hxv, fibreCharge_sum_smul_affineRoot, ← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
    have h1 : (x k₀ : ℝ) * fibreCharge β (F.affineRoot k₀) < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast hk₀) (hneg k₀)
    have h2 : ∑ k ∈ Finset.univ.erase k₀, (x k : ℝ) * fibreCharge β (F.affineRoot k) ≤ 0 :=
      Finset.sum_nonpos fun k _ =>
        mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hx k) (hneg k).le
    linarith
  · intro h
    exact (F.isInFundamentalAlcove_iff_affineRoot β).mpr fun k =>
      h _ (F.isPositiveRoot_affineRoot k)

/-- **The fundamental-alcove theorem.** In the fundamental alcove, `Z ≠ 0` on every rank-zero root
`(0, c, s)` with `c ∈ ⊕ ℤCᵢ`. -/
theorem fibreCharge_ne_zero (hb : ∀ x y, b x y = b y x) {β : N →+ ℝ}
    (hβ : F.IsInFundamentalAlcove β) {v : MukaiLattice ℤ N} (hv : F.IsRoot v) :
    fibreCharge β v ≠ 0 := by
  have h := (F.isInFundamentalAlcove_iff β).mp hβ
  rcases F.isPositiveRoot_or_neg hb hv with hp | hn
  · exact (h v hp).ne
  · have := h _ hn
    rw [fibreCharge_neg] at this
    linarith

/-- **The boundary of the closed alcove.** A point of the closed alcove outside the open alcove
has some affine simple root in `ker Z`. -/
theorem exists_fibreCharge_affineRoot_eq_zero {β : N →+ ℝ}
    (hc : F.IsInClosedFundamentalAlcove β) (ho : ¬F.IsInFundamentalAlcove β) :
    ∃ k, fibreCharge β (F.affineRoot k) = 0 := by
  by_contra h
  simp only [not_exists] at h
  refine ho ⟨fun i => lt_of_le_of_ne (hc.1 i) fun h0 => h (some i) ?_, ?_⟩
  · simp [← h0]
  · refine lt_of_le_of_ne hc.2 fun h1 => h none ?_
    simp [h1]

/-! ### The Riemann–Roch membership field -/

/-- **The Riemann–Roch membership field** at a class `H`: every `(-2)`-class orthogonal to `H` is
supported on the fibre. On a K3 surface with `H` pulled back from the contraction of one fibre,
it follows from Riemann–Roch (a `(-2)`-class or its negative is effective) and from `H` being
ample off the exceptional curves. -/
structure RiemannRochMembership (H : N) : Prop where
  /-- Every `(-2)`-class orthogonal to `H` lies in `⊕ ℤCᵢ`. -/
  mem : ∀ c : N, b c H = 0 → b c c = -2 → c ∈ F.rootLattice

/-- **The fundamental-alcove theorem with the Riemann–Roch membership field.** In the
fundamental alcove, `Z ≠ 0` on every rank-zero root `(0, c, s)` with `H·c = 0`. -/
theorem fibreCharge_ne_zero_of_riemannRochMembership (hb : ∀ x y, b x y = b y x) {H : N}
    (hRR : F.RiemannRochMembership H) {β : N →+ ℝ} (hβ : F.IsInFundamentalAlcove β) {c : N}
    (hcH : b c H = 0) (hc : b c c = -2) (s : ℤ) : fibreCharge β ((0, c, s)) ≠ 0 :=
  F.fibreCharge_ne_zero hb hβ ⟨rfl, hRR.mem c hcH hc, hc⟩

end FundamentalCycle

end Mukai
