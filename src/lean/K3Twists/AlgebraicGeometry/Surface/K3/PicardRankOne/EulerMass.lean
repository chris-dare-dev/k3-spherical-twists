/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.PeriodicWitness
import K3Twists.GroupTheory.GroupAction.MassGrowth

/-!
# The mass comparison on the Mukai lattice

Let `X` be a K3 surface with `Pic X = ℤH`, `H² = 2d`, `d ≥ 1`. This file builds
`MassComparisonHypotheses` from the classes of the library: objects are formal direct sums of Mukai
vectors (`ClassSum`), the isometries of the Mukai lattice act on them, the spherical objects are the
roots, the twist along a root is the reflection in it, the split generator is
`G = 𝒪_X ⊕ 𝒪_X(H) ⊕ 𝒪_X(2H)`, and the count is the absolute Euler pairing
`h(U, V) = Σ |χ(u, v)|` over the summands. Every field is proved:

* the diagonal estimate `|⟨u, v⟩| ≤ 21 N(u) N(v)` for `N(x) = Σ_k |⟨v(𝒪_X(kH)), x⟩|`
  (`abs_pairing_le`): the three pairings with the line bundles determine the coordinates of a class;
* isometries are additive (`isometry_smul_add`), which gives the conjugation formula
  `ρ_{g e} = g ρ_e g⁻¹` for reflections;
* the one-letter bounds (U_m), (L_m) are the triangle inequality for
  `⟨w, ρ_e v⟩ = ⟨w, v⟩ + ⟨e, v⟩⟨w, e⟩`.

The point `g` of the space of stability conditions is an isometry, and the "mass" at `g` is the
count `m_g(V) = h(gG, V)` from the moved generator. The distance bound is
`δ(g, g') = log(21 h(gG, g'G))`.

**What is not geometric.** The count `|χ|` is a lower bound for the total dimension of `Ext^*`
between objects, with equality at the centres, and `m_g` is the lattice shadow of the mass of a
stability condition. The fields `hom`, `mass` and `twist` have no geometric instance here: the
true Ext counts, masses and twist functors need the 2-Calabi–Yau category `D^b(X)`, its spherical
twists and a space of Bridgeland stability conditions, none of which Mathlib has. The model shows
that the comparison layer and Theorem C hold together with a positive exponent
(`eulerClassTwistSystem_tendsto_log_lenMax`), on the real classes of a K3 surface.

## Main definitions

* `ClassSum`: formal direct sums of Mukai vectors.
* `eulerMass d hd`: the instance of `MassComparisonHypotheses`.
* `eulerClassTwistSystem d`: the twist system of `𝒪_X` and `𝒪_X(H)` on `ClassSum`.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open MukaiVector Filter Topology Real

variable (d : ℤ)

/-! ### Three line bundles detect a class -/

/-- `v(𝒪_X)`, `v(𝒪_X(H))`, `v(𝒪_X(2H))`. -/
def lineTriple : Fin 3 → MukaiVector ℤ := ![lineBundle d 0, lineBundle d 1, lineBundle d 2]

lemma isRoot_lineTriple (k : Fin 3) : IsRoot d (lineTriple d k) := by
  fin_cases k <;> exact isRoot_lineBundle d _

/-- `N(x) = Σ_k |⟨v(𝒪_X(kH)), x⟩|`. -/
def lineNorm (x : MukaiVector ℤ) : ℤ := ∑ k, |pairing d (lineTriple d k) x|

lemma lineNorm_nonneg (x : MukaiVector ℤ) : 0 ≤ lineNorm d x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma pairing_lineTriple (x : MukaiVector ℤ) :
    pairing d (lineTriple d 0) x = -x.s - x.r ∧
      pairing d (lineTriple d 1) x = 2 * d * x.c - x.s - x.r * (d + 1) ∧
        pairing d (lineTriple d 2) x = 4 * d * x.c - x.s - x.r * (4 * d + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · show 2 * d * 0 * x.c - 1 * x.s - x.r * (d * 0 ^ 2 + 1) = -x.s - x.r
    ring
  · show 2 * d * 1 * x.c - 1 * x.s - x.r * (d * 1 ^ 2 + 1) = 2 * d * x.c - x.s - x.r * (d + 1)
    ring
  · show 2 * d * 2 * x.c - 1 * x.s - x.r * (d * 2 ^ 2 + 1) =
      4 * d * x.c - x.s - x.r * (4 * d + 1)
    ring

/-- The coordinates of a class are bounded by `N`: `|r| ≤ 2N`, `|2dc| ≤ 3N`, `|c| ≤ 3N`,
`|s| ≤ 3N`. -/
theorem coord_bounds (hd : 1 ≤ d) (x : MukaiVector ℤ) :
    |x.r| ≤ 2 * lineNorm d x ∧ |2 * d * x.c| ≤ 3 * lineNorm d x ∧ |x.c| ≤ 3 * lineNorm d x ∧
      |x.s| ≤ 3 * lineNorm d x := by
  obtain ⟨h0, h1, h2⟩ := pairing_lineTriple d x
  set l0 := pairing d (lineTriple d 0) x
  set l1 := pairing d (lineTriple d 1) x
  set l2 := pairing d (lineTriple d 2) x
  have hN : lineNorm d x = |l0| + |l1| + |l2| := by
    simp [lineNorm, Fin.sum_univ_three, l0, l1, l2]
  have hr : 2 * d * x.r = -(l2 - 2 * l1 + l0) := by rw [h0, h1, h2]; ring
  have hc : 2 * d * x.c = l1 - l0 + d * x.r := by rw [h0, h1]; ring
  have hs : x.s = -l0 - x.r := by rw [h0]; ring
  have hd2 : (1 : ℤ) ≤ 2 * d := by linarith
  have a0 := abs_nonneg l0
  have a1 := abs_nonneg l1
  have a2 := abs_nonneg l2
  have h2r : |2 * d * x.r| ≤ 2 * lineNorm d x := by
    rw [hr, abs_neg, hN]
    calc |l2 - 2 * l1 + l0| ≤ |l2 - 2 * l1| + |l0| := abs_add_le _ _
      _ ≤ |l2| + |2 * l1| + |l0| := by gcongr; exact abs_sub _ _
      _ = |l2| + 2 * |l1| + |l0| := by rw [abs_mul, abs_two]
      _ ≤ 2 * (|l0| + |l1| + |l2|) := by linarith
  have hrr : |x.r| ≤ |2 * d * x.r| := by
    rw [abs_mul (2 * d), abs_of_pos (by linarith : (0 : ℤ) < 2 * d)]
    exact le_mul_of_one_le_left (abs_nonneg _) hd2
  have hdr : |d * x.r| ≤ |2 * d * x.r| := by
    rw [abs_mul d, abs_mul (2 * d), abs_of_pos (by linarith : (0 : ℤ) < d),
      abs_of_pos (by linarith : (0 : ℤ) < 2 * d)]
    have := abs_nonneg x.r
    nlinarith
  have h2c : |2 * d * x.c| ≤ 3 * lineNorm d x := by
    rw [hc]
    calc |l1 - l0 + d * x.r| ≤ |l1 - l0| + |d * x.r| := abs_add_le _ _
      _ ≤ |l1| + |l0| + |d * x.r| := by gcongr; exact abs_sub _ _
      _ ≤ 3 * lineNorm d x := by rw [hN] at h2r ⊢; linarith
  have hcc : |x.c| ≤ |2 * d * x.c| := by
    rw [abs_mul (2 * d), abs_of_pos (by linarith : (0 : ℤ) < 2 * d)]
    exact le_mul_of_one_le_left (abs_nonneg _) hd2
  refine ⟨hrr.trans h2r, h2c, hcc.trans h2c, ?_⟩
  rw [hs]
  calc |-l0 - x.r| ≤ |-l0| + |x.r| := abs_sub _ _
    _ ≤ 3 * lineNorm d x := by
      rw [abs_neg]
      have := hrr.trans h2r
      rw [hN] at this ⊢
      linarith

/-- **The diagonal estimate on the Mukai lattice**: `|⟨u, v⟩| ≤ 21 N(u) N(v)`. -/
theorem abs_pairing_le (hd : 1 ≤ d) (u v : MukaiVector ℤ) :
    |pairing d u v| ≤ 21 * lineNorm d u * lineNorm d v := by
  obtain ⟨ur, uc2, -, us⟩ := coord_bounds d hd u
  obtain ⟨vr, -, vc, vs⟩ := coord_bounds d hd v
  have hu := lineNorm_nonneg d u
  have hv := lineNorm_nonneg d v
  have e : pairing d u v = (2 * d * u.c) * v.c - u.r * v.s - v.r * u.s := by
    simp only [pairing]
  rw [e]
  calc |(2 * d * u.c) * v.c - u.r * v.s - v.r * u.s|
      ≤ |(2 * d * u.c) * v.c - u.r * v.s| + |v.r * u.s| := abs_sub _ _
    _ ≤ |(2 * d * u.c) * v.c| + |u.r * v.s| + |v.r * u.s| := by gcongr; exact abs_sub _ _
    _ = |2 * d * u.c| * |v.c| + |u.r| * |v.s| + |v.r| * |u.s| := by
        rw [abs_mul (2 * d * u.c) v.c, abs_mul u.r v.s, abs_mul v.r u.s]
    _ ≤ (3 * lineNorm d u) * (3 * lineNorm d v) + (2 * lineNorm d u) * (3 * lineNorm d v) +
        (2 * lineNorm d v) * (3 * lineNorm d u) := by
        gcongr
    _ = 21 * lineNorm d u * lineNorm d v := by ring

/-- The three pairings with the line bundles determine a class. -/
theorem eq_zero_of_pairing_lineTriple (hd : d ≠ 0) {x : MukaiVector ℤ}
    (h : ∀ k, pairing d (lineTriple d k) x = 0) : x = 0 := by
  obtain ⟨h0, h1, h2⟩ := pairing_lineTriple d x
  rw [h 0] at h0
  rw [h 1] at h1
  rw [h 2] at h2
  have hr : 2 * d * x.r = 0 := by linear_combination h2 - 2 * h1 + h0
  have hr0 : x.r = 0 := by
    rcases mul_eq_zero.mp hr with h | h
    · exact absurd h (by omega)
    · exact h
  have hc : 2 * d * x.c = 0 := by linear_combination h0 - h1 + d * hr0
  have hc0 : x.c = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h (by omega)
    · exact h
  have hs0 : x.s = 0 := by linear_combination h0 - hr0
  ext <;> simp [hr0, hc0, hs0]

/-- A nonzero class pairs nontrivially with one of the line bundles. -/
theorem exists_pairing_lineTriple_ne_zero (hd : d ≠ 0) {x : MukaiVector ℤ} (hx : x ≠ 0) :
    ∃ k, pairing d (lineTriple d k) x ≠ 0 := by
  by_contra h
  push Not at h
  exact hx (eq_zero_of_pairing_lineTriple d hd h)

lemma ne_zero_of_isRoot {e : MukaiVector ℤ} (he : IsRoot d e) : e ≠ 0 := by
  rintro rfl
  simp [IsRoot, pairing] at he

/-! ### Isometries are additive -/

/-- An isometry of the Mukai lattice is additive: `g(x + y) - g x - g y` pairs to zero with every
class. -/
theorem isometry_smul_add (hd : d ≠ 0) (g : mukaiIsometries d) (x y : MukaiVector ℤ) :
    g • (x + y) = g • x + g • y := by
  have hz : g • (x + y) - g • x - g • y = 0 := by
    refine eq_zero_of_pairing_lineTriple d hd fun k => ?_
    have e : ∀ w, pairing d (lineTriple d k) (g • w) = pairing d (g⁻¹ • lineTriple d k) w := by
      intro w
      rw [← pairing_smul_isometry d g (g⁻¹ • lineTriple d k) w, smul_inv_smul]
    simp only [sub_eq_add_neg, pairing_add_right, pairing_neg_right, e]
    ring
  exact sub_eq_zero.mp (by rw [← hz]; abel)

/-- An isometry as an additive map. -/
def isometryAddHom (hd : d ≠ 0) (g : mukaiIsometries d) : MukaiVector ℤ →+ MukaiVector ℤ :=
  AddMonoidHom.mk' (g • ·) (isometry_smul_add d hd g)

lemma isometry_smul_zsmul (hd : d ≠ 0) (g : mukaiIsometries d) (n : ℤ) (x : MukaiVector ℤ) :
    g • (n • x) = n • (g • x) :=
  map_zsmul (isometryAddHom d hd g) n x

lemma isometry_smul_zero (hd : d ≠ 0) (g : mukaiIsometries d) : g • (0 : MukaiVector ℤ) = 0 :=
  map_zero (isometryAddHom d hd g)

/-- `ρ_{g e} = g ρ_e g⁻¹` for an isometry `g`. -/
theorem reflectIsometry_conj (hd : d ≠ 0) (g : mukaiIsometries d) {e : MukaiVector ℤ}
    (he : IsRoot d e) (hge : IsRoot d (g • e)) :
    reflectIsometry d hge = g * reflectIsometry d he * g⁻¹ := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  change (reflectIsometry d hge) • x = (g * reflectIsometry d he * g⁻¹) • x
  rw [mul_smul, mul_smul, reflectIsometry_smul, reflectIsometry_smul, bilinearFormReflect_apply,
    bilinearFormReflect_apply, isometry_smul_add d hd, isometry_smul_zsmul d hd, smul_inv_smul,
    ← pairing_smul_isometry d g e (g⁻¹ • x), smul_inv_smul]

lemma reflectIsometry_mul_self {e : MukaiVector ℤ} (he : IsRoot d e) :
    reflectIsometry d he * reflectIsometry d he = 1 :=
  Subtype.ext (Equiv.ext fun x => BilinearForm.reflect_reflect (mukaiForm d) e he x)

lemma reflectIsometry_inv {e : MukaiVector ℤ} (he : IsRoot d e) :
    (reflectIsometry d he)⁻¹ = reflectIsometry d he :=
  inv_eq_of_mul_eq_one_right (reflectIsometry_mul_self d he)

/-! ### Formal direct sums of classes -/

/-- A **formal direct sum of classes**: an object, read through the classes of its summands. -/
structure ClassSum where
  /-- The classes of the summands. -/
  toMultiset : Multiset (MukaiVector ℤ)

namespace ClassSum

/-- The object with one summand of class `x`. -/
def single (x : MukaiVector ℤ) : ClassSum := ⟨{x}⟩

instance : MulAction (mukaiIsometries d) ClassSum where
  smul g U := ⟨U.toMultiset.map (g • ·)⟩
  one_smul U := by
    show (⟨U.toMultiset.map ((1 : mukaiIsometries d) • ·)⟩ : ClassSum) = U
    simp
  mul_smul g h U := by
    show (⟨U.toMultiset.map ((g * h) • ·)⟩ : ClassSum) = ⟨(U.toMultiset.map (h • ·)).map (g • ·)⟩
    simp [Multiset.map_map, mul_smul]

lemma smul_toMultiset (g : mukaiIsometries d) (U : ClassSum) :
    (g • U).toMultiset = U.toMultiset.map (g • ·) := rfl

lemma smul_single (g : mukaiIsometries d) (x : MukaiVector ℤ) : g • single x = single (g • x) := by
  show (⟨({x} : Multiset _).map (g • ·)⟩ : ClassSum) = ⟨{g • x}⟩
  simp

/-- `h(U, V) = Σ_{u, v} |⟨u, v⟩|`, the absolute Euler pairing summed over the summands. -/
noncomputable def hom (U V : ClassSum) : ℝ :=
  (U.toMultiset.map fun u => (V.toMultiset.map fun v => |((pairing d u v : ℤ) : ℝ)|).sum).sum

/-- The same count with values in `ℕ`. -/
def count (U V : ClassSum) : ℕ :=
  (U.toMultiset.map fun u => (V.toMultiset.map fun v => (pairing d u v).natAbs).sum).sum

lemma count_cast (U V : ClassSum) : (count d U V : ℝ) = hom d U V := by
  simp only [count, hom, Nat.cast_multiset_sum, Multiset.map_map, Function.comp_def,
    Nat.cast_natAbs, Int.cast_abs]

lemma hom_nonneg (U V : ClassSum) : 0 ≤ hom d U V :=
  Multiset.sum_nonneg fun _ hx => by
    obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hx
    exact Multiset.sum_nonneg fun _ hy => by
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hy
      exact abs_nonneg _

lemma hom_comm (U V : ClassSum) : hom d U V = hom d V U := by
  unfold hom
  rw [Multiset.sum_map_sum_map]
  simp only [pairing_comm]

lemma hom_smul (g : mukaiIsometries d) (U V : ClassSum) : hom d (g • U) (g • V) = hom d U V := by
  simp [hom, smul_toMultiset, Multiset.map_map, pairing_smul_isometry]

lemma count_smul (g : mukaiIsometries d) (U V : ClassSum) :
    count d (g • U) (g • V) = count d U V := by
  simp [count, smul_toMultiset, Multiset.map_map, pairing_smul_isometry]

lemma hom_single_left (x : MukaiVector ℤ) (V : ClassSum) :
    hom d (single x) V = (V.toMultiset.map fun v => |((pairing d x v : ℤ) : ℝ)|).sum := by
  simp [hom, single]

lemma hom_single_right (U : ClassSum) (x : MukaiVector ℤ) :
    hom d U (single x) = (U.toMultiset.map fun u => |((pairing d u x : ℤ) : ℝ)|).sum := by
  simp [hom, single]

lemma single_le_hom {U V : ClassSum} {u v : MukaiVector ℤ} (hu : u ∈ U.toMultiset)
    (hv : v ∈ V.toMultiset) : |((pairing d u v : ℤ) : ℝ)| ≤ hom d U V := by
  have h1 : |((pairing d u v : ℤ) : ℝ)| ≤
      (V.toMultiset.map fun v => |((pairing d u v : ℤ) : ℝ)|).sum :=
    Multiset.single_le_sum (fun _ hx => by
      obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx; exact abs_nonneg _) _
      (Multiset.mem_map_of_mem _ hv)
  refine h1.trans (Multiset.single_le_sum (fun _ hx => ?_) _ (Multiset.mem_map_of_mem _ hu))
  obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx
  exact Multiset.sum_nonneg fun _ hy => by
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hy; exact abs_nonneg _

end ClassSum

open ClassSum

/-- `G = 𝒪_X ⊕ 𝒪_X(H) ⊕ 𝒪_X(2H)`. -/
def lineGenerator : ClassSum := ⟨{lineTriple d 0, lineTriple d 1, lineTriple d 2}⟩

lemma hom_lineGenerator (V : ClassSum) :
    hom d (lineGenerator d) V = ∑ k, hom d (single (lineTriple d k)) V := by
  simp [hom, lineGenerator, single, Fin.sum_univ_three, add_assoc]

/-- `h(G, single x) = N(x)`. -/
lemma hom_lineGenerator_single (x : MukaiVector ℤ) :
    hom d (lineGenerator d) (single x) = (lineNorm d x : ℝ) := by
  simp [hom, lineGenerator, single, lineNorm, Fin.sum_univ_three, add_assoc]

/-- `h(U, G) = Σ_u N(u)`. -/
lemma hom_lineGenerator_right (U : ClassSum) :
    hom d U (lineGenerator d) = (U.toMultiset.map fun u => (lineNorm d u : ℝ)).sum := by
  unfold hom
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun u _ => ?_)
  simp [lineGenerator, lineNorm, Fin.sum_univ_three, pairing_comm, add_assoc]

/-- `h(G, V) = Σ_v N(v)`. -/
lemma hom_lineGenerator_left (V : ClassSum) :
    hom d (lineGenerator d) V = (V.toMultiset.map fun v => (lineNorm d v : ℝ)).sum := by
  rw [hom_comm, hom_lineGenerator_right]

/-- **The diagonal estimate** `h(U, V) ≤ 21 h(U, G) h(G, V)`. -/
theorem hom_le_hom_lineGenerator (hd : 1 ≤ d) (U V : ClassSum) :
    hom d U V ≤ 21 * hom d U (lineGenerator d) * hom d (lineGenerator d) V := by
  rw [hom_lineGenerator_right, hom_lineGenerator_left]
  set SV := (V.toMultiset.map fun v => (lineNorm d v : ℝ)).sum
  calc hom d U V ≤ (U.toMultiset.map fun u =>
        (V.toMultiset.map fun v => 21 * (lineNorm d u : ℝ) * lineNorm d v).sum).sum := by
        unfold hom
        refine Multiset.sum_map_le_sum_map _ _ fun u _ => ?_
        refine Multiset.sum_map_le_sum_map _ _ fun v _ => ?_
        have h' : ((|pairing d u v| : ℤ) : ℝ) ≤ ((21 * lineNorm d u * lineNorm d v : ℤ) : ℝ) := by
          exact_mod_cast abs_pairing_le d hd u v
        push_cast at h'
        exact h'
    _ = (U.toMultiset.map fun u => (21 * (lineNorm d u : ℝ)) * SV).sum := by
        refine congrArg Multiset.sum (Multiset.map_congr rfl fun u _ => ?_)
        rw [Multiset.sum_map_mul_left]
    _ = 21 * (U.toMultiset.map fun u => (lineNorm d u : ℝ)).sum * SV := by
        rw [Multiset.sum_map_mul_right, Multiset.sum_map_mul_left]

/-! ### Reflections on formal sums -/

lemma pairing_reflect (e w v : MukaiVector ℤ) :
    pairing d w (BilinearForm.reflect (mukaiForm d) e v) =
      pairing d w v + pairing d e v * pairing d w e := by
  rw [bilinearFormReflect_apply, pairing_add_right, pairing_smul_right]

/-- The reflection in `e`, applied to every summand. -/
def reflectSum (e : MukaiVector ℤ) (V : ClassSum) : ClassSum :=
  ⟨V.toMultiset.map (BilinearForm.reflect (mukaiForm d) e)⟩

/-- `h(X, e) h(e, V)` as a double sum. -/
lemma hom_single_mul_hom_single (X : ClassSum) (e : MukaiVector ℤ) (V : ClassSum) :
    hom d X (single e) * hom d (single e) V =
      (X.toMultiset.map fun w => (V.toMultiset.map fun v =>
        |((pairing d w e : ℤ) : ℝ)| * |((pairing d e v : ℤ) : ℝ)|).sum).sum := by
  rw [hom_single_right, hom_single_left, ← Multiset.sum_map_mul_right]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun w _ => Multiset.sum_map_mul_left.symm)

/-- (U) on formal sums: `h(X, ρ_e V) ≤ h(X, V) + h(X, e) h(e, V)`. -/
theorem hom_reflectSum_le (X : ClassSum) (e : MukaiVector ℤ) (V : ClassSum) :
    hom d X (reflectSum d e V) ≤ hom d X V + hom d X (single e) * hom d (single e) V := by
  rw [hom_single_mul_hom_single]
  unfold hom reflectSum
  rw [← Multiset.sum_map_add]
  refine Multiset.sum_map_le_sum_map _ _ fun w _ => ?_
  rw [Multiset.map_map, ← Multiset.sum_map_add]
  refine Multiset.sum_map_le_sum_map _ _ fun v _ => ?_
  simp only [Function.comp, pairing_reflect]
  push_cast
  calc |((pairing d w v : ℤ) : ℝ) + (pairing d e v : ℤ) * (pairing d w e : ℤ)|
      ≤ |((pairing d w v : ℤ) : ℝ)| + |((pairing d e v : ℤ) : ℝ) * (pairing d w e : ℤ)| :=
        abs_add_le _ _
    _ = _ := by rw [abs_mul, mul_comm]

/-- (L) on formal sums: `h(e, V) h(X, e) ≤ h(X, V) + h(X, ρ_e V)`. -/
theorem hom_mul_le_reflectSum (X : ClassSum) (e : MukaiVector ℤ) (V : ClassSum) :
    hom d (single e) V * hom d X (single e) ≤ hom d X V + hom d X (reflectSum d e V) := by
  rw [mul_comm, hom_single_mul_hom_single]
  unfold hom reflectSum
  rw [← Multiset.sum_map_add]
  refine Multiset.sum_map_le_sum_map _ _ fun w _ => ?_
  rw [Multiset.map_map, ← Multiset.sum_map_add]
  refine Multiset.sum_map_le_sum_map _ _ fun v _ => ?_
  simp only [Function.comp, pairing_reflect]
  push_cast
  calc |((pairing d w e : ℤ) : ℝ)| * |((pairing d e v : ℤ) : ℝ)|
      = |(((pairing d w v : ℤ) : ℝ) + (pairing d e v : ℤ) * (pairing d w e : ℤ)) -
          ((pairing d w v : ℤ) : ℝ)| := by rw [← abs_mul]; ring_nf
    _ ≤ |((pairing d w v : ℤ) : ℝ)| +
          |((pairing d w v : ℤ) : ℝ) + (pairing d e v : ℤ) * (pairing d w e : ℤ)| :=
        (abs_sub _ _).trans (le_of_eq (add_comm _ _))

/-! ### The instance -/

/-- Spherical objects: one summand, whose class is a root. -/
def IsSphericalSum (U : ClassSum) : Prop := ∃ e, U = single e ∧ IsRoot d e

lemma reflectIsometry_congr {e e' : MukaiVector ℤ} (h : e = e') (he : IsRoot d e)
    (he' : IsRoot d e') : reflectIsometry d he = reflectIsometry d he' := by
  subst h; rfl

open Classical in
/-- The twist along a spherical object: the reflection in its root (and the identity on other
objects, where it is never used). -/
noncomputable def sumTwist (U : ClassSum) : mukaiIsometries d :=
  if h : IsSphericalSum d U then reflectIsometry d h.choose_spec.2 else 1

lemma sumTwist_single {e : MukaiVector ℤ} (he : IsRoot d e) :
    sumTwist d (single e) = reflectIsometry d he := by
  unfold sumTwist
  split_ifs with h
  · have h1 : single e = single h.choose := h.choose_spec.1
    have h2 : h.choose = e := by
      have := congrArg ClassSum.toMultiset h1
      simp only [single, Multiset.singleton_inj] at this
      exact this.symm
    exact reflectIsometry_congr d h2 _ _
  · exact absurd ⟨e, rfl, he⟩ h

lemma reflectIsometry_smul_sum {e : MukaiVector ℤ} (he : IsRoot d e) (V : ClassSum) :
    reflectIsometry d he • V = reflectSum d e V := rfl

lemma isRoot_smul (g : mukaiIsometries d) {e : MukaiVector ℤ} (he : IsRoot d e) :
    IsRoot d (g • e) := by
  unfold IsRoot at he ⊢; rw [pairing_smul_isometry]; exact he

lemma hom_single_le_of_mem (X : ClassSum) {v : MukaiVector ℤ} {V : ClassSum}
    (hv : v ∈ V.toMultiset) : hom d X (single v) ≤ hom d X V := by
  rw [hom_single_right]
  unfold hom
  refine Multiset.sum_map_le_sum_map _ _ fun w _ => ?_
  exact Multiset.single_le_sum (fun _ hx => by
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hx; exact abs_nonneg _) _
    (Multiset.mem_map_of_mem _ hv)

lemma mem_smul_lineGenerator (g : mukaiIsometries d) (k : Fin 3) :
    g • lineTriple d k ∈ (g • lineGenerator d).toMultiset := by
  rw [smul_toMultiset]
  exact Multiset.mem_map_of_mem _ (by fin_cases k <;> simp [lineGenerator])

/-- Nonzero classes have positive count from any translate of `G`. -/
lemma one_le_hom_smul_lineGenerator (hd : d ≠ 0) (g : mukaiIsometries d) {x : MukaiVector ℤ}
    (hx : x ≠ 0) : 1 ≤ hom d (g • lineGenerator d) (single x) := by
  have hx' : g⁻¹ • x ≠ 0 := fun h => hx (by
    have := congrArg (g • ·) h
    simpa [isometry_smul_zero d hd] using this)
  obtain ⟨k, hk⟩ := exists_pairing_lineTriple_ne_zero d hd hx'
  refine le_trans ?_ (single_le_hom d (mem_smul_lineGenerator d g k)
    (Multiset.mem_singleton_self x))
  rw [← pairing_smul_isometry d g⁻¹, inv_smul_smul]
  exact_mod_cast Int.one_le_abs hk

/-- Two translates of `G` have count at least one. -/
lemma one_le_hom_smul_smul (hd : d ≠ 0) (g g' : mukaiIsometries d) :
    1 ≤ hom d (g • lineGenerator d) (g' • lineGenerator d) :=
  (one_le_hom_smul_lineGenerator d hd g
    (ne_zero_of_isRoot d (isRoot_smul d g' (isRoot_lineTriple d 0)))).trans
    (hom_single_le_of_mem d _ (mem_smul_lineGenerator d g' 0))

/-- **The lattice instance of the mass comparison.** -/
noncomputable def eulerMass (hd : 1 ≤ d) :
    MassComparisonHypotheses ClassSum (mukaiIsometries d) (mukaiIsometries d) (Fin 3) where
  mass g V := hom d (g • lineGenerator d) V
  mass_nonneg _ _ := hom_nonneg d _ _
  δ g g' := log (21 * hom d (g • lineGenerator d) (g' • lineGenerator d))
  δ_nonneg g g' := by
    refine log_nonneg ?_
    have := one_le_hom_smul_smul d (by omega) g g'
    linarith
  δ_symm g g' := by rw [hom_comm]
  mass_le_exp_δ g g' V := by
    have hpos : 0 < 21 * hom d (g • lineGenerator d) (g' • lineGenerator d) := by
      have := one_le_hom_smul_smul d (by omega) g g'
      linarith
    rw [exp_log hpos]
    have h := hom_le_hom_lineGenerator d hd (g'⁻¹ • g • lineGenerator d) (g'⁻¹ • V)
    rw [hom_smul, ← hom_smul d g' (g'⁻¹ • g • lineGenerator d), smul_inv_smul,
      ← hom_smul d g' (lineGenerator d) (g'⁻¹ • V), smul_inv_smul] at h
    linarith
  hom := hom d
  hom_nonneg := hom_nonneg d
  hom_comm := hom_comm d
  hom_smul := hom_smul d
  mass_smul g g' V := by
    show hom d ((g * g') • lineGenerator d) (g • V) = hom d (g' • lineGenerator d) V
    rw [mul_smul, hom_smul]
  G := lineGenerator d
  S k := single (lineTriple d k)
  hom_G := hom_lineGenerator d
  K := 21
  K_pos := by norm_num
  hom_diag := hom_le_hom_lineGenerator d hd
  one_le_hom_G W := by
    have := one_le_hom_smul_smul d (by omega) 1 W
    rwa [one_smul] at this
  Spherical := IsSphericalSum d
  spherical_S k := ⟨lineTriple d k, rfl, isRoot_lineTriple d k⟩
  spherical_smul g U := by
    rintro ⟨e, rfl, he⟩
    exact ⟨g • e, smul_single d g e, isRoot_smul d g he⟩
  twist := sumTwist d
  twist_conj g E := by
    rintro ⟨e, rfl, he⟩
    rw [smul_single, sumTwist_single d (isRoot_smul d g he), sumTwist_single d he]
    exact reflectIsometry_conj d (by omega) g he _
  twist_smul_of_hom_eq_zero E V := by
    rintro ⟨e, rfl, he⟩ h
    rw [sumTwist_single d he, reflectIsometry_smul_sum]
    have hv : ∀ v ∈ V.toMultiset, pairing d e v = 0 := fun v hv => by
      have : |((pairing d e v : ℤ) : ℝ)| ≤ hom d (single e) V :=
        single_le_hom d (Multiset.mem_singleton_self e) hv
      rw [h] at this
      exact_mod_cast abs_nonpos_iff.mp this
    cases V with
    | mk V =>
      simp only [reflectSum, ClassSum.mk.injEq]
      conv_rhs => rw [← Multiset.map_id V]
      exact Multiset.map_congr rfl fun v hvV => by
        rw [bilinearFormReflect_apply, hv v hvV, zero_smul, add_zero]; rfl
  mass_twist_le g E V := by
    rintro ⟨e, rfl, he⟩
    rw [sumTwist_single d he, reflectIsometry_smul_sum]
    have := hom_reflectSum_le d (g • lineGenerator d) e V
    linarith
  mass_twist_inv_le g E V := by
    rintro ⟨e, rfl, he⟩
    rw [sumTwist_single d he, reflectIsometry_inv, reflectIsometry_smul_sum, hom_comm d V]
    have := hom_reflectSum_le d (g • lineGenerator d) e V
    linarith
  hom_mul_mass_le g E V := by
    rintro ⟨e, rfl, he⟩
    rw [sumTwist_single d he, reflectIsometry_smul_sum]
    exact hom_mul_le_reflectSum d (g • lineGenerator d) e V
  mass_pos_of_spherical g E := by
    rintro ⟨e, rfl, he⟩
    exact lt_of_lt_of_le one_pos
      (one_le_hom_smul_lineGenerator d (by omega) g (ne_zero_of_isRoot d he))
  C₁ := 1 / 21
  C₁_pos := by norm_num
  dhkk_comparison g U := by
    have h := hom_le_hom_lineGenerator d hd (g • lineGenerator d) U
    show 1 / 21 * hom d (g • lineGenerator d) U ≤
      hom d (g • lineGenerator d) (lineGenerator d) * hom d (lineGenerator d) U
    linarith

/-! ### The twist system of `𝒪_X` and `𝒪_X(H)` on formal sums, and Theorem C -/

lemma count_comm (U V : ClassSum) : count d U V = count d V U := by
  have := hom_comm d U V
  rw [← count_cast, ← count_cast] at this
  exact_mod_cast this

/-- The twist system of `𝒪_X` and `𝒪_X(H)` on formal sums: centres `v(𝒪_X)`, `v(𝒪_X(H))`, the
reflections in them as letters, and the count `Σ |χ|`. -/
def eulerClassTwistSystem : HomTwistSystem₀ (mukaiIsometries d) ClassSum (Fin 2) (Fin 2) where
  S i := single (lineCentre d i)
  T a := reflectIsometry d (isRoot_lineCentre d a)
  c := id
  h := count d
  h_smul := count_smul d
  upper a U V := by
    have := hom_reflectSum_le d U (lineCentre d a) V
    rw [← count_cast, ← count_cast, ← count_cast, ← count_cast] at this
    exact_mod_cast this

theorem eulerClassTwistSystem_isTwistSystem (hd : 1 ≤ d) :
    (eulerMass d hd).IsTwistSystem (eulerClassTwistSystem d) where
  count_eq U V := count_cast d U V
  spherical i := ⟨lineCentre d i, rfl, isRoot_lineCentre d i⟩
  letter a := Or.inl (sumTwist_single d (isRoot_lineCentre d a)).symm

theorem eulerClassTwistSystem_lowerBound : (eulerClassTwistSystem d).LowerBound := by
  intro a U Y
  have := hom_mul_le_reflectSum d U (lineCentre d a) Y
  rw [← count_cast, ← count_cast, ← count_cast, ← count_cast, mul_comm] at this
  exact_mod_cast this

theorem eulerClassTwistSystem_isSpherical : (eulerClassTwistSystem d).IsSpherical := by
  intro i
  change count d (single (lineCentre d i)) (single (lineCentre d i)) = 2
  simp [count, single, lineCentre_root d i]

theorem eulerClassTwistSystem_centre_smul (c : Fin 2) (D : ClassSum) :
    let H := eulerClassTwistSystem d
    H.h (H.S (H.c c)) (H.T c • D) = H.h (H.S (H.c c)) D := by
  intro H
  change count d (single (lineCentre d c)) (reflectSum d (lineCentre d c) D) =
    count d (single (lineCentre d c)) D
  simp only [count, single, reflectSum, Multiset.map_singleton, Multiset.sum_singleton,
    Multiset.map_map, Function.comp_def]
  congr 1
  refine Multiset.map_congr rfl fun v _ => ?_
  rw [pairing_reflect, lineCentre_root]
  rw [show pairing d (lineCentre d c) v + pairing d (lineCentre d c) v * -2 =
    -pairing d (lineCentre d c) v by ring, Int.natAbs_neg]

lemma one_le_count_lineCentre (hd : 0 ≤ d) (i j : Fin 2) :
    1 ≤ count d (single (lineCentre d i)) (single (lineCentre d j)) := by
  simp only [count, single, Multiset.map_singleton, Multiset.sum_singleton]
  fin_cases i <;> fin_cases j
  · simp [lineCentre_root]
  · simp only [Fin.zero_eta, Fin.mk_one]
    rw [pairing_lineCentre_zero_one]; omega
  · simp only [Fin.zero_eta, Fin.mk_one]
    rw [pairing_comm, pairing_lineCentre_zero_one]; omega
  · simp [lineCentre_root]

/-- Directed connectivity within two letters. -/
theorem eulerClassTwistSystem_directedConnected (hd : 0 ≤ d) :
    (eulerClassTwistSystem d).DirectedConnected 1 := by
  intro i j
  refine ⟨j, [i], rfl, rfl, le_rfl, ?_⟩
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact one_le_count_lineCentre d hd j i

/-- The whole system is one component: every subsystem on a predicate that always holds is
connected within two letters. -/
theorem eulerClassTwistSystem_restrict_directedConnected (hd : 0 ≤ d) (p : Fin 2 → Prop) :
    ((eulerClassTwistSystem d).restrict p).DirectedConnected 1 := by
  intro i j
  refine ⟨⟨j.1, j.2⟩, [⟨i.1, i.2⟩], rfl, rfl, le_rfl, ?_⟩
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact one_le_count_lineCentre d hd j.1 i.1

/-- **Theorem C on the Mukai lattice.** For the twist system of `𝒪_X` and `𝒪_X(H)` acting by
reflections (each letter is its own inverse), the Euler-count masses of the point class
`v(𝒪_x) = (0, 0, 1)`, maximized over the words of length exactly `n`, grow at an exact
exponential rate `η ≥ log(d + 1)`, at every point `g` of the model. -/
theorem eulerClass_exists_tendsto_log_lenMax (hd : 1 ≤ d) (g : mukaiIsometries d) :
    ∃ η : ℝ, log ((d : ℝ) + 1) ≤ η ∧
      Tendsto (fun n : ℕ => log (Monoid.lenMax (eulerClassTwistSystem d).T ((eulerMass d hd).mass g)
        n (single point)) / n) atTop (𝓝 η) := by
  classical
  set H := eulerClassTwistSystem d
  set I := eulerMass d hd
  have hH := eulerClassTwistSystem_isTwistSystem d hd
  have hinvT : ∀ a, H.T (id a) = (H.T a)⁻¹ := fun a =>
    (reflectIsometry_inv d (isRoot_lineCentre d a)).symm
  have hE : ∀ W : mukaiIsometries d, 1 ≤ I.hom I.G (W • single point) := fun W => by
    have hp : W • (point : MukaiVector ℤ) ≠ 0 := fun h => by
      have := congrArg (W⁻¹ • ·) h
      simp only [inv_smul_smul, isometry_smul_zero d (by omega)] at this
      have h1 := congrArg MukaiVector.s this
      simp [point] at h1
    have := one_le_hom_smul_lineGenerator d (by omega) 1 hp
    rw [one_smul] at this
    rw [smul_single]
    exact this
  have hC := hH.tendsto_log_lenMax (eulerClassTwistSystem_lowerBound d)
    (eulerClassTwistSystem_isSpherical d) id hinvT (fun _ => rfl) (fun _ : Fin 2 => ())
    (fun i j h => absurd rfl h) (d := 1)
    (fun _ => eulerClassTwistSystem_restrict_directedConnected d (by omega) _) g hE
  refine ⟨_, ?_, hC⟩
  -- the component meets the point, and its exponent is at least `log(d + 1)`
  have hmeet : ∃ i, (fun _ : Fin 2 => ()) i = () ∧ H.h (H.S i) (single point) ≠ 0 := by
    refine ⟨0, rfl, ?_⟩
    change count d (single (lineCentre d 0)) (single point) ≠ 0
    simp [count, single, lineCentre, pairing_comm, pairing_point_lineBundle]
  set B : {B : Unit // ∃ i, (fun _ : Fin 2 => ()) i = B ∧ H.h (H.S i) (single point) ≠ 0} :=
    ⟨(), hmeet⟩
  set H₀ := H.restrict fun i => (fun _ : Fin 2 => ()) i = B.1
  have : Nonempty {i // (fun _ : Fin 2 => ()) i = B.1} := ⟨⟨0, rfl⟩⟩
  have hwit : log ((d : ℝ) + 1) ≤ H₀.homExponent := by
    have hM : H₀.h (H₀.S (H₀.c ⟨0, rfl⟩)) (H₀.S (H₀.c ⟨1, rfl⟩)) = (d + 2).natAbs := by
      change count d (single (lineCentre d 0)) (single (lineCentre d 1)) = _
      simp only [count, single, Multiset.map_singleton, Multiset.sum_singleton]
      rw [pairing_lineCentre_zero_one, Int.natAbs_neg]
    have hcast : (((d + 2).natAbs : ℕ) : ℝ) = (d : ℝ) + 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast (by omega : 0 ≤ d + 2))]
      push_cast; ring
    have := H₀.log_sub_one_le_homExponent (fun U V => count_comm d U V)
      (H.lowerBound_restrict (eulerClassTwistSystem_lowerBound d) _)
      (H.isSpherical_restrict (eulerClassTwistSystem_isSpherical d) _)
      (fun c D => eulerClassTwistSystem_centre_smul d c.1 D)
      (eulerClassTwistSystem_restrict_directedConnected d (by omega) _) ⟨0, rfl⟩ ⟨1, rfl⟩
      (by rw [hM]; omega)
    rw [hM, hcast] at this
    convert this using 2
    ring
  refine hwit.trans (le_csSup ?_ (Set.mem_insert_of_mem _ ⟨B, rfl⟩))
  exact ((Set.finite_range _).insert 0).bddAbove

end AlgebraicGeometry.K3.PicardRankOne
