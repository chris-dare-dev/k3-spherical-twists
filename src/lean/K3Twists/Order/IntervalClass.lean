/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Order.Closure
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.SupClosed
import Mathlib.Order.WellFounded

/-!
# Interval classes and their saturation

An *interval class* on a lattice `α` is a predicate `Q a b`, read as "the subquotient `b / a`
belongs to a class `𝒯`", with three axioms:

* `refl`: `Q a a` (the class contains zero);
* `trans`: `Q a b` and `Q b c` give `Q a c` for `a ≤ b ≤ c` (closure under extensions, through
  `0 → b/a → c/a → c/b → 0`);
* `push`: `Q a s` gives `Q a' (a' ⊔ s)` for `a ≤ a'` and `a ≤ s` (closure under quotients, in the
  form `s/a ↠ (a' ⊔ s)/a'`, which also absorbs the second isomorphism theorem).

On the subobjects of an object `R` of an abelian category, `Q a b := 𝒯 (b / a)` is an interval
class for every class `𝒯` that contains zero and is closed under quotients and extensions
(`CategoryTheory.ObjectProperty.intervalClass`), for instance a torsion class in the sense of
Dickson. The radical `t(R)` and the saturation of a subobject are then order theory, the
lattice core of the torsion theory of Gabriel and Stenström.

## Main definitions

* `IntervalClass α`: the predicate and its three axioms;
* `IntervalClass.Hereditary`: `Q a c` gives `Q a b` for `a ≤ b ≤ c` (closure under subobjects);
* `IntervalClass.sat`: on a lattice with a top element and the ascending chain condition, the
  saturation `sat a`, the greatest `b ≥ a` with `Q a b` (for subobjects: the preimage in `R` of
  the largest subobject of `R / a` in the class);
* `IntervalClass.satClosure`: `sat` as a `ClosureOperator`;
* `IntervalClass.rad`: the radical `sat ⊥`, the greatest `b` with `b / ⊥` in the class;
* `IntervalClass.comap`: the interval class pulled back along an order isomorphism;
* `IntervalClass.Layer`, `IntervalClass.Layer.socleSeq`: a subclass closed under `⊔` that
  generates the class from below, and the iteration `a, soc a, soc (soc a), …` of its greatest
  steps.

## Main results

* `IntervalClass.satClosure`, `IntervalClass.isClosed_iff`: saturation is a closure operator, and
  `b` is saturated exactly when no `c > b` has `c / b` in the class (`t(R / b) = 0`);
* `IntervalClass.hereditary_iff_nested`: the nested formula — the saturation of `a` computed below
  `c` is `c ⊓ sat a`, for all `a ≤ c` — holds exactly when the class is hereditary;
* `IntervalClass.isGreatest_inf_rad`: for a hereditary class the radical computed below `c` is
  `c ⊓ rad` (the restriction formula `t(A) = A ∩ t(R)`), the case `a = ⊥` of the nested formula;
* `IntervalClass.sat_map`: an order isomorphism matching two interval classes matches their
  saturations;
* `IntervalClass.Layer.socleSeq_eq_sat_of_le`, `IntervalClass.Layer.exists_socleSeq_eq_sat`: the
  socle iteration from `a` reaches `sat a`, after at most `ℓ (sat a) - ℓ a` steps for any strictly
  monotone `ℓ : α → ℕ` (a length).

## Scope

The restriction formula for every `c` does not imply heredity: on the chain `0 < 1 < 2 < 3` with
`Q = refl ∪ {(1, 3), (2, 3)}` it holds while heredity and the nested formula fail (the model in
`K3TwistsTest/IntervalClassModel.lean`). It is also a different statement from the splitting law
for the radical in an extension `0 → A → R → B → 0`, by which the image of `t(R)` in `t(B)` is the
largest part of `t(B)` over which the extension, pushed out to `A / t(A)`, splits; that law is not
formalized here.

Defining `sat` uses all three axioms: the candidates are closed under `⊔` by `trans` and `push`
(without `trans` there may be no greatest candidate, also in the model file). Afterwards
monotonicity uses `push` and idempotence uses `trans`.

## References

* S. E. Dickson, *A torsion theory for Abelian categories*, Trans. Amer. Math. Soc. 121 (1966).
* B. Stenström, *Rings of Quotients*, Springer (1975), Chapter VI.

## Tags

torsion theory, radical, saturation, closure operator, interval class, socle series
-/

variable {α β : Type*}

/-- On a join-semilattice with the ascending chain condition, a nonempty set closed under `⊔` has
a greatest element. -/
theorem SupClosed.exists_isGreatest [SemilatticeSup α] [WellFoundedGT α] {s : Set α}
    (hs : SupClosed s) (hne : s.Nonempty) : ∃ a, IsGreatest s a := by
  obtain ⟨m, hm, hmax⟩ := (wellFounded_gt (α := α)).has_min s hne
  refine ⟨m, hm, fun a ha => ?_⟩
  have hlt : ¬ m < m ⊔ a := hmax _ (hs hm ha)
  rw [(le_sup_left.lt_or_eq).resolve_left hlt]
  exact le_sup_right

/-- An *interval class* on a lattice: a predicate `Q a b`, read as "the subquotient `b / a`
belongs to the class", that contains the zero subquotients and is closed under extensions
(`trans`) and quotients (`push`). On the subobjects of an object of an abelian category, a class
of objects containing zero and closed under quotients and extensions gives one
(`CategoryTheory.ObjectProperty.intervalClass`). -/
structure IntervalClass (α : Type*) [Lattice α] where
  /-- `Q a b`: the subquotient `b / a` belongs to the class. -/
  Q : α → α → Prop
  /-- The zero subquotient `a / a` belongs to the class. -/
  refl : ∀ a, Q a a
  /-- Closure under extensions: `b / a` and `c / b` in the class give `c / a` in the class. -/
  trans : ∀ {a b c}, a ≤ b → b ≤ c → Q a b → Q b c → Q a c
  /-- Closure under quotients, in the form `s / a ↠ (a' ⊔ s) / a'` for `a ≤ a'`. -/
  push : ∀ {a a' s}, a ≤ a' → a ≤ s → Q a s → Q a' (a' ⊔ s)

namespace IntervalClass

section Lattice

variable [Lattice α] (I : IntervalClass α)

/-- The class is *hereditary* (closed under subobjects): `c / a` in the class gives `b / a` in
the class for `a ≤ b ≤ c`. -/
def Hereditary : Prop :=
  ∀ ⦃a b c : α⦄, a ≤ b → b ≤ c → I.Q a c → I.Q a b

/-- Closure under the quotients `c / a ↠ c / b`, a case of `push`. -/
theorem quot {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) (h : I.Q a c) : I.Q b c := by
  have := I.push hab (hab.trans hbc) h
  rwa [sup_eq_right.mpr hbc] at this

/-- The candidates for the saturation of `a` below `c`: the `b` with `a ≤ b ≤ c` and `Q a b`. -/
def cands (a c : α) : Set α :=
  {b | a ≤ b ∧ b ≤ c ∧ I.Q a b}

/-- The candidates are closed under `⊔`; this uses `push` and `trans`. -/
theorem supClosed_cands (a c : α) : SupClosed (I.cands a c) := by
  rintro b ⟨hab, hbc, hQb⟩ b' ⟨hab', hbc', hQb'⟩
  exact ⟨le_sup_of_le_left hab, sup_le hbc hbc', I.trans hab le_sup_left hQb (I.push hab hab' hQb')⟩

/-- The interval class pulled back along an order isomorphism `e : α ≃o β`:
`Q a b := J.Q (e a) (e b)`. -/
def comap [Lattice β] (J : IntervalClass β) (e : α ≃o β) : IntervalClass α where
  Q a b := J.Q (e a) (e b)
  refl _ := J.refl _
  trans hab hbc h₁ h₂ := J.trans (e.monotone hab) (e.monotone hbc) h₁ h₂
  push {a a' s} h₁ h₂ h := by
    rw [map_sup]
    exact J.push (e.monotone h₁) (e.monotone h₂) h

@[simp]
theorem comap_Q [Lattice β] (J : IntervalClass β) (e : α ≃o β) (a b : α) :
    (J.comap e).Q a b ↔ J.Q (e a) (e b) :=
  Iff.rfl

variable [WellFoundedGT α]

/-- Below any `c ≥ a` there is a greatest candidate. -/
theorem exists_isGreatest_cands {a c : α} (h : a ≤ c) : ∃ s, IsGreatest (I.cands a c) s :=
  (I.supClosed_cands a c).exists_isGreatest ⟨a, le_rfl, h, I.refl a⟩

variable [OrderTop α]

/-- The saturation `sat a`: the greatest `b ≥ a` with `b / a` in the class. -/
noncomputable def sat (a : α) : α :=
  (I.exists_isGreatest_cands (le_top : a ≤ ⊤)).choose

theorem isGreatest_sat (a : α) : IsGreatest (I.cands a ⊤) (I.sat a) :=
  (I.exists_isGreatest_cands (le_top : a ≤ ⊤)).choose_spec

theorem le_sat (a : α) : a ≤ I.sat a :=
  (I.isGreatest_sat a).1.1

theorem Q_sat (a : α) : I.Q a (I.sat a) :=
  (I.isGreatest_sat a).1.2.2

theorem le_sat_of_Q {a b : α} (hab : a ≤ b) (h : I.Q a b) : b ≤ I.sat a :=
  (I.isGreatest_sat a).2 ⟨hab, le_top, h⟩

/-- The saturation is characterized as the greatest candidate. -/
theorem sat_eq_of_isGreatest {a b : α} (h : IsGreatest (I.cands a ⊤) b) : I.sat a = b :=
  (I.isGreatest_sat a).unique h

/-- Monotonicity of the saturation; this uses `push`. -/
theorem sat_mono {a a' : α} (h : a ≤ a') : I.sat a ≤ I.sat a' :=
  le_sup_right.trans (I.le_sat_of_Q le_sup_left (I.push h (I.le_sat a) (I.Q_sat a)))

/-- Idempotence of the saturation; this uses `trans`. -/
theorem sat_sat_le (a : α) : I.sat (I.sat a) ≤ I.sat a :=
  I.le_sat_of_Q ((I.le_sat a).trans (I.le_sat _))
    (I.trans (I.le_sat a) (I.le_sat _) (I.Q_sat a) (I.Q_sat _))

/-- Saturation is a closure operator. -/
noncomputable def satClosure : ClosureOperator α :=
  ClosureOperator.mk' I.sat (fun _ _ h => I.sat_mono h) I.le_sat I.sat_sat_le

@[simp]
theorem satClosure_apply (a : α) : I.satClosure a = I.sat a :=
  rfl

/-- The saturated elements are those `b` with no `c > b` such that `c / b` is in the class: for
subobjects, those with `t(R / b) = 0`. -/
theorem isClosed_iff (b : α) :
    I.satClosure.IsClosed b ↔ ∀ c, b ≤ c → I.Q b c → c ≤ b := by
  rw [ClosureOperator.isClosed_iff_closure_le]
  exact ⟨fun h c hbc hQ => (I.le_sat_of_Q hbc hQ).trans h, fun h => h _ (I.le_sat b) (I.Q_sat b)⟩

/-- **Transport.** An order isomorphism `e : α ≃o β` that matches the interval classes `I` and
`J` carries the saturation of `I` to that of `J`. -/
theorem sat_map [Lattice β] [WellFoundedGT β] [OrderTop β] (J : IntervalClass β) (e : α ≃o β)
    (he : ∀ a b, J.Q (e a) (e b) ↔ I.Q a b) (a : α) : e (I.sat a) = J.sat (e a) := by
  apply le_antisymm
  · exact J.le_sat_of_Q (e.monotone (I.le_sat a)) ((he _ _).2 (I.Q_sat a))
  · have h₁ : J.Q (e a) (J.sat (e a)) := J.Q_sat (e a)
    rw [← e.apply_symm_apply (J.sat (e a))] at h₁ ⊢
    rw [he] at h₁
    exact e.monotone (I.le_sat_of_Q ((e.le_symm_apply).2 (J.le_sat (e a))) h₁)

/-- The pulled-back class has the pulled-back saturation. -/
theorem sat_comap [Lattice β] [WellFoundedGT β] [OrderTop β] (J : IntervalClass β) (e : α ≃o β)
    (a : α) : e ((J.comap e).sat a) = J.sat (e a) :=
  (J.comap e).sat_map J e (fun _ _ => Iff.rfl) a

/-- **The nested formula** for a hereditary class: the saturation of `a` computed below `c ≥ a`
is `c ⊓ sat a`. -/
theorem isGreatest_inf_sat (hI : I.Hereditary) {a c : α} (hac : a ≤ c) :
    IsGreatest (I.cands a c) (c ⊓ I.sat a) := by
  refine ⟨⟨le_inf hac (I.le_sat a), inf_le_left, ?_⟩, ?_⟩
  · exact hI (le_inf hac (I.le_sat a)) inf_le_right (I.Q_sat a)
  · rintro b ⟨hab, hbc, hQ⟩
    exact le_inf hbc (I.le_sat_of_Q hab hQ)

/-- The nested formula characterizes hereditary classes: the saturation of `a` below `c` is
`c ⊓ sat a` for all `a ≤ c` exactly when the class is closed under subobjects. -/
theorem hereditary_iff_nested :
    I.Hereditary ↔ ∀ ⦃a c : α⦄, a ≤ c → IsGreatest (I.cands a c) (c ⊓ I.sat a) := by
  refine ⟨fun hI _ _ hac => I.isGreatest_inf_sat hI hac, fun h a b c hab hbc hQ => ?_⟩
  have hb : b ⊓ I.sat a = b :=
    inf_eq_left.mpr (le_trans hbc (I.le_sat_of_Q (hab.trans hbc) hQ))
  have := (h hab).1.2.2
  rwa [hb] at this

section Radical

variable [OrderBot α]

/-- The radical `rad = sat ⊥`: the greatest `b` with `b / ⊥` in the class (for subobjects of
`R`, the largest subobject `t(R)` in the class). -/
noncomputable def rad : α :=
  I.sat ⊥

theorem isGreatest_rad : IsGreatest {b | I.Q ⊥ b} I.rad :=
  ⟨I.Q_sat ⊥, fun _ hb => I.le_sat_of_Q bot_le hb⟩

theorem Q_rad : I.Q ⊥ I.rad :=
  I.Q_sat ⊥

theorem le_rad_of_Q {b : α} (h : I.Q ⊥ b) : b ≤ I.rad :=
  I.le_sat_of_Q bot_le h

theorem rad_eq_of_isGreatest {b : α} (h : IsGreatest {b | I.Q ⊥ b} b) : I.rad = b :=
  I.isGreatest_rad.unique h

/-- Every saturated element contains the radical. -/
theorem rad_le_sat (a : α) : I.rad ≤ I.sat a :=
  I.sat_mono bot_le

/-- **The restriction formula** `t(A) = A ⊓ t(R)` for a hereditary class: `c ⊓ rad` is the
greatest `b ≤ c` with `b / ⊥` in the class. This is the case `a = ⊥` of the nested formula; for
every `c` it does not imply heredity. It is not the splitting law for the image of `t(R)` in an
extension. -/
theorem isGreatest_inf_rad (hI : I.Hereditary) (c : α) :
    IsGreatest (I.cands ⊥ c) (c ⊓ I.rad) :=
  I.isGreatest_inf_sat hI bot_le

/-- The radical of a pulled-back class is the pulled-back radical. -/
theorem rad_comap [Lattice β] [WellFoundedGT β] [BoundedOrder β] (J : IntervalClass β)
    (e : α ≃o β) : e (J.comap e).rad = J.rad := by
  rw [rad, sat_comap, map_bot, rad]

end Radical

end Lattice

/-! ### The socle iteration -/

/-- A *layer* of an interval class `I`: a predicate `S a b` contained in `Q`, closed under `⊔`
over a fixed `a`, that generates `I` from below: whenever `a < b` and `Q a b`, some `c` with
`a < c ≤ b` has `S a c`. If the class `𝒯` is the extension closure of a set `𝒮` of objects and
closed under quotients, `S a b` can be "`b / a` is a quotient of a finite sum of objects of `𝒮`":
the first step of a filtration of a nonzero `b / a` with factors in `𝒮` gives `c`. For `𝒮` a set
of simple objects of `𝒯`, a step of the layer is a step of the socle series. -/
structure Layer [Lattice α] (I : IntervalClass α) where
  /-- `S a b`: the subquotient `b / a` belongs to the layer. -/
  S : α → α → Prop
  /-- The zero subquotient `a / a` belongs to the layer. -/
  refl : ∀ a, S a a
  /-- Closure under sums over a fixed `a`. -/
  sup : ∀ ⦃a b b'⦄, a ≤ b → a ≤ b' → S a b → S a b' → S a (b ⊔ b')
  /-- The layer is contained in the class. -/
  le : ∀ ⦃a b⦄, a ≤ b → S a b → I.Q a b
  /-- The layer generates the class from below. -/
  exists_of_lt : ∀ ⦃a b⦄, a < b → I.Q a b → ∃ c, a < c ∧ c ≤ b ∧ S a c

/-- Every interval class is a layer of itself: `Q a b` and `Q a b'` give `Q a (b ⊔ b')` by `push`
and `trans`. Its socle iteration reaches `sat a` in one step. -/
def selfLayer [Lattice α] (I : IntervalClass α) : I.Layer where
  S := I.Q
  refl := I.refl
  sup _ _ _ hab hab' h h' := I.trans hab le_sup_left h (I.push hab hab' h')
  le _ _ _ h := h
  exists_of_lt _ b hlt h := ⟨b, hlt, le_rfl, h⟩

namespace Layer

variable [Lattice α] {I : IntervalClass α} (L : I.Layer) [WellFoundedGT α]

theorem exists_isGreatest_soc (a : α) : ∃ s, IsGreatest {b | a ≤ b ∧ L.S a b} s :=
  SupClosed.exists_isGreatest
    (fun _ hb _ hb' => ⟨le_sup_of_le_left hb.1, L.sup hb.1 hb'.1 hb.2 hb'.2⟩) ⟨a, le_rfl, L.refl a⟩

/-- One step of the socle iteration: the greatest `b ≥ a` with `b / a` in the layer. -/
noncomputable def soc (a : α) : α :=
  (L.exists_isGreatest_soc a).choose

theorem le_soc (a : α) : a ≤ L.soc a :=
  (L.exists_isGreatest_soc a).choose_spec.1.1

theorem S_soc (a : α) : L.S a (L.soc a) :=
  (L.exists_isGreatest_soc a).choose_spec.1.2

theorem le_soc_of_S {a b : α} (hab : a ≤ b) (h : L.S a b) : b ≤ L.soc a :=
  (L.exists_isGreatest_soc a).choose_spec.2 ⟨hab, h⟩

/-- The socle iteration `a, soc a, soc (soc a), …`. -/
noncomputable def socleSeq (a : α) (n : ℕ) : α :=
  L.soc^[n] a

@[simp]
theorem socleSeq_zero (a : α) : L.socleSeq a 0 = a :=
  rfl

theorem socleSeq_succ (a : α) (n : ℕ) : L.socleSeq a (n + 1) = L.soc (L.socleSeq a n) :=
  Function.iterate_succ_apply' _ _ _

theorem socleSeq_le_succ (a : α) (n : ℕ) : L.socleSeq a n ≤ L.socleSeq a (n + 1) := by
  rw [socleSeq_succ]
  exact L.le_soc _

theorem monotone_socleSeq (a : α) : Monotone (L.socleSeq a) :=
  monotone_nat_of_le_succ (L.socleSeq_le_succ a)

theorem le_socleSeq (a : α) (n : ℕ) : a ≤ L.socleSeq a n :=
  L.monotone_socleSeq a (Nat.zero_le n)

/-- Each stage of the socle iteration from `a` is an extension of layers, so it lies in the
class over `a`. -/
theorem Q_socleSeq (a : α) (n : ℕ) : I.Q a (L.socleSeq a n) := by
  induction n with
  | zero => exact I.refl a
  | succ n ih =>
    rw [socleSeq_succ]
    exact I.trans (L.le_socleSeq a n) (L.le_soc _) ih (L.le (L.le_soc _) (L.S_soc _))

variable [OrderTop α]

theorem socleSeq_le_sat (a : α) (n : ℕ) : L.socleSeq a n ≤ I.sat a :=
  I.le_sat_of_Q (L.le_socleSeq a n) (L.Q_socleSeq a n)

/-- Below the saturation, every step of the socle iteration is strict. -/
theorem socleSeq_lt_succ {a : α} {n : ℕ} (h : L.socleSeq a n < I.sat a) :
    L.socleSeq a n < L.socleSeq a (n + 1) := by
  have hQ : I.Q (L.socleSeq a n) (I.sat a) :=
    I.quot (L.le_socleSeq a n) h.le (I.Q_sat a)
  obtain ⟨c, hlt, -, hS⟩ := L.exists_of_lt h hQ
  rw [socleSeq_succ]
  exact hlt.trans_le (L.le_soc_of_S hlt.le hS)

/-- **The finite socle iteration.** For a strictly monotone `ℓ : α → ℕ` (a length), the socle
iteration from `a` reaches the saturation `sat a` after `n` steps as soon as
`ℓ (sat a) ≤ ℓ a + n`. For subobjects of `R` and `a = ⊥`: the iteration reaches the radical
`t(R)` after at most `length t(R)` steps. -/
theorem socleSeq_eq_sat_of_le (ℓ : α → ℕ) (hℓ : StrictMono ℓ) {a : α} {n : ℕ}
    (h : ℓ (I.sat a) ≤ ℓ a + n) : L.socleSeq a n = I.sat a := by
  have key : ∀ m, L.socleSeq a m = I.sat a ∨ ℓ a + m ≤ ℓ (L.socleSeq a m) := by
    intro m
    induction m with
    | zero => exact Or.inr le_rfl
    | succ m ih =>
      rcases (L.socleSeq_le_sat a (m + 1)).lt_or_eq with hlt | heq
      · refine Or.inr ?_
        rcases ih with heq | hle
        · exact absurd (hlt.trans_le (heq ▸ L.socleSeq_le_succ a m)) (lt_irrefl _)
        · have hlt' : L.socleSeq a m < I.sat a :=
            (L.socleSeq_le_succ a m).trans_lt hlt
          have := hℓ (L.socleSeq_lt_succ hlt')
          omega
      · exact Or.inl heq
  rcases key n with heq | hle
  · exact heq
  · rcases (L.socleSeq_le_sat a n).lt_or_eq with hlt | heq
    · have := hℓ hlt
      omega
    · exact heq

/-- Under the ascending chain condition alone the socle iteration from `a` reaches `sat a`. -/
theorem exists_socleSeq_eq_sat (a : α) : ∃ n, L.socleSeq a n = I.sat a := by
  obtain ⟨n, hn⟩ := (wellFounded_gt (α := α)).not_rel_apply_succ (L.socleSeq a)
  refine ⟨n, ?_⟩
  rcases (L.socleSeq_le_sat a n).lt_or_eq with hlt | heq
  · exact absurd (L.socleSeq_lt_succ hlt) hn
  · exact heq

/-- The socle iteration from `⊥` reaches the radical after `n` steps when
`ℓ rad ≤ ℓ ⊥ + n`. -/
theorem socleSeq_bot_eq_rad_of_le [OrderBot α] (ℓ : α → ℕ) (hℓ : StrictMono ℓ) {n : ℕ}
    (h : ℓ I.rad ≤ ℓ ⊥ + n) : L.socleSeq ⊥ n = I.rad :=
  L.socleSeq_eq_sat_of_le ℓ hℓ h

end Layer

end IntervalClass
