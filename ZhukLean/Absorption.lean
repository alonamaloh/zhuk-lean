/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ZhukLean.Product
import Mathlib.Tactic.FinCases

/-!
# Idempotence, absorption, and Taylor identities

Part I §2 of the blueprint.

The one thing to get right here is the *quantifier shape* of absorption
(blueprint Definition 2.1 and Remark 2.2): the condition constrains a tuple
`z`, rather than quantifying over a list drawn from `E` and overwriting one
entry. The two readings differ exactly when `E = ∅`, `m = 1` and `D ≠ ∅`, and
only the tuple form makes the relational description of absorption a true
biconditional.

## Main definitions

* `IsIdempotent L M` — blueprint Definition 1.3.
* `Witnesses E D t` — blueprint Definition 2.1: `t` witnesses `E ⊴ D`.
* `Absorbs L E D` (`E ⊴ D`) and `BinAbsorbs L E D` (`E ⊴_bin D`).
* `TaylorAt D t i` — blueprint Definition 2.4, a Taylor identity at one coordinate.

## Main results

* `IsIdempotent.realize_const` — blueprint Lemma 1.13.
* `binAbsorbs_of_oneSided` — blueprint Lemma 2.6, the engine that turns a
  one-sided closure condition into two-sided binary absorption.
-/

open FirstOrder Language

namespace ZhukLean

variable {L : Language} {M : Type*} [L.Structure M]

/-! ## Idempotence -/

/-- Blueprint Definition 1.3: every basic operation is idempotent. -/
def IsIdempotent (L : Language) (M : Type*) [L.Structure M] : Prop :=
  ∀ {n : ℕ} (f : L.Functions n) (a : M), Structure.funMap f (fun _ => a) = a

/-- Blueprint Lemma 1.13: in an idempotent algebra every term operation is idempotent. -/
theorem IsIdempotent.realize_const (h : IsIdempotent L M) {α : Type*} (t : L.Term α) (a : M) :
    t.realize (fun _ => a) = a := by
  induction t with
  | var _ => rfl
  | func f ts ih =>
      have hts : (fun i => (ts i).realize (fun _ => a)) = fun _ => a := funext ih
      simp only [Term.realize, hts]
      exact h f a

/-- Blueprint Lemma 1.7: in an idempotent algebra every singleton is a subuniverse. -/
theorem IsIdempotent.closedUnder_singleton (h : IsIdempotent L M) {n : ℕ} (f : L.Functions n)
    (a : M) : ClosedUnder f ({a} : Set M) := by
  intro x hx
  have : x = fun _ => a := funext fun i => hx i
  simp [this, h f a]

/-! ## Absorption -/

/-- Blueprint Definition 2.1: the `m`-ary term `t` *witnesses* `E ⊴ D`.

Note the quantifier shape: the tuple `z` is constrained coordinatewise. See
Remark 2.2 of the blueprint for why the alternative reading is wrong. -/
def Witnesses (E D : Set M) {V : Type*} (t : L.Term V) : Prop :=
  ∀ (i : V) (z : V → M), z i ∈ D → (∀ j, j ≠ i → z j ∈ E) → t.realize z ∈ E

/-- Blueprint Definition 2.1: `E ⊴ D`. -/
def Absorbs (L : Language) [L.Structure M] (E D : Set M) : Prop :=
  ∃ (m : ℕ) (t : L.Term (Fin m)), Witnesses E D t

/-- Blueprint Definition 2.1: `E ⊴_bin D`, absorption witnessed by a binary term. -/
def BinAbsorbs (L : Language) [L.Structure M] (E D : Set M) : Prop :=
  ∃ t : L.Term (Fin 2), Witnesses E D t

theorem Absorbs.of_witnesses {E D : Set M} {m : ℕ} {t : L.Term (Fin m)}
    (h : Witnesses E D t) : Absorbs L E D := ⟨m, t, h⟩

/-- `Witnesses` transports along a relabelling of the variable type by an equivalence. -/
theorem Witnesses.relabelEquiv {E D : Set M} {V W : Type*} (e : V ≃ W) {t : L.Term V}
    (h : Witnesses E D t) : Witnesses E D (t.relabel e) := by
  intro i z hz hzE
  rw [Term.realize_relabel]
  refine h (e.symm i) (z ∘ e) ?_ ?_
  · simpa using hz
  · intro j hj
    exact hzE (e j) fun hcon => hj (by simpa using congrArg e.symm hcon)

theorem BinAbsorbs.absorbs {E D : Set M} (h : BinAbsorbs L E D) : Absorbs L E D := by
  obtain ⟨t, ht⟩ := h
  exact ⟨2, t, ht⟩

/-- A witness over any finite variable type gives absorption, by transporting along
`Fintype.equivFin`. This is what lets the star powers (whose variables are indexed by
functions) feed the `Fin m`-indexed `Absorbs`. -/
theorem Absorbs.of_finite {E D : Set M} {V : Type*} [Finite V] {t : L.Term V}
    (h : Witnesses E D t) : Absorbs L E D := by
  have : Fintype V := Fintype.ofFinite V
  exact ⟨Fintype.card V, t.relabel (Fintype.equivFin V), h.relabelEquiv (Fintype.equivFin V)⟩

/-- Blueprint Remark 2.3: the whole universe absorbs itself, witnessed by a variable. -/
theorem witnesses_univ (D : Set M) : Witnesses Set.univ D (L := L) (var 0 : L.Term (Fin 1)) := by
  intro _ _ _ _
  trivial

/-! ## Taylor identities -/

/-- Blueprint Definition 2.4: a Taylor identity for `t` at coordinate `i` over `D`.

`u` and `v` select, for each coordinate of `t`, one of the two variables `x` and `y`;
at the distinguished coordinate `i` they select different ones. Using
`Term.relabel`, the two sides are literally binary terms, which is what makes
`binAbsorbs_of_oneSided` below a substitution argument rather than an index
computation. -/
structure TaylorAt (D : Set M) {k : ℕ} (t : L.Term (Fin k)) (i : Fin k) where
  /-- The left-hand variable selection. -/
  u : Fin k → Fin 2
  /-- The right-hand variable selection. -/
  v : Fin k → Fin 2
  /-- The left side carries the first variable at coordinate `i`. -/
  u_at : u i = 0
  /-- The right side carries the second variable at coordinate `i`. -/
  v_at : v i = 1
  /-- The two sides agree on `D`. -/
  realize_eq : ∀ w : Fin 2 → M, (∀ b, w b ∈ D) →
    (t.relabel u).realize w = (t.relabel v).realize w

/-- `t` is Taylor on `D` when it has a Taylor identity at every coordinate. -/
def IsTaylorOn (D : Set M) {k : ℕ} (t : L.Term (Fin k)) : Type _ :=
  ∀ i : Fin k, TaylorAt D t i

/-! ## Blueprint Lemma 2.6

A one-sided closure condition, plus a single Taylor identity, gives two-sided
binary absorption.

The blueprint states this with `E` and `D` subuniverses; the proof uses only
`E ⊆ D`, so that is all we assume. -/

theorem binAbsorbs_of_oneSided {E D : Set M} (hED : E ⊆ D)
    {k : ℕ} {t : L.Term (Fin k)} {i : Fin k} (T : TaylorAt D t i)
    (hone : ∀ z : Fin k → M, z i ∈ E → (∀ j, j ≠ i → z j ∈ D) → t.realize z ∈ E) :
    Witnesses E D (t.relabel T.u) := by
  intro i₀ z hz hzE
  -- Every coordinate of `z` lies in `D`: the free one by hypothesis, the rest via `E ⊆ D`.
  have hzD : ∀ b, z b ∈ D := by
    intro b
    by_cases hb : b = i₀
    · exact hb ▸ hz
    · exact hED (hzE b hb)
  rw [Term.realize_relabel]
  -- Two cases, according to which of the two variables is the free one.
  fin_cases i₀
  · -- `z 0 ∈ D`, `z 1 ∈ E`: switch to the `v` side, which carries `z 1` at coordinate `i`.
    have hswap : t.realize (z ∘ T.u) = t.realize (z ∘ T.v) := by
      have := T.realize_eq z hzD
      rwa [Term.realize_relabel, Term.realize_relabel] at this
    rw [hswap]
    refine hone _ ?_ ?_
    · change z (T.v i) ∈ E
      rw [T.v_at]
      exact hzE 1 (by decide)
    · intro j _
      exact hzD (T.v j)
  · -- `z 0 ∈ E`, `z 1 ∈ D`: the `u` side already carries `z 0` at coordinate `i`.
    refine hone _ ?_ ?_
    · change z (T.u i) ∈ E
      rw [T.u_at]
      exact hzE 0 (by decide)
    · intro j _
      exact hzD (T.u j)

end ZhukLean
