/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ZhukLean.Absorption

/-!
# Essential relations

Blueprint Part II, Definitions 3.1–3.2 and Propositions 3.4–3.6.

An `m`-ary `S`-essential relation meets every box with one coordinate free and the
rest confined to `S`, but misses the all-`S` box. It is exactly the obstruction to
`m`-ary absorption.

## Main definitions

* `IsEssential L S R` — blueprint Definition 3.1 in the single-algebra case.

## Main results

* `not_isEssential_of_witnesses` — blueprint Proposition 3.5: absorption at arity
  `m` forbids `S`-essential relations of arity `m`.
-/

open FirstOrder Language

namespace ZhukLean

variable {L : Language} {M : Type*} [L.Structure M]

/-- Blueprint Definition 3.1, single-algebra case: `R` is `S`-essential of arity `m`.

`witness` is condition (E1) and `no_full` is condition (E2). -/
structure IsEssential (S : Set M) {m : ℕ} (R : L.Substructure (Fin m → M)) : Prop where
  /-- (E1): for each coordinate there is a tuple free at that coordinate and in `S` elsewhere. -/
  witness : ∀ i : Fin m, ∃ x ∈ R, ∀ j, j ≠ i → x j ∈ S
  /-- (E2): no tuple of `R` has all coordinates in `S`. -/
  no_full : ∀ x ∈ R, ¬ ∀ j, x j ∈ S

/-! ## Blueprint Proposition 3.5

If an `m`-ary term witnesses `S ⊴ A`, then there is no `S`-essential relation of
arity `m`. The proof applies the witnessing term to the `m` witnessing tuples: in
coordinate `j` the free argument sits in position `j`, so absorption puts the value
in `S`. -/

theorem exists_mem_forall_mem_of_witnesses {S : Set M} {m : ℕ} {t : L.Term (Fin m)}
    (ht : Witnesses S Set.univ t) (R : L.Substructure (Fin m → M))
    (hw : ∀ i : Fin m, ∃ x ∈ R, ∀ j, j ≠ i → x j ∈ S) :
    ∃ x ∈ R, ∀ j, x j ∈ S := by
  choose r hrR hrS using hw
  refine ⟨t.realize r, t.realize_mem r hrR, ?_⟩
  intro j
  rw [realize_pi]
  exact ht j (fun i => r i j) (Set.mem_univ _) fun i hi => hrS i j (Ne.symm hi)

theorem not_isEssential_of_witnesses {S : Set M} {m : ℕ} {t : L.Term (Fin m)}
    (ht : Witnesses S Set.univ t) (R : L.Substructure (Fin m → M)) :
    ¬ IsEssential S R := by
  rintro ⟨hw, hno⟩
  obtain ⟨x, hxR, hxS⟩ := exists_mem_forall_mem_of_witnesses ht R hw
  exact hno x hxR hxS

end ZhukLean
