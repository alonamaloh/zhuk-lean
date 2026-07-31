/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ZhukLean.Doubling

/-!
# The ternary collapse and the main theorem

Blueprint Corollary 8.1 and Theorem 0.1.

Iterating the doubling trick from arity `3` produces `C`-essential relations of
arity `2 + 2 ^ j` for every `j` — the arities blueprint Remark 8.2 records — while
absorption bounds the arity. So no ternary `C`-essential relation exists, and the
relational description turns that into a ternary witness.
-/

open FirstOrder Language

namespace ZhukLean

variable {L : Language} {A B : Type*} [L.Structure A] [L.Structure B]

/-- **Blueprint Corollary 8.1**: central absorption is witnessed by a ternary term. -/
theorem exists_ternary_witnesses [Finite A] {C : L.Substructure A} (hA : IsIdempotent L A)
    (hZ : ∀ a ∉ (C : Set A),
      ((a, a) : A × A) ∉ Substructure.closure L (centralPairs (C : Set A) a))
    (habs : Absorbs L (C : Set A) Set.univ) :
    ∃ s : L.Term (Fin 3), Witnesses (C : Set A) Set.univ s := by
  by_contra hcon
  push Not at hcon
  -- Failing to absorb at arity 3 produces a ternary essential relation.
  have h3 : HasEssential L (C : Set A) 3 := by
    by_contra h
    obtain ⟨s, hs⟩ := exists_witnesses_of_not_hasEssential (m := 3) (by omega) h
    exact hcon s hs
  -- Doubling iterates the arity through `2 + 2 ^ j`.
  have hiter : ∀ j : ℕ, HasEssential L (C : Set A) (2 + 2 ^ j) := by
    intro j
    induction j with
    | zero => simpa using h3
    | succ j ih =>
        have hprev : HasEssential L (C : Set A) (2 ^ j + 2) := by
          simpa [Nat.add_comm] using ih
        have hdbl := hasEssential_doubled hA hZ hprev
        have harith : 2 ^ j + 1 + (2 ^ j + 1) = 2 + 2 ^ (j + 1) := by
          rw [pow_succ]; omega
        exact harith ▸ hdbl
  -- But absorption bounds the arity.
  obtain ⟨m, t, ht⟩ := habs
  have hbig : m ≤ 2 + 2 ^ m := le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) (by omega)
  exact not_hasEssential_of_witnesses ht hbig (hiter m)

/-- **Blueprint Theorem 0.1** (main theorem).

Let `A`, `B` be finite idempotent algebras and `R ≤ A × B` subdirect, with left
centre `C`. If `B` has a Taylor term and no nonempty proper binary absorbing
subuniverse, then `C` centrally absorbs `A`, and the absorption is witnessed by a
**ternary** term. -/
theorem zhuk_main [Finite A] [Finite B] [Nonempty B] (hA : IsIdempotent L A)
    (hB : IsIdempotent L B) {R : L.Substructure (A × B)} (hsd : Subdirect R)
    {k : ℕ} {t : L.Term (Fin k)} (T : IsTaylorOn (Set.univ : Set B) t)
    (hbaf : ∀ N : L.Substructure B, (N : Set B).Nonempty → (N : Set B) ≠ Set.univ →
      ¬ BinAbsorbs L (N : Set B) Set.univ) :
    CentrallyAbsorbs L (leftCenter R) ∧
      ∃ s : L.Term (Fin 3), Witnesses (leftCenter R) Set.univ s := by
  have hz : CentrallyAbsorbs L (leftCenter R) := zhuk_center hA hB hsd T hbaf
  exact ⟨hz, exists_ternary_witnesses (C := leftCenterSub hB R) hA hz.central hz.absorbs⟩

end ZhukLean
