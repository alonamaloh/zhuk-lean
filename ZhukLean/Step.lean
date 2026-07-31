/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the CC BY 4.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ZhukLean.Center

/-!
# The enlargement step

Blueprint Theorem 5.1 (Zhuk). Applying a Taylor term of `B` to one element of `A`
and elements of the left center at every other coordinate strictly enlarges the
`R`-neighborhood, unless that neighborhood is a binary absorbing subuniverse of `B`.

The statement is over tuples constrained coordinatewise, matching
`Witnesses` — see blueprint Remark 5.3 for why the alternative shape is unusable.
-/

open FirstOrder Language

namespace ZhukLean

variable {L : Language} {A B : Type*} [L.Structure A] [L.Structure B]

/-- The set `E` of blueprint Theorem 5.1: values of `t` on tuples of `B` whose
`i`-th entry lies in the neighborhood of `a`. -/
def stepImage {k : ℕ} (t : L.Term (Fin k)) (i : Fin k) (N : Set B) : Set B :=
  {b | ∃ y : Fin k → B, y i ∈ N ∧ t.realize y = b}

theorem subset_stepImage (hB : IsIdempotent L B) {k : ℕ} (t : L.Term (Fin k)) (i : Fin k)
    (N : Set B) : N ⊆ stepImage t i N := by
  intro b hb
  exact ⟨fun _ => b, hb, hB.realize_const t b⟩

/-- Blueprint Theorem 5.1, Step 1: the image is contained in the neighborhood of the
value. This is where the elements of the left center at the other coordinates are
used: their neighborhoods are everything. -/
theorem stepImage_subset_nbhd {R : L.Substructure (A × B)} {k : ℕ} (t : L.Term (Fin k))
    (i : Fin k) (z : Fin k → A) (hz : ∀ j, j ≠ i → z j ∈ leftCenter R) :
    stepImage t i (nbhd R (z i)) ⊆ nbhd R (t.realize z) := by
  rintro _ ⟨y, hy, rfl⟩
  refine realize_mem_nbhd_realize t z y fun j => ?_
  by_cases hj : j = i
  · exact hj ▸ (by simpa [hj] using hy)
  · exact hz j hj (y j)

/-- **Blueprint Theorem 5.1** (the enlargement step).

If `B` has no nonempty proper binary absorbing subuniverse, then applying `t` with
one free coordinate and the left center elsewhere increases the neighborhood size by
at least one, until it saturates at `Nat.card B`. -/
theorem center_step [Finite B] (hA : IsIdempotent L A) (hB : IsIdempotent L B)
    {R : L.Substructure (A × B)} (hsd : Subdirect R)
    {k : ℕ} {t : L.Term (Fin k)} (T : IsTaylorOn (Set.univ : Set B) t)
    (hbaf : ∀ N : L.Substructure B, (N : Set B).Nonempty → (N : Set B) ≠ Set.univ →
      ¬ BinAbsorbs L (N : Set B) Set.univ)
    (i : Fin k) (z : Fin k → A) (hz : ∀ j, j ≠ i → z j ∈ leftCenter R) :
    min (Nat.card B) ((nbhd R (z i)).ncard + 1) ≤ (nbhd R (t.realize z)).ncard := by
  set N : Set B := nbhd R (z i) with hN
  set E : Set B := stepImage t i N with hE
  have hNE : N ⊆ E := subset_stepImage hB t i N
  have hEnb : E ⊆ nbhd R (t.realize z) := stepImage_subset_nbhd t i z hz
  by_cases hEN : E = N
  · -- The one-sided closure condition holds, so `N` binary absorbs `B`.
    have hone : ∀ y : Fin k → B, y i ∈ N → (∀ j, j ≠ i → y j ∈ (Set.univ : Set B)) →
        t.realize y ∈ N := by
      intro y hy _
      exact hEN ▸ ⟨y, hy, rfl⟩
    have hbin : BinAbsorbs L N (Set.univ : Set B) :=
      ⟨t.relabel (T i).u, binAbsorbs_of_oneSided (Set.subset_univ N) (T i) hone⟩
    have hNne : N.Nonempty := nbhd_nonempty hsd (z i)
    have hNuniv : N = Set.univ := by
      by_contra hcon
      exact hbaf (nbhdSub hA R (z i)) hNne hcon hbin
    -- Then `z i` is in the left center, hence so is the whole value.
    have hzi : z i ∈ leftCenter R := nbhd_eq_univ_iff.mp hNuniv
    have hall : ∀ j, z j ∈ leftCenter R := by
      intro j
      by_cases hj : j = i
      · exact hj ▸ hzi
      · exact hz j hj
    have : t.realize z ∈ leftCenter R := realize_mem_leftCenter hB t z hall
    have hfull : nbhd R (t.realize z) = Set.univ := nbhd_eq_univ_iff.mpr this
    rw [hfull, Set.ncard_univ]
    exact min_le_left _ _
  · -- Otherwise the image is strictly larger, so the neighborhood grew.
    have hss : N ⊂ E := ⟨hNE, fun h => hEN (Set.Subset.antisymm h hNE)⟩
    have hlt : N.ncard < E.ncard := Set.ncard_lt_ncard hss (Set.toFinite E)
    have hle : E.ncard ≤ (nbhd R (t.realize z)).ncard :=
      Set.ncard_le_ncard hEnb (Set.toFinite _)
    exact le_trans (min_le_right _ _) (le_trans hlt hle)

end ZhukLean
