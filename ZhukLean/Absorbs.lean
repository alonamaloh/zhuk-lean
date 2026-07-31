/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the CC BY 4.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ZhukLean.Step
import ZhukLean.StarPower

/-!
# Zhuk: the left center absorbs

Blueprint Theorem 5.2. Iterating the enlargement step `Nat.card B - 1` times drives
the value into the left center, so the star power of a Taylor term witnesses that
the left center absorbs `A`.

The induction `(∗_ℓ)` is stated over tuples constrained coordinatewise, matching
`Witnesses` exactly; blueprint Remark 5.3 explains why the alternative shape leaves
a gap at `C = ∅`.
-/

open FirstOrder Language

namespace ZhukLean

variable {L : Language} {A B : Type*} [L.Structure A] [L.Structure B]

/-- The `min` identity of blueprint Appendix C item 2, together with the
monotonicity it is used with. -/
theorem min_min_add_one (N x : ℕ) : min N (min N x + 1) = min N (x + 1) := by omega

/-- The inductive statement `(∗_ℓ)` of blueprint Theorem 5.2. -/
theorem center_star [Finite B] (hA : IsIdempotent L A) (hB : IsIdempotent L B)
    {R : L.Substructure (A × B)} (hsd : Subdirect R)
    {k : ℕ} {t : L.Term (Fin k)} (T : IsTaylorOn (Set.univ : Set B) t)
    (hbaf : ∀ N : L.Substructure B, (N : Set B).Nonempty → (N : Set B) ≠ Set.univ →
      ¬ BinAbsorbs L (N : Set B) Set.univ) :
    ∀ (ℓ : ℕ) (p : Fin ℓ → Fin k) (z : (Fin ℓ → Fin k) → A),
      (∀ r, r ≠ p → z r ∈ leftCenter R) →
      min (Nat.card B) ((nbhd R (z p)).ncard + ℓ)
        ≤ (nbhd R ((starPower t ℓ).realize z)).ncard := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro p z _
      have hp : p = Fin.elim0 := funext fun i => i.elim0
      rw [realize_starPower_zero, hp, Nat.add_zero]
      exact min_le_right _ _
  | succ ℓ ih =>
      intro p z hz
      -- Split the index: the block is `p 0`, the position inside it is `Fin.tail p`.
      set j : Fin k := p 0 with hjdef
      set d : Fin k → A := fun j' => (starPower t ℓ).realize fun q' => z (Fin.cons j' q')
        with hddef
      -- Blocks other than `j` consist entirely of centre elements.
      have hdC : ∀ j', j' ≠ j → d j' ∈ leftCenter R := by
        intro j' hj'
        refine realize_mem_leftCenter hB _ _ fun q' => hz _ fun hcon => hj' ?_
        rw [hjdef, ← hcon, Fin.cons_zero]
      -- The `j`-th block carries the free coordinate; apply the inductive hypothesis.
      have hIH : min (Nat.card B) ((nbhd R (z p)).ncard + ℓ) ≤ (nbhd R (d j)).ncard := by
        have hside : ∀ r, r ≠ Fin.tail p → (fun q' => z (Fin.cons j q')) r ∈ leftCenter R := by
          intro r hr
          refine hz _ fun hcon => hr ?_
          rw [← hcon, Fin.tail_cons]
        have := ih (Fin.tail p) (fun q' => z (Fin.cons j q')) hside
        rwa [hjdef, Fin.cons_self_tail] at this
      -- One more enlargement step at the block `j`.
      have hstep := center_step hA hB hsd T hbaf j d hdC
      rw [realize_starPower_succ]
      calc min (Nat.card B) ((nbhd R (z p)).ncard + (ℓ + 1))
          = min (Nat.card B) (min (Nat.card B) ((nbhd R (z p)).ncard + ℓ) + 1) := by
            omega
        _ ≤ min (Nat.card B) ((nbhd R (d j)).ncard + 1) := by omega
        _ ≤ (nbhd R (t.realize d)).ncard := hstep

/-- **Blueprint Theorem 5.2** (Zhuk: the left center absorbs).

The star power `t ^ *(Nat.card B - 1)` of a Taylor term witnesses that the left
center of a subdirect `R ≤ A × B` absorbs `A`, provided `B` has no nonempty proper
binary absorbing subuniverse. -/
theorem leftCenter_witnesses [Finite B] [Nonempty B] (hA : IsIdempotent L A)
    (hB : IsIdempotent L B) {R : L.Substructure (A × B)} (hsd : Subdirect R)
    {k : ℕ} {t : L.Term (Fin k)} (T : IsTaylorOn (Set.univ : Set B) t)
    (hbaf : ∀ N : L.Substructure B, (N : Set B).Nonempty → (N : Set B) ≠ Set.univ →
      ¬ BinAbsorbs L (N : Set B) Set.univ) :
    Witnesses (leftCenter R) Set.univ (starPower t (Nat.card B - 1)) := by
  intro p z _ hzC
  have hcard : 1 ≤ Nat.card B := Nat.one_le_iff_ne_zero.mpr (by
    simpa using (Nat.card_pos (α := B)).ne')
  have hne : 1 ≤ (nbhd R (z p)).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr (nbhd_nonempty hsd (z p))
  have hmain := center_star hA hB hsd T hbaf (Nat.card B - 1) p z hzC
  have hfull : Nat.card B ≤ (nbhd R ((starPower t (Nat.card B - 1)).realize z)).ncard := by
    refine le_trans ?_ hmain
    omega
  -- A subset of `B` of full size is everything.
  set W : Set B := nbhd R ((starPower t (Nat.card B - 1)).realize z) with hW
  have hsub : W = Set.univ := by
    have hle : (Set.univ : Set B).ncard ≤ W.ncard := by rwa [Set.ncard_univ]
    exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hle (Set.toFinite _)
  exact nbhd_eq_univ_iff.mp hsub

end ZhukLean
