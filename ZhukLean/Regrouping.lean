/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ZhukLean.Essential

/-!
# Regrouping

Blueprint Definition 3.2 and Lemma 3.7.

## The encoding

The blueprint states essentiality for a partition of an arbitrary finite index set
`I` into `m` nonempty blocks, and the induction shrinks an oversized block by
deleting one of its elements. Formalized literally that would change the index
*type* at every step (`I` becomes `{i // i ≠ u}`), and every relation would have to
be transported.

We use instead a *block function* `block : I → Fin m` together with a **live
set** `J : Finset I`. The ambient index type is fixed, the
relation never moves, and deleting an element is `J.erase u`. Projection in the
blueprint's sense becomes "stop quantifying over that coordinate", and the
blueprint's `R ∩ {x : x u ∈ S}` is the only relation ever formed.

Only the base case transports, once, along a choice of block representatives.
-/

open FirstOrder Language

namespace ZhukLean

variable {L : Language} {M : Type*} [L.Structure M]

/-- Blueprint Definition 3.2, in the live-set encoding: `R` is `S`-essential for the
blocks of `block`, as seen through the live coordinates `J`. -/
structure IsEssentialOn (S : Set M) {I : Type*} {m : ℕ} (J : Finset I) (block : I → Fin m)
    (R : L.Substructure (I → M)) : Prop where
  /-- (B1): for each block, a tuple of `R` lying in `S` at every live coordinate
  outside that block. -/
  witness : ∀ j : Fin m, ∃ x ∈ R, ∀ i ∈ J, block i ≠ j → x i ∈ S
  /-- (B2): no tuple of `R` lies in `S` at every live coordinate. -/
  no_full : ∀ x ∈ R, ¬ ∀ i ∈ J, x i ∈ S

/-- Every block meets the live set: otherwise its (B1) witness would violate (B2). -/
theorem IsEssentialOn.exists_mem {S : Set M} {I : Type*} {m : ℕ} {J : Finset I}
    {block : I → Fin m} {R : L.Substructure (I → M)} (h : IsEssentialOn S J block R)
    (j : Fin m) : ∃ i ∈ J, block i = j := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxR, hxS⟩ := h.witness j
  exact h.no_full x hxR fun i hi => hxS i hi (hcon i hi)

/-- **Blueprint Lemma 3.7** (regrouping).

An `S`-essential relation for a partition into `m` blocks yields an `S`-essential
relation of arity `m`. The induction is on the size of the live set; an oversized
block is shrunk in place, with no reordering. -/
theorem hasEssential_of_essentialOn {S : L.Substructure M} {I : Type*} {m : ℕ} :
    ∀ (n : ℕ) (J : Finset I) (block : I → Fin m) (R : L.Substructure (I → M)),
      J.card = n → IsEssentialOn (S : Set M) J block R → HasEssential L (S : Set M) m := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro J block R hcard hess
    by_cases hinj : ∀ i ∈ J, ∀ i' ∈ J, block i = block i' → i = i'
    · -- Base case: `block` is injective on the live set, so the blocks are singletons.
      choose g hgJ hgb using hess.exists_mem
      refine ⟨R.map (reindexHom g), ?_, ?_⟩
      · intro i
        obtain ⟨x, hxR, hxS⟩ := hess.witness i
        refine ⟨x ∘ g, ⟨x, hxR, rfl⟩, fun j hj => ?_⟩
        exact hxS (g j) (hgJ j) (by rw [hgb j]; exact hj)
      · rintro _ ⟨x, hxR, rfl⟩ hall
        refine hess.no_full x hxR fun i hi => ?_
        have : i = g (block i) := hinj i hi (g (block i)) (hgJ _) (hgb _).symm
        rw [this]
        exact hall (block i)
    · -- Inductive case: some block has two live elements.
      push Not at hinj
      obtain ⟨u, hu, u', hu', hbeq, hne⟩ := hinj
      set j₀ : Fin m := block u with hj₀
      by_cases hdag : ∃ x ∈ R, x u ∈ S ∧ ∀ i ∈ J, block i ≠ j₀ → x i ∈ S
      · -- Shrink the block: confine `u` to `S` and drop it from the live set.
        refine ih (J.erase u).card ?_ (J.erase u) block (R ⊓ S.comap (evalHom u)) rfl ?_
        · rw [Finset.card_erase_of_mem hu, ← hcard]
          exact Nat.pred_lt (by simpa [hcard] using Finset.card_ne_zero_of_mem hu)
        · constructor
          · intro j
            by_cases hjj : j = j₀
            · obtain ⟨x, hxR, hxu, hxS⟩ := hdag
              exact ⟨x, ⟨hxR, hxu⟩, fun i hi hb =>
                hxS i (Finset.mem_of_mem_erase hi) (hjj ▸ hb)⟩
            · obtain ⟨x, hxR, hxS⟩ := hess.witness j
              refine ⟨x, ⟨hxR, hxS u hu (by rw [← hj₀]; exact fun h => hjj h.symm)⟩, ?_⟩
              exact fun i hi hb => hxS i (Finset.mem_of_mem_erase hi) hb
          · rintro x ⟨hxR, hxu⟩ hall
            refine hess.no_full x hxR fun i hi => ?_
            by_cases hiu : i = u
            · exact hiu ▸ hxu
            · exact hall i (Finset.mem_erase.mpr ⟨hiu, hi⟩)
      · -- Collapse the block to the single coordinate `u`.
        push Not at hdag
        refine ih (insert u (J.filter (fun i => block i ≠ j₀))).card ?_ _ block R rfl ?_
        · refine lt_of_lt_of_le (Finset.card_lt_card ?_) (le_of_eq hcard)
          refine ⟨?_, ?_⟩
          · intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi'
            · exact hu
            · exact Finset.mem_of_mem_filter _ hi'
          · intro hsub
            have : u' ∈ insert u (J.filter (fun i => block i ≠ j₀)) := hsub hu'
            rcases Finset.mem_insert.mp this with rfl | hbad
            · exact hne rfl
            · exact (Finset.mem_filter.mp hbad).2 hbeq.symm
        · constructor
          · intro j
            by_cases hjj : j = j₀
            · obtain ⟨x, hxR, hxS⟩ := hess.witness j
              refine ⟨x, hxR, fun i hi hb => ?_⟩
              rcases Finset.mem_insert.mp hi with rfl | hi'
              · exact absurd (hjj ▸ hj₀.symm) hb
              · exact hxS i (Finset.mem_of_mem_filter _ hi') hb
            · obtain ⟨x, hxR, hxS⟩ := hess.witness j
              refine ⟨x, hxR, fun i hi hb => ?_⟩
              rcases Finset.mem_insert.mp hi with rfl | hi'
              · exact hxS i hu hb
              · exact hxS i (Finset.mem_of_mem_filter _ hi') hb
          · intro x hxR hall
            obtain ⟨i, hi, hb, hnot⟩ := hdag x hxR (hall u (Finset.mem_insert_self _ _))
            exact hnot (hall i (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hi, hb⟩)))

end ZhukLean
