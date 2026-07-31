/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ZhukLean.Regrouping

/-!
# The relational description of absorption

Blueprint Lemma 3.9 and Theorem 3.10 (Barto–Kazda). `S` absorbs `A` with respect to
an `m`-ary term precisely when there is no `S`-essential relation of arity `m`.

The forward direction is `not_isEssential_of_witnesses`. The converse runs the
algebra of `m`-ary term operations against the regrouping lemma: the relation is
the set of term operations restricted to the tuples with exactly one coordinate
outside `S`, and the blocks are indexed by *which* coordinate that is.
-/

open FirstOrder Language

namespace ZhukLean

variable {L : Language} {M : Type*} [L.Structure M]

/-- Blueprint Lemma 3.9: the `m`-ary term operations form a subuniverse of the power
`M ^ (M ^ m)`, containing the projections. -/
def termOps (L : Language) (M : Type*) [L.Structure M] (m : ℕ) :
    L.Substructure ((Fin m → M) → M) where
  carrier := Set.range fun t : L.Term (Fin m) => fun x : Fin m → M => t.realize x
  fun_mem := by
    intro n f ts hts
    choose g hg using hts
    refine ⟨Term.func f g, ?_⟩
    funext x
    have hx : ∀ i, ts i x = (g i).realize x := fun i => congrFun (hg i).symm x
    simp only [Term.realize, funMap_pi]
    exact congrArg _ (funext fun i => (hx i).symm)

theorem mem_termOps {m : ℕ} {p : (Fin m → M) → M} :
    p ∈ termOps L M m ↔ ∃ t : L.Term (Fin m), (fun x => t.realize x) = p := Iff.rfl

theorem proj_mem_termOps {m : ℕ} (i : Fin m) :
    (fun x : Fin m → M => x i) ∈ termOps L M m := ⟨var i, rfl⟩

/-- **Blueprint Theorem 3.10** (Barto–Kazda), the substantial direction.

If there is no `S`-essential relation of arity `m`, then some `m`-ary term witnesses
`S ⊴ A`. -/
theorem exists_witnesses_of_not_hasEssential [Finite M] {S : L.Substructure M} {m : ℕ}
    (hm : 0 < m) (h : ¬ HasEssential L (S : Set M) m) :
    ∃ t : L.Term (Fin m), Witnesses (S : Set M) Set.univ t := by
  classical
  have : Fintype M := Fintype.ofFinite M
  -- The live coordinates: tuples with exactly one entry outside `S`.
  set X : Finset (Fin m → M) :=
    Finset.univ.filter (fun x => ∃ i, x i ∉ S ∧ ∀ j, j ≠ i → x j ∈ S) with hX
  -- The block of a live tuple is the coordinate that escapes `S`.
  set block : (Fin m → M) → Fin m :=
    fun y => if hy : ∃ i, y i ∉ (S : Set M) then hy.choose else ⟨0, hm⟩ with hblock
  have hblock_spec : ∀ y ∈ X, ∀ i, block y ≠ i → y i ∈ S := by
    intro y hy i hne
    obtain ⟨i₀, hi₀, hrest⟩ := (Finset.mem_filter.mp hy).2
    have hex : ∃ i, y i ∉ (S : Set M) := ⟨i₀, hi₀⟩
    have hchoose : y hex.choose ∉ (S : Set M) := hex.choose_spec
    have : block y = i₀ := by
      rw [hblock]
      simp only [dif_pos hex]
      by_contra hcon
      exact hchoose (hrest _ hcon)
    exact hrest i (fun hcon => hne (this.trans hcon.symm))
  -- Condition (B1) holds, witnessed by the projections.
  have hB1 : ∀ j : Fin m, ∃ p ∈ termOps L M m, ∀ y ∈ X, block y ≠ j → p y ∈ (S : Set M) := by
    intro j
    exact ⟨_, proj_mem_termOps j, fun y hy hne => hblock_spec y hy j hne⟩
  -- So (B2) must fail, else regrouping would produce an essential relation of arity `m`.
  have hnotess : ¬ IsEssentialOn (S : Set M) X block (termOps L M m) := fun hess =>
    h (hasEssential_of_essentialOn X.card X block (termOps L M m) rfl hess)
  have hB2 : ∃ p ∈ termOps L M m, ∀ y ∈ X, p y ∈ (S : Set M) := by
    by_contra hcon
    push Not at hcon
    refine hnotess ⟨hB1, fun p hp hall => ?_⟩
    obtain ⟨y, hy, hny⟩ := hcon p hp
    exact hny (hall y hy)
  obtain ⟨p, ⟨t, rfl⟩, hp⟩ := hB2
  -- The term found is a witness.
  refine ⟨t, fun i z _ hzS => ?_⟩
  by_cases hzi : z i ∈ (S : Set M)
  · exact t.realize_mem z fun j => by
      by_cases hj : j = i
      · exact hj ▸ hzi
      · exact hzS j hj
  · refine hp z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, hzi, fun j hj => hzS j hj⟩⟩)

end ZhukLean
