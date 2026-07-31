/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the CC BY 4.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ZhukLean.Absorption
import Mathlib.Data.Set.Card

/-!
# Left centers and their neighborhoods

Blueprint Part III, Definitions 4.1–4.2 and Lemma 4.3.

Given a subdirect `R ≤ A × B`, the *neighborhood* of `a : A` is the set of `b : B`
related to it, and the *left center* is the set of `a` related to everything.

## Main definitions

* `Subdirect R` — blueprint Definition 4.1.
* `nbhd R a` — blueprint Definition 4.2, written `a + R` in the blueprint.
* `leftCenter R` — blueprint Definition 4.2.

## Main results

* `closedUnder_nbhd`, `nbhd_nonempty`, `closedUnder_leftCenter`,
  `realize_mem_nbhd_realize` — blueprint Lemma 4.3 (a), (b), (c), (d).
-/

open FirstOrder Language

namespace ZhukLean

variable {L : Language} {A B : Type*} [L.Structure A] [L.Structure B]

/-- Blueprint Definition 4.1: `R` is subdirect when both projections are onto. -/
structure Subdirect (R : L.Substructure (A × B)) : Prop where
  /-- Every element of `A` occurs as a first coordinate. -/
  fst : ∀ a : A, ∃ b : B, (a, b) ∈ R
  /-- Every element of `B` occurs as a second coordinate. -/
  snd : ∀ b : B, ∃ a : A, (a, b) ∈ R

/-- Blueprint Definition 4.2: the neighborhood `a + R`. -/
def nbhd (R : L.Substructure (A × B)) (a : A) : Set B := {b | (a, b) ∈ R}

/-- Blueprint Definition 4.2: the left center of `R`. -/
def leftCenter (R : L.Substructure (A × B)) : Set A := {a | ∀ b : B, (a, b) ∈ R}

@[simp]
theorem mem_nbhd {R : L.Substructure (A × B)} {a : A} {b : B} :
    b ∈ nbhd R a ↔ (a, b) ∈ R := Iff.rfl

@[simp]
theorem mem_leftCenter {R : L.Substructure (A × B)} {a : A} :
    a ∈ leftCenter R ↔ ∀ b : B, (a, b) ∈ R := Iff.rfl

theorem nbhd_eq_univ_iff {R : L.Substructure (A × B)} {a : A} :
    nbhd R a = Set.univ ↔ a ∈ leftCenter R := by
  constructor
  · intro h b
    have : b ∈ nbhd R a := h ▸ Set.mem_univ b
    exact this
  · intro h
    exact Set.eq_univ_of_forall fun b => h b

/-! ## Blueprint Lemma 4.3 -/

/-- Lemma 4.3(a): each neighborhood is a subuniverse of `B`.

Idempotence of `A` is what lets the first coordinate stay put. -/
theorem closedUnder_nbhd (hA : IsIdempotent L A) (R : L.Substructure (A × B)) (a : A)
    {n : ℕ} (f : L.Functions n) : ClosedUnder f (nbhd R a) := by
  intro x hx
  have hmem : ∀ i, ((a, x i) : A × B) ∈ R := fun i => hx i
  have hR : Structure.funMap f (fun i => ((a, x i) : A × B)) ∈ R := R.fun_mem f _ hmem
  have hsplit : Structure.funMap f (fun i => ((a, x i) : A × B))
      = (Structure.funMap f fun _ => a, Structure.funMap f x) := rfl
  rw [hsplit, hA f a] at hR
  exact hR

/-- Lemma 4.3(b): neighborhoods are nonempty, by subdirectness. -/
theorem nbhd_nonempty {R : L.Substructure (A × B)} (h : Subdirect R) (a : A) :
    (nbhd R a).Nonempty := by
  obtain ⟨b, hb⟩ := h.fst a
  exact ⟨b, hb⟩

/-- Lemma 4.3(c): the left center is a subuniverse of `A`.

Idempotence of `B` is what lets the second coordinate stay put. -/
theorem closedUnder_leftCenter (hB : IsIdempotent L B) (R : L.Substructure (A × B))
    {n : ℕ} (f : L.Functions n) : ClosedUnder f (leftCenter R) := by
  intro x hx b
  have hmem : ∀ i, ((x i, b) : A × B) ∈ R := fun i => hx i b
  have hR : Structure.funMap f (fun i => ((x i, b) : A × B)) ∈ R := R.fun_mem f _ hmem
  have hsplit : Structure.funMap f (fun i => ((x i, b) : A × B))
      = (Structure.funMap f x, Structure.funMap f fun _ => b) := rfl
  rw [hsplit, hB f b] at hR
  exact hR

/-- Lemma 4.3(d): preservation. If each `y j` lies in the neighborhood of `z j`, then
the value of a term at `y` lies in the neighborhood of its value at `z`. -/
theorem realize_mem_nbhd_realize {R : L.Substructure (A × B)} {α : Type*}
    (t : L.Term α) (z : α → A) (y : α → B) (h : ∀ a, y a ∈ nbhd R (z a)) :
    t.realize y ∈ nbhd R (t.realize z) := by
  have hpair : ∀ a, ((z a, y a) : A × B) ∈ R := h
  have := t.realize_mem (fun a => ((z a, y a) : A × B)) hpair
  rwa [realize_prod] at this

/-- The neighborhood, bundled as a substructure of `B`. -/
def nbhdSub (hA : IsIdempotent L A) (R : L.Substructure (A × B)) (a : A) : L.Substructure B where
  carrier := nbhd R a
  fun_mem := closedUnder_nbhd hA R a

@[simp]
theorem coe_nbhdSub (hA : IsIdempotent L A) (R : L.Substructure (A × B)) (a : A) :
    (nbhdSub hA R a : Set B) = nbhd R a := rfl

/-- The left center, bundled as a substructure of `A`. -/
def leftCenterSub (hB : IsIdempotent L B) (R : L.Substructure (A × B)) : L.Substructure A where
  carrier := leftCenter R
  fun_mem := closedUnder_leftCenter hB R

@[simp]
theorem coe_leftCenterSub (hB : IsIdempotent L B) (R : L.Substructure (A × B)) :
    (leftCenterSub hB R : Set A) = leftCenter R := rfl

/-- The left center is closed under term operations: blueprint Lemma 4.3(c) combined
with preservation. -/
theorem realize_mem_leftCenter (hB : IsIdempotent L B) {R : L.Substructure (A × B)}
    {α : Type*} (t : L.Term α) (z : α → A) (hz : ∀ a, z a ∈ leftCenter R) :
    t.realize z ∈ leftCenter R :=
  t.realize_mem (S := leftCenterSub hB R) z hz

/-- The left center is exactly the set of elements whose neighborhood is everything. -/
theorem leftCenter_eq {R : L.Substructure (A × B)} :
    leftCenter R = {a | nbhd R a = Set.univ} := by
  ext a
  exact nbhd_eq_univ_iff.symm

end ZhukLean
