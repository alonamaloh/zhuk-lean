/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the CC BY 4.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ZhukLean.Absorption
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Star powers

Blueprint Definition 2.7. The blueprint gives `t ^ *ℓ` arity `k ^ ℓ` and decomposes
an index `p ∈ [k ^ (ℓ+1)]` as `p = (j-1) * k ^ ℓ + q` by Euclidean division.

`PLAN_ZHUK_CENTERS.md` proposes instead indexing the variables of `t ^ *ℓ` by the
type `Fin ℓ → Fin k`, which has `k ^ ℓ` elements. Then "block `j`, position `q`"
is just `Fin.cons j q` — peeling off the first argument of a function — and the
division disappears. This file is the test of that claim.
-/

open FirstOrder Language

namespace ZhukLean

variable {L : Language} {M : Type*} [L.Structure M]

/-- Blueprint Definition 2.7, with variables indexed by `Fin ℓ → Fin k` rather than
by `Fin (k ^ ℓ)`. -/
def starPower {k : ℕ} (t : L.Term (Fin k)) : (ℓ : ℕ) → L.Term (Fin ℓ → Fin k)
  | 0 => var Fin.elim0
  | ℓ + 1 => t.subst fun j => (starPower t ℓ).relabel fun q => Fin.cons j q

@[simp]
theorem starPower_zero {k : ℕ} (t : L.Term (Fin k)) :
    starPower t 0 = var Fin.elim0 := rfl

theorem starPower_succ {k ℓ : ℕ} (t : L.Term (Fin k)) :
    starPower t (ℓ + 1) = t.subst fun j => (starPower t ℓ).relabel fun q => Fin.cons j q := rfl

/-- The evaluation law for a star power: the outer term is applied to the values of
the previous star power on each block, where the blocks are indexed by the first
argument. This is the shape the induction of blueprint Theorem 5.2 consumes. -/
@[simp]
theorem realize_starPower_succ {k ℓ : ℕ} (t : L.Term (Fin k))
    (z : (Fin (ℓ + 1) → Fin k) → M) :
    (starPower t (ℓ + 1)).realize z
      = t.realize fun j => (starPower t ℓ).realize fun q => z (Fin.cons j q) := by
  rw [starPower_succ, Term.realize_subst]
  simp [Term.realize_relabel, Function.comp_def]

@[simp]
theorem realize_starPower_zero {k : ℕ} (t : L.Term (Fin k)) (z : (Fin 0 → Fin k) → M) :
    (starPower t 0).realize z = z Fin.elim0 := rfl

end ZhukLean
