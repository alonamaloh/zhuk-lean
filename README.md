# Zhuk's centers in Lean 4

A Lean 4 / Mathlib formalization of the blueprint at
`~/claude/zeb/zhuk_centers.tex` (also at
<https://github.com/alonamaloh/csp-zhuk-centers>), built as a comparison point for
the same development in `~/claude/math/` — see `PLAN_ZHUK_CENTERS.md` there.

Lean 4.32.2, Mathlib v4.32.2. `lake build`; warm builds are ~2 s.

## Status

**Proved, `sorry`-free** (every theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`):

| Blueprint | Lean |
|---|---|
| Def 1.3 idempotence | `IsIdempotent` |
| Lemma 1.7 singletons | `IsIdempotent.closedUnder_singleton` |
| Lemma 1.13 term ops idempotent | `IsIdempotent.realize_const` |
| Def 1.8 products (Layer 2 of the plan) | `piStructure`, `prodStructure` |
| Lemma 1.19(c),(e) projection/reindexing | `reindexHom`, `evalHom` |
| Def 2.1 absorption (tuple form) | `Witnesses`, `Absorbs`, `BinAbsorbs` |
| Def 2.4 Taylor identities | `TaylorAt`, `IsTaylorOn` |
| **Lemma 2.6** one-sided ⟹ binary absorption | `binAbsorbs_of_oneSided` |
| Def 2.7 star powers | `starPower`, `realize_starPower_succ` |
| Def 3.1 essential relations | `IsEssential` |
| **Prop 3.5** absorption forbids essential relations | `not_isEssential_of_witnesses` |
| Prop 3.4 arity reduction | `hasEssential_of_succ`, `hasEssential_of_le` |
| Cor 3.6 absorption bounds essential arity | `not_hasEssential_of_witnesses` |
| Def 3.2 essential for a partition | `IsEssentialOn` |
| **Lemma 3.7** regrouping | `hasEssential_of_essentialOn` |
| Lemma 3.9 the algebra of `m`-ary term operations | `termOps` |
| **Theorem 3.10** relational description (Barto–Kazda) | `exists_witnesses_of_not_hasEssential` |
| Def 4.1–4.2 subdirect, neighborhood, left center | `Subdirect`, `nbhd`, `leftCenter` |
| Lemma 4.3(a)–(d) | `closedUnder_nbhd`, `nbhd_nonempty`, `closedUnder_leftCenter`, `realize_mem_nbhd_realize` |
| **Theorem 5.1** the enlargement step | `center_step` |
| **Theorem 5.2** Zhuk: the left center absorbs | `leftCenter_witnesses` |
| **Theorem 6.1** Zhuk: centrality of the left center | `center_central` |
| Def 6.2 central absorption | `CentrallyAbsorbs` |
| **Corollary 6.3** Zhuk's center theorem | `zhuk_center` |
| Step 1 of doubling, the generation property (‡) | `betaSet_subset_closure` |
| Step 3 of doubling, the linking relation misses `B'×B'` | `linking_disjoint` |
| **Lemma 7.1** Zhuk–Kozik essential doubling | `hasEssential_doubled` |
| **Corollary 8.1** central absorption is ternary | `exists_ternary_witnesses` |
| **Theorem 0.1** main theorem | `zhuk_main` |

**The blueprint is fully formalized.** Every numbered statement of
`zhuk_centers.tex` that carries mathematical content has a Lean counterpart, and
`zhuk_main` is blueprint Theorem 0.1.

## What Mathlib supplied

Most of the blueprint's Part I. `Mathlib/ModelTheory/` has `Language` (Def 1.1),
`Term` (Def 1.9) — whose `func` constructor is `(Fin l → Term α) → Term α`, the
function-typed recursive argument that `PLAN_ZHUK_CENTERS.md` calls the M0 gate —
`Term.subst` / `Term.relabel` with their realize laws (Def 1.10, Lemma 1.11),
`Substructure` (Def 1.4), `Substructure.closure` (Lemma 1.6) with
`closure_induction`, `Term.realize_mem` (Lemma 1.14), and
`mem_closure_iff_exists_term` (Lemma 1.15).

Mathlib has **no** product-of-structures instance — `Ultraproducts` goes straight
to the quotient via `Prestructure`. That is Layer 2 of the plan, and `Product.lean`
supplies it. Mathlib has no CSP or universal-algebra content at all: Parts II–III
are entirely new.

## Findings for the blueprint

Three places where formalizing found the blueprint over-assuming or over-working.
None is an error; all are simplifications.

1. **Lemma 2.6 does not need `E` and `D` to be subuniverses.** The blueprint
   assumes it; the proof uses only `E ⊆ D`. `binAbsorbs_of_oneSided` assumes only
   that.
2. **Star powers do not need Euclidean division.** Indexing the variables of
   `t ^ *ℓ` by `Fin ℓ → Fin k` rather than `Fin (k ^ ℓ)` makes "block `j`, position
   `q`" into `Fin.cons j q`, and the evaluation law a two-line proof. This confirms
   the proposal in Layer 4 of the plan and would delete Appendix C item 6.
3. **Lemma 1.15 needs no enumeration.** Mathlib's `mem_closure_iff_exists_term`
   takes the variable type to *be* the generating set. The blueprint fixes a finite
   enumeration to avoid substitution bookkeeping; that is unnecessary once terms are
   polymorphic in the variable type. This would also simplify Theorem 6.1, whose
   "normal form for the generators" with `p ≤ q` exists only to index a sorted
   enumeration — classifying *variables* by which of the three generator blocks they
   lie in removes the sorting, and Lemma 1.20 (block-respecting enumeration) with it.
   **Confirmed**: `center_central` is proved with the selector
   `fun g => if g.2 = a then 1 else 0` and no enumeration anywhere.
4. **Theorem 6.1 needs neither finiteness nor a Taylor term.** The blueprint states
   it for finite idempotent `A`, `B`; the proof needs only that `B` has no nonempty
   proper binary absorbing subuniverse, plus idempotence of `A` to bundle the
   neighborhood as a subuniverse. `center_central` assumes only that.

5. **The live-set encoding of regrouping works.** Stated literally, the blueprint's
   induction over "an arbitrary finite index set" changes the index *type* at every
   step. Fixing an ambient index type with a block function `I → Fin m` and a live
   set `J : Finset I` — the plan's proposal — keeps the relation put; deleting an
   element is `J.erase u`, projection becomes "stop quantifying over that
   coordinate", and only the base case transports, once. `hasEssential_of_essentialOn`
   is proved that way.

6. **The doubled relation needs no coordinate reversal.** The blueprint writes `R'`
   over `A₀ × ⋯ × Aₙ × Aₙ × ⋯ × A₀`, with the second half reversed. Essentiality
   does not depend on the order of the coordinates, so `doubled` is indexed by the
   sum type `Fin (n+1) ⊕ Fin (n+1)` and the reversal disappears. Transport to
   `Fin (2n+2)` is then free: `hasEssential_of_essentialOn`'s base case *is* a
   reindexing, so regrouping doubles as the transport lemma.
7. **Remark 7.2 is right, and load-bearing.** Step 1 has to be a standalone
   universally quantified statement (`betaSet_subset_closure`) proved before `b` is
   fixed, because Step 3 instantiates it at `b'` and then again at the `b'''` that
   the first instantiation produced. Formalized in the source's order it would not
   typecheck.

## Frictions

- Mathlib's `ModelTheory` imports do not transitively bring in the tactic library;
  `fin_cases` needed `import Mathlib.Tactic.FinCases` explicitly.
- `Structure` bundles `funMap` and `RelMap` together, so every product instance must
  supply a `RelMap` even though the blueprint's signatures are purely algebraic.
- Tactic imports keep biting: `fin_cases`, `ring` and `norm_num` are each absent
  until imported. `omega` is available and handles `min`/`max` on `ℕ`, which covered
  every arithmetic obligation in the enlargement induction.
- Binder-type inference on subtype coercions: `fun g => (g : A × A).1` elaborates
  `g : A × A` rather than coercing from `↥S`. Naming the valuation fixes it.

## License

[Apache 2.0](LICENSE), matching Mathlib and the rest of the Lean ecosystem. Note
that the companion blueprint at <https://github.com/alonamaloh/csp-zhuk-centers>
is CC BY 4.0: a prose document, where a Creative Commons licence is appropriate.
