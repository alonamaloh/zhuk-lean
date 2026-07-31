# Zhuk's centers in Lean 4

A complete Lean 4 / Mathlib formalization of Zhuk's theorem on the left centre of a
subdirect relation, and its collapse to ternary absorption.

Let `A` and `B` be finite idempotent algebras of a common signature, let
`R ≤ A × B` be subdirect, and let

```
C = { a ∈ A : {a} × B ⊆ R }
```

be its *left centre*. If `B` has a Taylor term and no nonempty proper binary
absorbing subuniverse, then `C` centrally absorbs `A`, and the absorption is
witnessed by a **ternary** term. That is `zhuk_main`.

This is Zhuk's key structural lemma from the proof of the CSP dichotomy
conjecture, together with the Zhuk–Kozik essential doubling trick that forces
ternary absorption. The first half produces a witnessing term of arity
`k ^ (|B| - 1)`; the second half does not compress that term, but shows no ternary
essential relation can exist, from which the relational description of absorption
yields the *existence* of a ternary witness.

The prose blueprint this follows, with full proofs and a bibliography, is at
<https://github.com/alonamaloh/csp-zhuk-centers>. Statement numbers below refer to
it.

Lean 4.32.2, Mathlib v4.32.2. `lake build`; warm builds are ~2 s.

## Status

**Complete and `sorry`-free** — every theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.

| Blueprint | Lean |
|---|---|
| Def 1.3 idempotence | `IsIdempotent` |
| Lemma 1.7 singletons | `IsIdempotent.closedUnder_singleton` |
| Lemma 1.13 term ops idempotent | `IsIdempotent.realize_const` |
| Def 1.8 products | `piStructure`, `prodStructure` |
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
| Def 4.1–4.2 subdirect, neighbourhood, left centre | `Subdirect`, `nbhd`, `leftCenter` |
| Lemma 4.3(a)–(d) | `closedUnder_nbhd`, `nbhd_nonempty`, `closedUnder_leftCenter`, `realize_mem_nbhd_realize` |
| **Theorem 5.1** the enlargement step | `center_step` |
| **Theorem 5.2** Zhuk: the left centre absorbs | `leftCenter_witnesses` |
| **Theorem 6.1** Zhuk: centrality of the left centre | `center_central` |
| Def 6.2 central absorption | `CentrallyAbsorbs` |
| **Corollary 6.3** Zhuk's centre theorem | `zhuk_center` |
| Step 1 of doubling, the generation property (‡) | `betaSet_subset_closure` |
| Step 3 of doubling, the linking relation misses `B'×B'` | `linking_disjoint` |
| **Lemma 7.1** Zhuk–Kozik essential doubling | `hasEssential_doubled` |
| **Corollary 8.1** central absorption is ternary | `exists_ternary_witnesses` |
| **Theorem 0.1** main theorem | `zhuk_main` |

## What Mathlib supplied

Most of the blueprint's Part I. `Mathlib/ModelTheory/` has `Language` (Def 1.1) and
`Term` (Def 1.9) — whose `func` constructor takes `Fin l → Term α`, so a signature
of arbitrary branching arity needs no encoding — together with `Term.subst` /
`Term.relabel` and their realize laws (Def 1.10, Lemma 1.11), `Substructure`
(Def 1.4), `Substructure.closure` (Lemma 1.6) with `closure_induction`,
`Term.realize_mem` (Lemma 1.14), and `mem_closure_iff_exists_term` (Lemma 1.15).

Mathlib has **no** product-of-structures instance — `Ultraproducts` goes straight
to the quotient via `Prestructure` — so `Product.lean` supplies the dependent and
binary products, coordinatewise realization, and reindexing and evaluation
homomorphisms. Mathlib has no CSP or universal-algebra content at all, so Parts
II and III are entirely new.

## Findings for the blueprint

Seven places where formalizing found the paper over-assuming or doing more work
than needed. None is an error; all are hypothesis weakenings or apparatus that
dissolves.

1. **Lemma 2.6 does not need `E` and `D` to be subuniverses.** The blueprint
   assumes it; the proof uses only `E ⊆ D`. `binAbsorbs_of_oneSided` assumes only
   that.
2. **Star powers do not need Euclidean division.** Indexing the variables of
   `t ^ *ℓ` by `Fin ℓ → Fin k` rather than `Fin (k ^ ℓ)` makes "block `j`, position
   `q`" into `Fin.cons j q`, and the evaluation law a two-line proof. Appendix C
   item 6 can go.
3. **Lemma 1.15 needs no enumeration.** Mathlib's `mem_closure_iff_exists_term`
   takes the variable type to *be* the generating set. The blueprint fixes a finite
   enumeration to avoid substitution bookkeeping; that is unnecessary once terms are
   polymorphic in the variable type. This also simplifies Theorem 6.1, whose
   "normal form for the generators" with `p ≤ q` exists only to index a sorted
   enumeration — classifying *variables* by which of the three generator blocks they
   lie in removes the sorting, and Lemma 1.20 (block-respecting enumeration) with
   it. `center_central` is proved with the selector `fun g => if g.2 = a then 1 else 0`
   and no enumeration anywhere.
4. **Theorem 6.1 needs neither finiteness nor a Taylor term.** The blueprint states
   it for finite idempotent `A`, `B`; the proof needs only that `B` has no nonempty
   proper binary absorbing subuniverse, plus idempotence of `A` to bundle the
   neighbourhood as a subuniverse. `center_central` assumes only that.
5. **Regrouping wants a live set, not a shrinking index type.** Stated literally,
   the blueprint's induction over "an arbitrary finite index set" changes the index
   *type* at every step, and every relation would have to be transported. Fixing an
   ambient index type with a block function `I → Fin m` and a live set
   `J : Finset I` keeps the relation still: deleting an element is `J.erase u`,
   projection becomes "stop quantifying over that coordinate", and only the base
   case transports, once. That is `hasEssential_of_essentialOn`.
6. **The doubled relation needs no coordinate reversal.** The blueprint writes `R'`
   over `A₀ × ⋯ × Aₙ × Aₙ × ⋯ × A₀`, with the second half reversed. Essentiality
   does not depend on the order of the coordinates, so `doubled` is indexed by the
   sum type `Fin (n+1) ⊕ Fin (n+1)` and the reversal disappears. Transport to
   `Fin (2n+2)` is then free: `hasEssential_of_essentialOn`'s base case *is* a
   reindexing, so regrouping doubles as the transport lemma.
7. **Remark 7.2 is load-bearing, not explanatory.** Step 1 of the doubling proof
   has to be a standalone universally quantified statement
   (`betaSet_subset_closure`) established before `b` is fixed, because Step 3
   instantiates it at `b'` and then again at the `b'''` that the first
   instantiation produced. Written in the source's order it does not typecheck.

## Frictions

- Mathlib's `ModelTheory` imports do not transitively bring in the tactic library.
  `fin_cases`, `ring` and `norm_num` are each absent until imported explicitly.
  `omega` *is* available, and handles `min`/`max` on `ℕ`, which covered every
  arithmetic obligation in the enlargement induction.
- `Structure` bundles `funMap` and `RelMap` together, so every product instance must
  supply a `RelMap` even though the signatures here are purely algebraic.
- Binder-type inference on subtype coercions: `fun g => (g : A × A).1` elaborates
  `g : A × A` rather than coercing from `↥S`. Naming the valuation fixes it.

## References

- D. Zhuk, *A proof of the CSP dichotomy conjecture*, JACM **67** (2020), no. 5,
  article 30 — the left-centre argument.
- L. Barto and A. Kazda, *Deciding absorption*, IJAC **26** (2016), no. 5,
  1033–1060 — the relational description of absorption, Part II here.
- L. Barto and M. Kozik, *Absorbing subalgebras, cyclic terms, and the constraint
  satisfaction problem*, LMCS **8** (2012), no. 1 — the absorption theorem this
  mechanism replaces.
- Z. Brady, *Notes on CSPs and polymorphisms*, arXiv:2210.07383 — where the
  argument is assembled in the form the blueprint follows.

## License

[Apache 2.0](LICENSE), matching Mathlib and the rest of the Lean ecosystem. The
companion blueprint is CC BY 4.0: a prose document, where a Creative Commons
licence is appropriate.
