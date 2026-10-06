# Subtyping in kernel D<: with bad bounds is decidable

D<: is the fragment of DOT, the calculus behind Scala's type system, with type members and
path-dependent types. Hu and Lhoták ("Undecidability of D<: and Its Decidable Fragments",
POPL 2020) proved subtyping in D<: undecidable and identified decidable fragments, among them
*kernel* D<:, whose rule for function types compares result types only under identical
parameter types. They left open whether kernel D<: stays decidable when the *bad bounds*
rule is added back (if the type of a variable `x` has a member with lower bound `S` and one
with upper bound `U`, then `S <: U`), and conjectured that it does not (§7.1). This
repository contains a machine-checked proof, in Lean 4 with Mathlib, that it does.

## What is proved

```lean
theorem Dsub.decidable : ComputablePred Dsub.Subtyping
```

stated in `Resolution.lean` and proved via `Dsub.subtyping_computable` in
`Resolution/Final.lean`. The definitions of types, contexts and the subtyping rules, together
with the numbering of judgments that fixes what "computable" means, are in
`Dsub/Basic.lean` and take 227 lines. The proof takes about 5,300 lines. It is kernel-checked,
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`, and contains no `sorry`
and no `native_decide`.

As a side result, `Dsub.Sub.trans` in `Resolution/Trans.lean` shows that transitivity is
admissible, so the result holds equally for kernel D<: with both transitivity and bad
bounds.

## The argument

Every goal in a derivation has the form `P <: Dᵏ(V)` with `D(W) = {A : ⊥..W}`; within a fixed
context the counter `k` is resolved by saturating two finite relations. Contexts grow only
through the kernel rule for function types. The variables it creates form a forest of depth
at most the `∀`-nesting depth of the input, and the two sides of a goal share only a chain of
them. Two isomorphic sibling subtrees that the goal does not mention can be removed without
changing derivability, and once none can be removed the number of created variables is
bounded by a tower of exponentials. So only finitely many contexts matter, and saturation
over all of them decides subtyping. `PROOF.md` gives the argument in full.

## Structure of the proof

The modules under `Resolution/`, in dependency order:

| Module | Content |
| --- | --- |
| `Syntax` | Renamings, nested declarations `Dᵏ`, context morphisms. |
| `Lemmas` | Subtyping is preserved by renaming along context morphisms. |
| `Height` | Derivations with a height bound, `SubH`. |
| `Rules` | The rules of saturation within one context (judgments and summaries) and their soundness. |
| `Thin` | Occurrences, `∀`-nesting depth, removing variables from a context. |
| `Annot` | Annotations, the invariant `Inv`, and its backward preservation (PROOF.md §2, Lemma 2). |
| `Collapse` | Collapses; removing one is exact, with heights (§3, Lemma 3). |
| `Counts` | The numbers of variables of a type, of created and of base variables. |
| `Family`, `FamilyEnum` | Saturation over a finite family of contexts with the kernel rule; completeness; the family `Φ L s` of all bounded contexts. |
| `Sized` | The size part of the invariant. |
| `Good`, `NormFam` | Normalisation by removing collapses, given Lemma 4; the conditions of completeness for `Φ`. |
| `BoundCode`, `Bound`, `BoundPrim` | Lemma 4 (§4): an irreducible state has at most `Bnd N s n₀` created variables; `Bnd` is primitive recursive. |
| `PrimBasic`, `PrimFix`, `PrimCodes`, `PrimCtx` | Codes of types, contexts and judgments; primitive recursive operations on them; least fixpoints over a finite universe of codes. |
| `PrimFires`, `PrimDecide` | The rule check on codes, and saturation on codes, sound and complete for `Φ`. |
| `Final` | Bounds read off the input code, and the final assembly. |
| `Trans` | Admissibility of transitivity (not used by the main theorem). |

## Building

The project uses Lean `v4.34.0` and Mathlib `v4.34.0` (see `lean-toolchain` and
`lake-manifest.json`). With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
scripts/check-axioms.sh
```

The last command runs `lake env lean Check.lean` and fails unless the output is exactly

```
'Dsub.decidable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dsub.Sub.trans' depends on axioms: [propext, Quot.sound]
```

The GitHub Actions workflow in `.github/workflows/build.yml` does all three on every push.

## Provenance

The proof was found and written by Claude Opus 5.5 (Anthropic) on 6–7 October 2026, in an
interactive Claude Code session with Yichen Xu, who chose the problem, asked for the calculus
to be formalised, and then asked for a proof of either decidability or undecidability,
without mathematical guidance. The model first attempted an undecidability construction, found why
it fails, and turned that obstruction into the decidability argument. Parts of the Lean proof
were written by subagents, further instances of the same model working from briefs.

The first commit of this repository is the session's output unchanged. The second removes
declarations and two modules that the main theorem does not use, renames the module
`Decide` to `Rules`, rewrites comments, and replaces a deprecated lemma name; it changes no
statement, and no proof beyond that rename.

## Authors

Claude Opus 5.5 and Yichen Xu.

## License

Apache 2.0; see `LICENSE`.
