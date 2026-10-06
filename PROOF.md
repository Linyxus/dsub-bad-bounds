# Subtyping in kernel D<: with bad bounds is decidable: the informal proof

The calculus is that of `Dsub/Basic.lean`, with the rules top, bot, refl_sel, bnd, all (the
kernel rule: identical parameter types), sel_lower, sel_upper and bad_bounds. Subtyping is
preserved by renaming along context morphisms (`Sub.rename`). The Lean development follows
this text; the module comments refer to its sections, and `README.md` maps them to modules.

Notation: `D(W) = {A:⊥..W}`, `Dᵏ` its iterate. `ν(T)` is the ∀-nesting depth of `T`
(`ν(∀(x:S)T) = max(ν S, 1 + ν T)`, `ν({A:S..U}) = max(ν S, ν U)`, `0` on atoms). `occ(T)`
is the set of variables occurring in `T`.

## 1. Setting

Fix an input `Γ₀ ⊢ S₀ <: U₀` with `Γ₀ : Ctx n₀`. Let `𝒮` be the set of all renamings of
subterms of `S₀`, `U₀` and the types of `Γ₀` (any scope), and `N = max ν` over `𝒮`
(= the ∀-nesting depth of the input).

A **state** is a goal `Γ ⊢ P <: Dᵏ(V)` where `Γ = Γ₀ , z₁:T₁ , … , z_m:T_m`
(the `zᵢ` are *created* variables, appended by the kernel rule), with
`P ∈ 𝒮 ∪ {⊤,⊥}` and `V ∈ 𝒮 ∪ {⊤,⊥} ∪ {{A:P'..⊤} : P' ∈ 𝒮 ∪ {⊤,⊥}}`.
The two **terms** of the state are `P` and `V̂`, where `V̂ = P'` if `V = {A:P'..⊤}` and
`V̂ = V` otherwise.

**Lemma 1 (shapes).** Every premise of a rule whose conclusion is a state is a state, and
its two terms are: (a) a sub-term of one old term and a sub-term of the other old term
(rules bnd, all — the contravariant premise of bnd swaps sides but still takes one sub-term
from each), or (b) a lookup `Γ(x)` and one of the old terms, unchanged (sel_lower,
sel_upper, both premises of BB), or (c) trivial (`⊥` on the left). The all rule applies
only at `k = 0` and is the only rule that changes the context. (Inspection; the `k ≥ 1`
case is an inversion of the rules.)

All types occurring in states are in `𝒮 ∪ {⊤,⊥}` or of the form `Dᵏ`/`{A:·..⊤}` around
them; in particular every context type `Tᵢ` is in `𝒮` (a parameter type of an entered
`∀` is a subterm of a term in `𝒮`).

## 2. Annotated states and the invariant

An **annotation** of a state is a partial map `par` from created variables to created
variables with `par(z)` created before `z`, i.e. a forest on the created variables. Write
`x ⊏ z` for "x is a proper ancestor of z", `δ(z)` for the depth of `z` (roots: 1), and say
`x`, `x'` are *related* if one is an ancestor of the other or they are equal.

**Invariant `I`** of an annotated state:

- (I1) every created variable's type mentions only base variables and its own proper
  ancestors;
- (I2) for every created `x` and every type `T` among the two terms and the context types:
  if `x ∈ occ(T)` then `ν(T) + δ(x) ≤ N`;
- (I3) for unrelated created `x`, `x'`, it is not the case that both terms mention both;
- (I4) `δ(x) ≤ N` for every created `x`.

The root state (no created variables, empty annotation) satisfies `I`.

**Lemma 2 (backward preservation).** If a state satisfies `I` and a rule concludes it, then
every premise satisfies `I`, with the same annotation, except for the all rule, whose
premise gets `par(z) =` the deepest created variable occurring in both terms of the
conclusion (none if there is none).

Proof.
- Premises of kind (a): each term's `occ` is contained in an old term's `occ` and `ν` does
  not increase, so (I2), (I3) are inherited; the context is unchanged.
- Kind (b): the new term `Γ(x)` mentions only a chain of related variables (I1), so it
  cannot take part in a violation of (I3); (I2) for `Γ(x)` holds because it is a context
  type.
- The all rule, conclusion `Γ ⊢ ∀(y:S)B <: ∀(y:S)B'` (k = 0), premise
  `Γ, z:S ⊢ B <: B'`:
  - The created variables occurring in both `∀(y:S)B` and `∀(y:S)B'` are pairwise related
    (I3), hence form a chain; let `p` be its deepest element, `par(z) = p`.
  - (I1) for `z`: `occ(S) ⊆ occ(∀(y:S)B) ∩ occ(∀(y:S)B')`, i.e. that chain, i.e. ancestors
    of `z`.
  - (I2): types mentioning `z` are the bodies, with `ν(B) ≤ ν(∀(y:S)B) − 1`. If `p` exists,
    `ν(∀(y:S)B) + δ(p) ≤ N` by (I2) for `p`, so `ν(B) + δ(z) ≤ N`. If not, `δ(z) = 1` and
    `ν(B) + 1 ≤ ν(∀(y:S)B) ≤ N`. For other `x` occurring in a body, `ν(B) ≤ ν(∀…)`.
  - (I3): a pair `(x, z)` with both bodies mentioning `x` means `x` occurs in both
    conclusion terms, so `x` is an ancestor of `z`. Pairs of old variables: `occ` of the
    bodies is that of the conclusion terms plus `z`.
  - (I4): `δ(z) = δ(p) + 1 ≤ N − ν(∀(y:S)B) + 1 ≤ N`, since `ν(∀…) ≥ 1`. ∎

So every state in a derivation of the root (read top-down) has an annotation satisfying
`I`. Note that `I` constrains states only; it is not part of the rules.

## 3. Collapse is exact

A **collapse** of a state `Γ ⊢ J` is a non-empty set `X` of created variables such that:
- (C1) `J` mentions no variable of `X`;
- (C2) no variable outside `X` has a type mentioning a variable of `X`;
- (C3) there is a map `r : X → (created variables) ∖ X` such that `r`, extended by the
  identity, is a context morphism `Γ → Γ ∖ X`: `Γ(r w) = r̂(Γ(w))` for `w ∈ X`.

**Lemma 3 (exactness).** If `X` is a collapse, then `Γ ⊢ J ⇔ Γ∖X ⊢ J`, by derivations of
the same height. (⇒) `Sub.rename` along `r̂` (C2, C3; `J` is fixed by C1). (⇐) `Sub.rename`
along the inclusion `Γ∖X → Γ`, a context morphism by C2. ∎

Lemma 3 needs neither the annotation nor `I`. After removing a collapse, the annotation is
restricted by re-parenting each variable to its nearest remaining ancestor. Ancestor sets
shrink to their remaining part, and relatedness among the remaining variables is
unchanged, so `I` is preserved.

## 4. Irreducible states are small

**Lemma 4.** There is a computable `B` (from the input) such that every annotated state
satisfying `I` and admitting no collapse has at most `B` created variables.

Proof.
- By (I4) the forest has depth `≤ N`.
- The *label* of a created variable is its type with each mentioned ancestor replaced by
  its depth. Since types are in `𝒮` and mention base variables and at most `N` ancestors,
  there are finitely many labels, `L` say, computable.
- Two sibling subtrees (same parent, or both roots) are *isomorphic* if a bijection
  matches parents and labels. Suppose such twins `X = subtree(v')` and `subtree(v)` exist
  and `X` is not mentioned by the two terms. Then `X` is a collapse:
  - (C2): by (I1), anything mentioning a variable of `X` is a descendant of it, hence in
    `X`.
  - (C3): the bijection, because siblings share all ancestors, so labels determine types.
  - (C1): by assumption.
- The terms mention at most `F` created variables, `F` = the maximum number of free
  variables of a type in `𝒮`. Mark these, and their ancestors (at most `N F`).
- At each node, the unmarked child subtrees are pairwise non-isomorphic, and at most `F`
  child subtrees contain a marked variable.
- Let `C(d)` be the number of isomorphism classes of subtrees rooted at depth `d` that can
  occur. Then `C(N) ≤ L` and `C(d) ≤ L · 2^{C(d+1)}`, and the branching is at most
  `C(d+1) + F`. Hence the size is bounded by a computable tower `B`. ∎

In Lean (`Bound.lean`) the parent of a created variable is its nearest proper ancestor, the
class of a subtree is computed with fuel `N`, and the tower is the primitive recursive
function `Bnd N s n₀`, where `s` bounds the sizes of types and `n₀` the number of base
variables.

## 5. The decision procedure

Define `gc(Γ ⊢ J)`: while some collapse exists, remove the first one (in a fixed
enumeration order). This is computable, since there are finitely many candidate `X` and
`r`, and it terminates because the context shrinks. By Lemma 3, `Sub` is preserved both
ways.

**Normalised system `NSub`.** It has the same rules as `Sub`, except that the premise of
the all rule is replaced by `gc(Γ, z:S ⊢ B <: B')`.
- Soundness: `NSub ⊆ Sub`, by Lemma 3 (⇐) at each all-step.
- Completeness: if `Γ ⊢ J` is derivable, the state admits an annotation with `I`, and
  `|created| ≤ B`, then `NSub` derives it. Induction on the height of a `Sub`-derivation:
  - all-step: the premise satisfies `I` (Lemma 2); `gc` keeps `I` (§3) and shrinks the
    created part to `≤ B` (Lemma 4); Lemma 3 (⇒) gives a `Sub`-derivation of the `gc`'d
    premise of no greater height, so the induction hypothesis applies.
  - Other rules keep the context.

**Deciding `NSub` on states with `≤ B` created variables.** The contexts form a finite set
`𝒞` (types from `𝒮` in bounded scopes). Within one context the counter `k` is handled by
two finite relations saturated jointly: base judgments at `k = 0`, and summaries, each of
which pops one level of `k` (`Rules.lean`). The all rule links a `k = 0` judgment in `Γ` to a
`k = 0` judgment in `gc(Γ, z:S)`, which is in `𝒞`; in Lean, to a judgment of any member of
`𝒞` together with a context morphism into `Γ, z:S` (`Family.lean`). Joint saturation over `𝒞` is a least
fixpoint of a monotone operator on a finite powerset, hence computable.

**Theorem.** `Γ₀ ⊢ S₀ <: U₀` holds iff `NSub` derives it (root: no created variables, so
the bound holds), and `NSub` is decidable. Hence `Subtyping` is decidable. ∎

In Lean the saturation is carried out on the codes of judgments, as the least fixpoint of a
primitive recursive operator over a primitive recursive universe of codes (`Prim*.lean`).
The bounds are read off the input code `m`: every type of the judgment it names has size and
`∀`-nesting at most `m + 1`, and its scope is at most `m` (`Final.lean`).

## Remarks

- The result answers the question of Hu and Lhoták (POPL 2020, §7.1), who conjectured that
  kernel D<: with the bad bounds rule is undecidable.
- The decisive fact is (I3) of Lemma 2. The kernel rule compares parameter types for
  identity, which could be used to link created variables into long structures; but the two
  terms of a goal can only share a *chain* of created variables, so no such structure forms.
- Transitivity is admissible in the calculus (`Trans.lean`), so the same holds for kernel
  D<: with both the transitivity rule and the bad bounds rule.
- The bound `B` is a tower of exponentials of height `N`; complexity is not addressed.

