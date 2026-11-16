# Source review: arXiv:2407.12677v6

These are historical diagnostics of arXiv v6. The submission now targets
the revised local manuscript of 13 November 2026, recorded in
[paper-version.json](paper-version.json). Theorem 2, its proof dependencies,
and effectivity are complete; references below to open principal theorems,
global soundness, or infinite-word obligations describe earlier checkpoints.
Current coverage is in [PLAN.md](PLAN.md) and [paper-coverage.json](paper-coverage.json).

Paper revisions are tracked in [PAPER_CHANGES.md](PAPER_CHANGES.md), including proved replacements and open downstream changes.

## Context decomposition loses an initial hole

The definitions immediately preceding `lemma:context-decomposition` in
Section 2.8 (`reference/source/systems.tex`, lines 596–624) admit this case:

1. Let C be the closed context with one vertex, labelled by the rank-zero
   hole. That vertex is initial, there are no root vertices, and there are
   no edges. This satisfies the definition of a set-context and of a context.
2. Its only piece P₀ is obtained by deleting the hole, so P₀ is empty.
3. The stated recomposition Context(P₀) adds a new hole, but takes initial
   vertices from P₀. Consequently it has no initial vertices and no roots.
4. Removing unreachable vertices gives the empty set-system.
5. The empty system and C are not unfold-equivalent: a common locally
   surjective cover must have an initial vertex to cover C, but cannot map
   any vertex to the empty system.

`audit/ContextDecomposition.lean` defines C, the untrimmed recomposition,
and its reachable restriction, and proves that C and the recomposition
are not unfold-equivalent. This file imports definitions only; its final
axiom report must contain only `propext`, `Classical.choice`, and `Quot.sound`.
It does not assume any paper theorem. Run it from `concepts/` with:

```sh
lake env lean ../audit/ContextDecomposition.lean
```

This is a boundary case in the stated auxiliary construction, not a
counterexample to either main theorem. The source proof of
`lemma:choice-extremal-context` uses this decomposition, so the proof route
needs a repair before that step can be certified.

The implemented correction retains, alongside the unary pieces, whether the
hole is initial, whether it is a root, and the directions of any edges from
the hole to itself. The reconstruction must restore these three kinds of
boundary data. Merely requiring positive hole rank is insufficient: an
initial unary hole with a self-loop has the same loss of boundary data.
The audit also checks the looping-hole example for every rank k, including
k ≥ 2 as used by the extremal-context argument. The repaired argument has now been checked through the automaton-property
theorem. The general corrected decomposition is now proved
in `proofs/Lax369799Proofs/ContextDecomposition.lean`, with its statement and
construction in `concepts/Lax369799/ContextDecomposition.lean`.

The construction retains the ordinary-vertex interpretation of the hole;
it imposes no restriction on its initial/root marks or self-loops. It
copies each unary piece separately, adds a fresh hole carrying the recorded
boundary data, and removes unreachable vertices. Its projection to the
original context is locally surjective. This proves unfold-equivalence
for every closed context, without any paper theorem as an assumption.
A separate checked statement confirms that none of the pieces contains
a hole-labelled vertex. The pieces currently use finite presentations,
with unreachable vertices removed only after reconstruction; their labels
are in the extended alphabet but avoid its hole symbol.

`PresentationCovers.trim_cover` supplies the general reachable-restriction
lemma used by this proof. The later algebraic normal form and extremal-context argument now carry
the same boundary data and have ground proofs as well.

The literal decomposition lemma has deliberately not been added as an
Archive statement. The draft retains the paper's principal theorem
statements as open obligations, without treating them as proved.

The proved downstream repair is detailed in [EXTREMAL_REPAIR.md](EXTREMAL_REPAIR.md).
The planted normal contexts and modified Delta are now defined in
`concepts/Lax369799/ExtremalContexts.lean`. Delta's determinism has a ground
proof, as does finite extremal choice over boundary data and unary values.
The algebraic normal form, both comparison inequalities, and the resulting
automaton-property theorem also have ground proofs.


## Intermediate pruning breaks flattening associativity

The convention at the start of Section 2 and in the set-system definition
requires removal of unreachable vertices (`reference/source/systems.tex`,
lines 21 and 54). The monad lemma in Section 2.6 (lines 482–490) asserts

```
flatten(flatten(S₃)) = flatten(relabel flatten S₃).
```

With pruning after each flattening, these two sides need not even be
unfold-equivalent. The following example uses only two outer vertices:

- The outer system is closed, has initial vertex p, no roots, and the
  edge p --0--> q.
- The label of p is the empty rank-one set-system over set-systems.
- The label of q is `atomic(plant(atomic a))`, for a nullary letter a.

Every system supplied as input satisfies the stated reachability condition.
In particular, q is reachable along the outer edge.

If the outer and middle levels are flattened first, p contributes no
vertices. The middle vertex contributed by q is neither initial nor root,
so pruning removes it. Both this intermediate result and its subsequent
flattening are empty.

If the middle and inner levels are flattened first, q's label becomes the
one-vertex rooted a-system. The final flattening retains this inner root,
independently of reachability from p. The result therefore has a root.
A common locally surjective cover cannot map to the empty system and also
cover this root.

`audit/FlatteningAssociativity.lean` defines this example and proves
`flattening_not_associative_up_to_unfolding`. Its axiom report is exactly
`propext`, `Classical.choice`, and `Quot.sound`; it assumes no paper theorem.
Run it from `proofs/`:

```sh
lake env lean ../audit/FlatteningAssociativity.lean
```

This issue is independent of the corrected hole-boundary decomposition.
The associativity claim has not been added as an Archive axiom. Existing
set-algebra results are conditional on the explicit set-algebra axioms;
they do not supply the missing syntactic set-algebra construction.

The user authorized choosing a repair ("do whatever works"). A separate
finite-presentation construction now retains all vertices during
substitution. Its associativity and both unit laws have Lean proofs in
`proofs/Lax369799Proofs/UntrimmedFlattening.lean`. The existing reachable
system development has not been silently reinterpreted. The remaining
work is to establish the appropriate algebra and yield laws for the
repaired construction; retention alone does not justify carrying over
continuity unchanged.

## The yield-substitution inclusion used for continuity fails

The inclusion marked `(*)` in the syntactic continuity proof
(`reference/source/set-algebras.tex`, lines 308–316) asserts that every yield
of a substituted system comes from substituting an outer yield. This fails
already for a reachable two-vertex pattern, independently of intermediate
pruning:

- The initial outer vertex p has rank two and is labelled by the empty
  rank-two set-system.
- Its only edge is p --0--> q; direction 1 has no edge.
- Vertex q has rank zero and is labelled by the one-vertex rooted a-system.
- There are no outer roots.

There is no outer initial yield: any deterministic resolution must supply
an edge in direction 1 at p, which a morphism cannot preserve. There is no
outer root yield either. Nevertheless, flattening retains q's inner root,
so the planted a-system is a yield of the flattening. Thus the left side
of `(*)` is nonempty and its right side is empty.

`audit/YieldSubstitution.lean` checks both facts and proves
`yield_substitution_inclusion_fails`, using only `propext`,
`Classical.choice`, and `Quot.sound`. Run from `proofs/`:

```sh
lake env lean ../audit/YieldSubstitution.lean
```

This refutes the asserted inclusion, not the main theorem and not by itself
all possible proofs of continuity. The unpruned quotient construction does
not assume this inclusion or continuity. Its order, meet, and recognition
proofs remain valid. The verified extremal-context proof does not invoke
the continuity field; later uses of yield-order must be reviewed separately.

## Direct hole loops in context smallification

The smallification proof in v6 applies the recognising evaluation to every
unary cut piece. For a deterministic context, a direction leading straight
back to the hole has an empty cut piece. That piece is not a deterministic
system, so its value is not supplied by the stated regular-tree evaluation.
This is a typing issue in the displayed proof; it does not by itself refute
the smallification statement with its original bound.

`DeterministicPieces.direction_piece` and `entry_piece` now prove the exact
alternatives: a direct boundary connection produces an empty piece, and
every other continuation produces a deterministic unary system. The optional
continuation keeps the identity case separate. The checked compression lemma
preserves both optional observations and loop flags, with fibre bound
`Nat.card (B 1) + 1`. `FiniteProfiles.bounded_profile_finite` proves that this
modified bound still gives finitely many profiles. Evaluation preservation under this compression is now proved in
`ContinuationCompression`, including the recognising-alphabet version.
`OptimalResolutions` now proves bounded optimal flatten-resolution.
`BoundedProfileRefinement` proves that these modified profiles refine every
finite contextual acceptance test and give a rankwise-finite quotient.
`ReachableFiniteness` also establishes the original reachable syntactic
rankwise-finiteness theorem, without assuming the original small-profile
refinement statement. The smaller original bound remains unproved.


## Nonlinear substitution: resolutions recover the mixed case

The example in `audit/NonlinearSubstitution.lean` illustrates the need for
resolutions, not a defect in independent-choice substitution. This is the
same phenomenon explicitly discussed in v6 Section 2.9,
`example:direct-resolutions-not-compositional`. The earlier interpretation
of this diagnostic as requiring a choice-semantics clarification was mistaken.

Let `b = a(x,x)`. The direct-resolution-only combination of a unary outer
choice yields only `a(x₀,x₀)` and `a(x₁,x₁)`, whereas substitution also admits
`a(x₀,x₁)`. A resolution retains this mixed system together with the map
`σ : Fin 2 → Fin 1` sending both variables to zero. Renaming the mixed
system by `σ` gives a direct resolution of `b`.

The audit now proves `mixed_is_resolution_of_repeated`, constructs the
explicit `splitResolution` flatten-resolution, and proves
`resolutions_recover_mixed`: its flattening is a direct resolution of the
original flattened pattern and an unfolding of the mixed system. All these
proofs use only background axioms. `distribution_fails` remains a correct
statement about the insufficient direct-resolution-only construction.

No shared-choice convention is needed. Continue using resolutions with
their variable-origin maps. The remaining normal-form and continuity
obligations must be proved using the appropriate resolution arguments;
this example is not evidence that those obligations are false.

The general resolution argument is now checked in the Archive development.
`ResolutionLifting.transfer` preserves the variable-origin map when passing
through yield inclusion. `YieldSubstitution.transfer_resolution` applies
this to factorized flatten-resolutions. `YieldObservations.flatten_mono`
and `yield_context_congruence` include both initial and root yields and
use only background axioms. Thus the nonlinear example creates no gap
in these compositional results.

## Continuity and unary normal forms after resolution transfer

The user's resolution correction is implemented: general flatten-resolution
transfer and full yield-context congruence are proved. The mixed branch in
`NonlinearSubstitution.lean` is explicitly recovered by a split-variable
resolution. That example is not a defect in resolution composition.

There is a separate compatibility question at the later continuity step.
The same audit now proves `continuity_forces_distribution`: for every
continuity-bearing `SetAlgebra E` and every unary value b,

```
eval(b(x₀ + x₁)) = eval(b(x₀) + b(x₁)).
```

Here the left presentation has one unary vertex and two possible targets
in direction zero. The right presentation has two initial unary vertices,
with their sole directions going to x₀ and x₁ respectively. Both have no
roots. Projection to either variable is atomic b, so the proved unary
normal form gives the displayed equality.

The audit also proves `continuity_forces_expanded_distribution`: take
b = eval(a(x,x)) for an arbitrary binary algebra element a, and use
associativity to expand both sides. All these proofs have only the three
background axioms (and the explicitly quantified SetAlgebra hypothesis).
The earlier `distribution_fails` theorem checks that the corresponding
base-letter presentations do not have the same yields: the left admits
a(x₀,x₁), while the right does not.

The intended syntactic interpretation can distinguish them: substitute
leaves with two different marks and consider the unfolding-invariant
language “all children of the initial vertex have the same mark.” Every
yield on the right satisfies it; a mixed yield on the left does not.
The closed-context separation and the resulting impossibility of the
original syntactic set-algebra are now kernel-checked; see the final
section below.

The question is how continuity or the unary normal-form argument should
be adjusted to account for split-variable resolutions. The unpruned
quotient does not assert continuity, so its existing proofs remain valid;
its automaton-property theorem cannot yet be combined with the original
continuity-based unary normal-form theorem. This issue does not affect the
completed MSO recognition or encoding/bisimulation proofs.


## Corollary 46 and expanded representatives

The user authorized following the expanded-representative route and
pointed out that the finite-family step is Corollary 46 of v6
(`corollary:yield-continuous` in `systems.tex`). Its statement is

```
Yields(C[S]) = ⋃ { Yields(C[Σ F]) | F ⊆ Yields(S), F finite }.
```

The finite sum remains inside the context. Different occurrences may
therefore choose different members of F; replacing this by a union over
single outer yields would lose precisely the mixed choices discussed
above. Corollary 46 supplies the finite approximation for the expanded
base-letter representative. It does not by itself prove the separate
inclusion (*) for atomic algebra labels.

`FiniteResolutionApproximation.direct_approximation` formalizes the
central flattening step in the proof of the preceding lemma: factor a
direct resolution, collect the finitely many renamed inner resolutions
over each outer vertex, and retain their variable maps when reassembling
the flatten-resolution. `ContextResolutionApproximation` now proves the context version for
initial and root resolutions. `RootResolutionApproximation` retains the
entry flags in the finite support of root observations.
`YieldContinuity.continuity` proves Corollary 46 for arbitrary finite
families of yields, including both directions and root yields. Finite
indexed families may repeat a summand; their disjoint sum is the
corresponding finite sum in the statement. The converse combines
unfolding witnesses into a cover of the proposed sum.

`ResolutionFamilies` and `FiniteResolutionNormalForms` also prove finite
families of actual resolutions preserving bounded profiles, and hence
contextual equivalence for a language recognized by a finite
unfolding-invariant algebra. `ExpandedContinuity` proves that evaluation
is represented by expansion, and that acceptance of all expanded yields
in every context is independent of the chosen representatives. These
statements do not assert the original atomic-label continuity axiom or
its unary normal-form consequence.


The extension to unpruned contexts is also proved, in
`FiniteYieldContinuity`. `FiniteContinuityOrder.order_approximation`
characterizes comparison with a base presentation by comparison with
all finite sums of its yields. `ExpandedContinuity.finite_approximation`
identifies the same criterion for evaluation after expansion. Thus the
expanded route now has a checked finite-approximation law, independent
of (*); the distinction from atomic-label continuity remains explicit.


`FiniteYieldMeets.finite_meet` proves that finite sums, including the
empty sum, are meets in the contextual order. Consequently,
`FiniteYieldMeets.yield_lower_bound` and
`ExpandedContinuity.yield_lower_bound` give the lower-bound form of
continuity: being below an evaluated expansion is equivalent to being
below the class of every base-alphabet yield of that expansion. This
proves the expanded-representative route through Corollary 46 without
using (*). It still does not turn an atomic unary algebra label into a
base-alphabet unary system: its representative may branch and repeat a
variable. Section 5.1's unary normal-form argument needs a separate
replacement before the repaired quotient can feed the original
unfold-automaton construction.


## Original continuity cannot be added to the original syntactic quotient

The attempted bridge now has a checked counterexample, not merely a
failure of equality of open yield sets. The namespace
`OriginalContinuityBridgeAudit` in `audit/NonlinearSubstitution.lean`
uses the ranked alphabet with Boolean labels in each rank. The witness
itself uses only one binary symbol a and two nullary symbols p and q,
whose Boolean labels differ. Its language consists of systems whose
initial vertex's children all have the same Boolean label.

The theorem `language_unfold` proves that this language is invariant
under unfolding, so it satisfies the hypothesis of the original
`syntactic_algebra_exists` statement. No recognizability hypothesis is
required by that statement.

Let b be represented by a(x,x). The two rank-two presentations are

```
expanded         = expand(b(x₀ + x₁))
expandedParallel = expand(b(x₀) + b(x₁)).
```

The context `closing` substitutes p for x₀ and q for x₁. Theorems
`parallel_accepted` and `expanded_rejected` prove that the second closed
presentation is accepted and the first is rejected. The first has the
mixed yield a(p,q); all yields of the second have uniformly labelled
children. The proof checks the actual context substitution using covers,
including all initial and root yields. These witnesses are acyclic and
root-free, so this issue is separate from the intermediate-pruning and
hole-boundary issues.

`distinct_classes` therefore proves that the two presentations have
different classes in the original reachable yield-syntactic quotient.
On the other hand, original continuity forces

```
eval(b(x₀ + x₁)) = eval(b(x₀) + b(x₁)).
```

The quotient-evaluation law identifies these values with the two
classes above. The theorem `no_original_syntactic_algebra` concludes

```
¬ Nonempty (SyntacticOrder.SyntacticAlgebra language).
```

Lean checks this theorem using only `propext`, `Classical.choice`, and
`Quot.sound`; it does not use any unproved paper statement. The audit was
checked with `lake env lean ../audit/NonlinearSubstitution.lean` from
`proofs/`. Thus the original `syntactic_algebra_exists` statement, with
the current definitions, is refuted by this audit and must not be used
as a bridge. Corollary 46 remains valid, including over Y, and the
expanded continuity results remain proved. This does not refute the
paper's main logical theorem or rule out a repair that changes the
algebra interface or the syntactic semantics; such a repair must avoid
forcing the two separated classes to coincide.


## Expanded interface adopted (2026-09-18)

`ExpandedSyntacticAlgebra` now packages quotient substitution with expanded
continuity, proves existence and representative availability, and supplies
recognition, expanded yield order, finite resolution normal forms for
evaluations, and the syntactic automaton-property corollary. The original
continuity-bearing existence declarations were removed from the active
concept statements. The original generic set-algebra remains an explicitly
conditional interface. See PAPER_CHANGES.md for the replacement formulas
and the remaining transition-construction obligation.


## Revised §6.3: global branch soundness (2026-09-18)

The split extremal construction resolves local transition selection.
The checked run and observation theorems give

- language membership ⇒ a legal run with accepted algebraic value;
- accepted algebraic run value ⇒ accepted finite and regular branch observations;
- accepted algebraic run value ⇒ language membership.

The missing implication is from accepted branch observations to language
membership (or, more strongly, to accepted algebraic run value), for the
chosen legal transitions. Expanded continuity checks whole expanded
yields. In `b(c₀(x₀)+c₁(x₁))`, a representative of the unary type `b` can
repeat its sole variable and admit a mixed expansion. The separate branch
words do not directly test that mixed expansion. The already checked
nonlinear-substitution example explains why a generic unary distributivity
argument is unavailable; it is **not** a counterexample to the implication
restricted to legal runs.

Question sent to the author: do the legal-transition inequalities yield a
further global soundness lemma, or should the selected unary types satisfy
a stronger restriction? A unary component having only one successor index
is distinct from every resolution using that successor at most once.
No stronger restriction is assumed in the current development.

The author clarified that one branch takes only one of the cᵢ successors.
This is correct: the concern is a whole expanded yield with different
choices on different branches, not two choices on one branch. For example,
with b represented by a(x,x), the mixed yield is a(c₀(x₀),c₁(x₁)); the
separate type-word expansions give a(c₀(x₀),c₀(x₀)) and
a(c₁(x₁),c₁(x₁)). A proof may establish input-language membership directly,
without asserting the stronger acceptance of every expanded run yield.


### Author-directed restriction on final unary types

The author confirms that hidden branching choices must be absent from
final unary elements; choices belong in the explicit selection of
deterministic elements. `ChoicePreservingUnary` now states the binary
choice law as a predicate on eligible unary types, and proves finite
branch testing under that predicate. This does not redefine all unary
quotient values as eligible. The rank-one bypass in parallel replacement
has been removed; all positive ranks now use extremal selection.

The construction question is now resolved. A second extremal selection,
at rank one, refines each component below its original value while
retaining acceptance in its current context. Its principal normal-context
test proves binary choice preservation on closed continuations. Finite
iteration refines a whole parallel tuple and retains its transition
inequality. The legal transition definition and its existence proof now
both require these selected components. No extra distributivity or
completeness assumption is used. See PAPER_CHANGES.md, item 15.

The remaining global soundness and infinite-word obligations are separate;
no completed proof of §6.3 is claimed from this binary law alone.


### Cyclic splitting now established

The restriction on selected unary types now yields a stronger, checked
result than binary distribution over closed continuations. Outgoing
choices at a unary hole can be split in arbitrary cyclic contexts, with
acceptance equivalent to the conjunction of the restricted tests.
Finite iteration reduces a legal run's algebraic acceptance to its
admissible functional restrictions. This uses the exact normal-data test
and a cover that folds duplicate graph copies; it does not invoke the
false inclusion (*) from the original continuity proof.

The remaining observation bridge must retain unmarked components of
functional restrictions, since expansion of their labels can contribute
roots. Finite branch graph evaluation has meanwhile been identified with
the encoded finite-word evaluator. Full §6.3 soundness and the algebraic
infinite-word parity construction are still not claimed complete.
