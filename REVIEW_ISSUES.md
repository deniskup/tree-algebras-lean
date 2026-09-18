# Source review: arXiv:2407.12677v6

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
This last closed-context explanation is mathematical, rather than a
separate kernel-checked closed-language counterexample.

The question is how continuity or the unary normal-form argument should
be adjusted to account for split-variable resolutions. The unpruned
quotient does not assert continuity, so its existing proofs remain valid;
its automaton-property theorem cannot yet be combined with the original
continuity-based unary normal-form theorem. This issue does not affect the
completed MSO recognition or encoding/bisimulation proofs.
