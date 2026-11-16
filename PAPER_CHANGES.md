# Completed target: Theorem 2 and effectivity

The user's clarified scope is Theorem 2 with end-to-end effectivity and
all transitive proof dependencies. Both main endpoints are in
`proofs/Lax369799Proofs/MainTheorems.lean`. The executable function is
`Lax369799.EffectiveFiniteTranslation.compile`; its correctness theorem
requires exactly the promised finite bisimulation invariance.

The effectivity sketch on page 54 is now formalized by numeric bounds for
recognizing algebras, small profiles, Safra states, appearance records and
word conditions. Finite Boolean modal tables enumerate the possible
certificates. The scalar priority compiler translates each table.

A separate finite-model proof supplies the comparison bound: merge modal
game positions sharing a word state, use positional determinacy to select
one local transition, and retain its supported reachable successors.
Alternating simulations prove that the resulting model still wins and
has at most one vertex per word state. Applied to the syntactic MSO
translation of a difference of two modal candidates, this gives a
computable finite separator bound. Bounded graph enumeration and verified
model checkers select an equivalent candidate under the promise.

This follows the paper's finite-search argument, deriving its small-model
ingredient from the already proved finite construction. It does not
assume the unrestricted Janin-Walukiewicz theorem. The algorithm uses an
explicitly encoded finite vocabulary and is exhaustive, with generous
bounds. It is total even when the input does not satisfy the promise.

The broad numbered inventory remains in `paper-coverage.json`: 59 matched
claims, with Theorem 1 and the separate exact Lemma 42/47 formulations
partially aligned. These are outside the clarified completion target;
the actual Theorem 2/effectivity dependency route is entirely proved.
The supported statements of Lemmas 46, 81 and 82 have also been completed.

Final replay and axiom-audit evidence is in `validation-report.json`.
The sections below preserve earlier checkpoints and revision history;
their remaining-work descriptions are historical.

# Changes required to arXiv:2407.12677v6

## Previous checkpoint: explicit supported statements and coverage inventory

The complete numbered inventory is `paper-coverage.json`; the latest
replay checks 198 concepts and 546 ground proofs. The unpruned morphism,
pullback, folding, and flattening results are exposed directly. Supported
system selection, system pullbacks, common unfoldings, and renaming lifts
preserve all outputs. Yield comparisons and continuity keep the variable
map fixed, including root yields. Full supported profile congruence holds
in every rank, and the closed small-profile result and both refinement
corollaries use the original algebra with bound |B₀| + |B₁| + 1. Completion
preserves unfolding invariance and has at most |B₀| + |B₁| unary classes.

At that checkpoint the remaining work included the systems-only clause of Lemma 42; exact supported
formulations of Lemmas 46, 47, 81, 82; unrestricted Theorem 1 in its forward
direction; and the unnumbered effective MSO-to-mu extraction. These are
not counted as proved by the absence of unproved Archive declarations.


## Revised PDF adopted on 2026-11-13

The current target is the user-provided local PDF recorded in
`paper-version.json`, rather than an inferred new arXiv version. Section 4
retains unreachable vertices and Definition 63 removes the old continuity
axiom; Section 5 now uses extremal accepted situations and the two-part
automaton property of Definition 90.

`SetSystemAlgebras` supplies the new evaluation interface and its proved
syntactic instance. `ExtendedContexts` represents the initial/root markers
explicitly. Minimal formal marker data are saturated, and saturation is
proved equivalent to the planted boundary representation. `ExtremalSituations`
minimizes the element together with the context data and proves extremal
replacement and simultaneous replacement. Unlike the earlier fixed-element
context minimization, its split witness equals the original extremal element.
`DirectionProjections` proves the canonical reconstruction and the extremality
of every direction. `ExtremalPaths` proves the regular-branch criterion,
including unmarked tails from all vertices of a functional restriction, and
combines it with direction decomposition to prove Corollary 96.

These changes resolve the earlier open structural path-soundness step for
extremal unary/nullary graphs. Generic context decomposition and extremal
replacement over arbitrary set-algebras are proved in
`ExtendedContextDecomposition` and `ExtendedSetAlgebras`. The revised
small-map bound is used by `Resolutions.SmallMap` and its refinement is
proved in `SmallProfileRefinement`. Two obsolete v6 declarations were
removed in favor of the proved unpruned statements.

`SupportedSystems` now implements output-variable reachability and proves
its preservation under flattening. `SupportCompaction` proves that every
legacy system factors as an injective renaming of a fully supported one.
`SupportedAlgebras` now provides the precise interface and its renaming
law. `SupportEvaluation` proves a finite observation quotient and identifies
its closed sort with the original closed values. `SupportPorts` proves
the corresponding substitution identity. `SubstitutionProfiles` proves
substitution congruence, and `SystemMonad` proves the unit and
associativity identities up to isomorphism. `SupportedCompletion` defines
associative quotient evaluation and proves recognition equivalence.
The renaming and profile statements have also been strengthened to remove
the unnecessary unfolding-invariance hypothesis.

The algebraic infinite-word language now has a proved parity realization:
unary composition is associative, linked-pair factorizations have a Büchi
recognizer, and Safra determinization with appearance records gives the
paper's least-recurring-even condition. A product combines it with the
terminating-word evaluator. `UnaryGraphEvaluation` and
`UnarySystemEvaluation` prove agreement with finite branch-graph
evaluation, including terminating branches. `RunAcceptance` proves both
directions of run correctness, and `AlgebraToAutomaton` proves the existing
algebra-to-automaton declaration along the route of Theorem 103. Its
recognition hypothesis now uses the exact supported-system algebra of
Definition 6, through the proved completion bridge. The clone and modal
algebra declarations have been updated to the same hypothesis.
Clone normalization is now proved in `CloneNormalization`, including an
accepting run on every accepted presentation. Its proof uses pointwise
monotonicity of infinite words, surjective rerouting, uniform stabilization,
and a checked expansion identity for compressed labels. The modal
translation is now proved, using the finite acceptance game, its projected
priority equations, and scalar fixed-point elimination.

The rank-zero case of Lemma 91 is now proved in `ClosedExtremal`, and the
normal-context test statements have been generalized to every rank.
`ModalAcceptanceGame` supplies the total finite arena with explicit winning
and losing terminals, the reversed parity convention, and the exact modal
predecessor identity. The independent `ParityFixedPoints` proof eliminates
one priority by a least or greatest fixed point; `ParityGameEquations`
iterates it to characterize the winning region of any finite parity game.
That characterization is instantiated for the acceptance arena. `FixedPointRetraction`, `ModalGameEquations`, and `ModalGameTranslation`
prove the passage to formulas over the original input. `AutomatonRunGame`
and `CloneGameRun` prove the run/game correspondence. The latter uses the
clone condition to build a bisimilar finite accepting presentation.

The adapted Safra, appearance-record, compactness, and finite parity-game
proofs are from Bojańczyk, Casares, Manthe, and Parys,
[arXiv:2611.10136v1](https://arxiv.org/abs/2611.10136v1), incorporated with
the user's authorization. `external-proofs.json` records source hashes and
adaptations, and `manifest.yaml` contains the citation. No licence claim
beyond the recorded authorization has been added.
`PriorityCompilation` supplies an executable final compiler from finite
modal transition formulas, with a semantic correctness proof. The earlier
MSO-to-finite-data stages still need an effectivity proof. See the revised
coverage table at the start of `PLAN.md`.

The current validation record is at the start of `PLAN.md`. A separate
axiom audit of determinization, finite parity-game determinacy, and the
algebraic omega-language regularity proof found only `propext`,
`Classical.choice`, and `Quot.sound`. The same audit now covers clone
normalization, finite modal equation elimination, the rank-zero context
test, the acceptance arena, the nested parity-game characterization, the modal
translation, and both main results. The replay now checks 479 ground proofs
and leaves no unproved declared statement. The effective translation assertion and the review of quoted external
results remain manuscript coverage obligations. Ancillary helper declarations retained for source
comparison also produce unused-helper warnings.

The sections below record problems in earlier versions and the history of
their repairs. Their numbering refers to those versions unless specified.

Updated 2026-09-18. This log tracks the authorized repair using expanded
continuity. “Proved” means an Archive proof with background axioms only;
it does not mean that the revised proof of the main theorem is complete.
The reference TeX is retained for comparison, not silently rewritten.

## 1. Substitution retains all vertices

**Location:** §2.6, `definition:flattening`, associativity and later substitution laws.

**Change:** use finite presentations without a reachability restriction during
substitution. Take the reachable restriction only when observing yields.
A rooted vertex in an inner presentation can survive an empty surrounding
component; deleting unreachable intermediate vertices destroys associativity.

**Status: proved.** `FinitePresentations`, `UntrimmedFlattening`,
`FiniteMonadLaws`, and `FiniteContexts` supply the replacement. The checked
counterexample to intermediate pruning is `audit/FlatteningAssociativity.lean`.

## 2. Context decomposition preserves the hole's boundary data

**Location:** §2.8, `lemma:context-decomposition` and recomposition.

**Change:** retain whether the hole is initial or a root, and its self-loop
directions, in addition to the unary pieces. The hole remains an ordinary
vertex, as clarified by the author. Recomposition must restore these data.

**Status: proved.** `FiniteDecomposition` and `FiniteNormalForms`; regression
example in `audit/ContextDecomposition.lean`. The extremal comparisons use
the boundary data explicitly.

## 3. Corollary 46 stays valid

**Location:** §2.9, `corollary:yield-continuous`.

No alphabet restriction or change to the corollary's mathematical assertion
is needed. It holds over the base alphabet and over the quotient alphabet.
For finite sets of yields, the sum remains inside the context:

\[
\operatorname{Yields}(C[S])=
\bigcup_{F\subseteq_{\mathrm{fin}}\operatorname{Yields}(S)}
\operatorname{Yields}(C[\textstyle\sum F]).
\]

**Status: proved.** `YieldContinuity.continuity` and its unpruned-context
version `FiniteYieldContinuity.continuity`. Instantiating the alphabet with
quotient values does not justify commuting yields with expansion.

## 4. Replace atomic-label continuity with expanded continuity

**Location:** §4.1, `definition:set-algebras`; §4.2,
`lemma:syntorder`, especially the continuity argument and inclusion (*).

Write \(\pi\) for the contextual quotient map on base-alphabet finite
presentations. For a pattern \(P\) labelled by quotient values, choose
representatives \(q_v\) with \(\pi(q_v)=P(v)\), and put
\(\bar P=\operatorname{flatten}(P[q_v])\). Use the law

\[
a\leq\operatorname{eval}(P)
\quad\Longleftrightarrow\quad
\forall T\in\operatorname{Yields}(\operatorname{trim}\bar P),\ a\leq\pi(T).
\]

Here \(\pi(T)\) means the class of the finite presentation underlying the
base-alphabet yield. Quantify over every choice of representatives. The
resulting order and acceptance tests are independent of that choice;
literal equality of the yield sets is neither assumed nor required.
The interface retains the presentation map and base alphabet.

Delete (*) and its claimed factorization through an atomic quotient-labelled
yield. Do not use the old continuity axiom or the old yield-order lemma to
prove the new existence theorem. The replacement proof combines Corollary
46, the contextual finite-meet law, and the quotient evaluation law.

**Status: proved.** `ExpandedContinuity` proves the expanded evaluation,
contextual/closed acceptance, representative independence, and lower-bound
laws. `ExpandedSyntacticAlgebra.SyntacticAlgebra` is the working interface;
`syntactic_algebra_exists` proves it exists. `representatives_exist` ensures
its law is applicable to every pattern. `recognition` recovers the language.
The refuted original existence declaration has been removed from
`SyntacticAlgebraTheorems`, rather than kept as an outstanding proof goal.
The original `SetAlgebras.SetAlgebra` survives only for conditional results.

The checked obstruction is
`OriginalContinuityBridgeAudit.no_original_syntactic_algebra` in
`audit/NonlinearSubstitution.lean`. For a unary representative \(a(x,x)\),
expansion before resolution retains mixed choices that atomic unary
resolution cannot see. A closing context with two differently marked
leaves separates the resulting contextual classes. Consequently this is a
change of interface, not a new proof of the old axiom.

## 5. Restrict the yield-order inference to expanded yields

**Location:** §4.1, `lemma:yieldssubset-yaleq`, and all later uses.

For the revised quotient, use

\[
\operatorname{Yields}(\bar P)\subseteq\operatorname{Yields}(\bar Q)
\ \Longrightarrow\ \operatorname{eval}(Q)\leq\operatorname{eval}(P),
\]

with reachable restriction understood at observation. Inclusion of yields
of atomic quotient-labelled patterns does not suffice.

**Status: proved.** `ExpandedSyntacticAlgebra.expanded_yield_order`, directly
from expanded continuity. Audit each subsequent use of the original lemma.

## 6. Profiles retain variable origins and an identity case

**Location:** §4.3, small profiles, `lemma:optimal-flatten-resolution`,
`statement:spe-refines-ssc`.

Keep split-variable resolutions together with their variable-origin maps.
The checked finite bound uses the unary carrier with an additional identity
case; the original bound using only its cardinality remains unproved.
Keep initial and rooted observations in the contextual comparison.

**Status: proved replacement bound and finiteness.** `BoundedProfiles`,
`BoundedProfileRefinement`, and the finite/reachable finiteness modules.
No claim is made that the stronger original numerical bound is false.

## 7. Replace the unary normal-form step

**Location:** §5.1, `lemma:det-characterisation` in
`subsection:deterministic-set-algebra`.

Do not deduce that a unary quotient label distributes over a sum. In
particular, do not identify \(b(x_0+x_1)\) with \(b(x_0)+b(x_1)\) under
evaluation when representatives may repeat a variable. The old normal-form
proof remains conditional on the old stronger set-algebra axioms.

The proved replacement is a finite family of whole deterministic initial
or planted-root resolutions of an expanded presentation, preserving its
contextual class for a finite unfolding-invariant recognizer. Each component
retains its internal branching. This does not assert that components can
be replaced by independent unary branches.

**Status: proved class representation; downstream use open.**
`FiniteResolutionNormalForms.contextual_normal_form` and
`ExpandedSyntacticAlgebra.expanded_normal_form`. The latter identifies the
family's class with the evaluation of the original algebra-labelled pattern.

## 8. Restate the syntactic automaton-property corollary

**Location:** §5.2, `lemma:ya-automaton-property`, `cor:synt-aut-prop`.

Use the quotient substitution algebra with expanded continuity and its
contextual order/acceptance predicate. The extremal argument, with the
corrected hole boundary data, gives a deterministic value below any value
in an accepting context while preserving acceptance. Here “deterministic”
is the stated generation by unary/nullary algebra labels; it does not
supply the old parallel-unary normal form.

**Status: proved.** `FiniteAutomatonProperty` and the packaged
`ExpandedSyntacticAlgebra.syntactic_automaton_property`. The old existential
corollary demanding the original continuity interface has been replaced.

## 9. Rework the automaton construction before claiming the main theorem

**Location:** §6.3, `thm:alg2aut`, and its use in §6.4.

The existing construction through independent unary branch types uses the
old §5.1 normal form. The new finite resolution representation has not yet
been converted into a finite transition/word-condition construction that
preserves the choices at branching vertices. This is a mathematical
obligation, not merely an interface rename. The bisimulation-automaton and
mu-calculus conversion obligations also remain open.

**Status: partially repaired by item 12.** Local parallel transition
selection is now proved; run soundness and the word condition remain open.
Preserve the original recognition and logical-equivalence targets. Do not claim they follow merely from the repaired continuity and
automaton-property theorems.

## 10. Iterative replacement and its corrected acceptance criterion

**Location:** §5.1, closure of deterministic elements under substitution;
§6.3, the iterative vertex-replacement paragraph and acceptance of the
resulting labelled presentation.

**Status: proved.** `FiniteVertexReplacement.vertex_context` marks any
vertex while retaining its incident edges and boundary flags.
`simultaneous_replacement` iterates the repaired automaton property over
all vertices of a closed finite presentation. The chosen labels are
pointwise below the original labels and preserve acceptance.

`FiniteDeterministicElements.realization` expands any family of
deterministic values into unary/nullary generating presentations and
proves that their simultaneous flattening has the same value and only
unary/nullary labels. `substitution_closed` proves the subalgebra closure
remark. This asserts a bound on label ranks, not a bound on the number
of outgoing edges or on the branching of base-alphabet representatives.

`ExpandedCertificates.language_iff_certificate` now characterizes language
membership exactly: choose such local deterministic values below the input
labels, choose representatives, and require every yield of their expansion
to be admissible. Soundness follows from monotone evaluation and upward
closure; completeness follows from simultaneous replacement and expanded
continuity. The statement holds on the given input presentation.

The remaining step in item 9 is now precise: replace this expanded-yield
acceptance test by a finite-state word condition and a transition table
with the shape required by `UnfoldAutomata.UnfoldAutomaton`, proving both
directions. The current certificate still tests entire branching yields;
it is not yet an unfold-automaton or an effective recognition procedure.

## 11. The remaining transition argument is not supplied by expanded continuity

**Location:** §5.2, the diagram defining Δ; §6.3, both recognition lemmas
following `thm:alg2aut`. Reviewed against `ExtremalContexts.deltaPattern`,
`FiniteExtremal.delta`, and `AlgebraicTransitions.accepting_transition`.

The extremal witness is more specific than an arbitrary presentation with
unary labels, but it still has a joint condition: its rooted m₀ vertex has
an edge to every initial Uᵢ component. Expanding a representative of m₀
can resolve different occurrences of its variable through different Uᵢ.
The retained boundary root flag can also mark the components themselves.
Thus its known unary/nullary realization does not itself give the tuple
of independent unary types required by the original transition table.

There are two separate obligations for continuing that construction:

1. **Local transition completeness.** In every accepting context, choose
   unary values b₁,…,bₖ whose parallel value is below a and still accepted
   in that context. The proved extremal theorem supplies Δ instead. A
   proof for this special extremal witness could suffice; it need not
   reinstate the false general distributivity law.
2. **Run soundness.** For the transitions actually selected, prove that
   the proposed branch condition implies acceptance of all yields after
   expansion. The original text identifies these tests before expansion.
   The certificate theorem deliberately retains the expanded-yield test.
   A proof restricted to valid transitions could suffice; the existing
   counterexample does not refute such a restricted assertion.

Alternatively, replace both obligations with a new finite transition and
word-condition construction that retains the joint condition. Its finite
representation and recognition equivalence would still need proofs.
Neither alternative has been established here. Merely choosing finite
representatives or invoking Corollary 46 does not discharge these steps.
The parity word-condition construction and later automata conversions
also remain required; the formalization is not complete.

The author clarified that each Uᵢ should commit to its own successor,
as in Example 81. This leads to the split construction below and resolves
the local transition-completeness obligation. Run soundness and the word
condition still require proofs; no assumption for them has been added.

## 12. Split the rooted incoming piece between the successor components

**Location:** §5.2, construction of Δ and its extremal comparisons;
§6.3, selection of transitions. This implements the successor-selection
intuition of Example 81 without the general §5.1 normal-form lemma.

**Change:** replace the single rooted m₀ vertex feeding all Uᵢ by one
rooted m₀ vertex for each Uᵢ, feeding only that component. Each enlarged
component is still unary and is applied solely to xᵢ. Retain the extremal
boundary flag on its a-vertex and the original loop directions. Evaluate
these enlarged unary components to obtain the tuple b₁,…,bₖ.

**Status: proved.** `ExtremalSuccessors.component_step` first verifies that
each original Uᵢ already stays in its own component and exits only to xᵢ.
`SplitExtremal` defines the modified witness. The boundary and unary-piece
comparison maps each use one component at a time, so their extremality
arguments also hold for the split witness. Consequently its value remains
below a. Conversely, merging the copied incoming pieces maps the split
witness to the original Δ; reverse morphism monotonicity transfers the
original acceptance-preservation inequality to the split witness.

`SplitExtremal.parallel_value` follows directly from associativity.
`ParallelReplacement.accepting_parallel` now proves that in every accepting
context, a positive-rank value admits an accepted parallel tuple below it.
This replaces the use of `lemma:det-characterisation` when selecting a
transition in §6.3. No distributivity for arbitrary unary values is used,
and no equality between the original and split witnesses is asserted.

The change resolves item 11(1). Item 11(2), the connection from branch tests
to expanded-yield acceptance, and the finite parity word-condition
construction remain open.

## 13. Connect split transitions to runs and terminating word tests

**Location:** §6.3, definition of Δ and Ω, and the two recognition proofs.

**Status: algebraic run equivalence and terminating-word automaton proved.**
`ExpandedTransitions.automaton` is the transition table over the repaired
quotient, with a word condition supplied as a parameter. Its local
acceptance-preserving transition theorem uses `ParallelReplacement`.
`run_label_below` verifies the inequalities for the actual `Run` fields,
including exact agreement at leaves. `evaluated_run_sound` transfers
acceptance of the evaluated run to language membership.

Conversely, `evaluated_run_exists` gives a legal run on the given input
presentation with an accepted evaluated value, for every accepted input.
It uses `FiniteLocalReplacement.simultaneous` to choose the parallel tuples
while preserving acceptance, then encodes them as finite unary types.
These statements hold for any supplied word condition; they do **not**
assert `Run.Accepting` for that condition.

`RunPresentations` expands the selected tuples into a presentation labelled
only by unary/nullary values. Its evaluation equals the evaluated run.
Acceptance passes to any presentation mapping into it, which will be used
for the finite path and cycle observations.

`FiniteBranchWords` constructs a deterministic automaton for terminating
words. A prefix state stores a function on the nullary sort; a nullary
letter applies that function and enters a final-value state. A further
letter enters a dead state. The state set is finite when the nullary sort
is finite. `chain_evaluation` identifies iterated unary application with
evaluation of the corresponding finite path presentation, and `accepts`
proves the automaton's acceptance criterion for such words.

**Still open:** construct the finite-branch and lasso observation maps for
runs; construct and verify the infinite-word condition (including its
finite parity representation); prove the required implication from branch
acceptance to input-language membership. The algebraic soundness theorem
does not replace that last implication, and the finite-word automaton is
not a condition for infinite words.

## 14. Branch observations and the remaining soundness bridge

**Location:** §6.3, both recognition directions and the branch condition Ω.

**Status: observation maps and regular-branch reduction proved.**
`RunBranchObservations.path_morphism` maps the finite graph of a terminating
branch into the flattened run presentation. `regularPath_morphism` does
the same for a finite functional graph representing an infinite branch.
The two acceptance corollaries follow by reverse morphism monotonicity.
They include the leaf case, arbitrary finite prefixes, and cycles.

`RegularBranchWords` proves that finite branch graphs unfold to ultimately
periodic branches and that every ultimately periodic branch has such a
finite presentation, preserving both vertices and chosen directions.
`regular_test` therefore reduces any supplied parity condition on all
infinite branches to these finite observations.

`CombinedWordCondition` gives a product construction combining the finite
word evaluator with any supplied parity condition. Its finite acceptance
is exactly iterated unary evaluation; its infinite acceptance is exactly
that of the supplied parity component. This does not construct that
component from the algebra.

The main theorem `AlgebraToAutomaton.algebra_to_automaton` remains unproved.
In particular, the converse to the observation-acceptance statements is
not a consequence of the expanded continuity law alone for arbitrary
unary presentations. A type may repeat its one successor variable, so
expansion can mix later choices within that type. Splitting the extremal
witness separates successor indices at a single transition, but does not
assert linear use of a successor inside the unary representative.

Each individual branch still chooses only one successor. The mixed
choices mentioned here occur on different branches of a whole expanded
yield, not on one branch. The author correctly emphasized this distinction.
The required conclusion is language membership; proving acceptance of the
entire evaluated run is one possible, stronger intermediate statement.

The author question is whether the legal-transition inequalities provide
a further global soundness argument, or whether the selected types need
a stronger restriction. No counterexample to soundness *for legal runs*
is claimed, and no additional soundness assumption has been inserted into
the main theorem. Besides this bridge, the algebraic infinite-word
condition and its parity realization remain to be constructed. The direct
finite path observation also still needs to be identified with the
recursive path used by the finite-word evaluator.

## 15. Restrict the selected unary types to preserve explicit choices

**Location:** §5.1, extremal selection, and §6.3's unary type alphabet.

**Author clarification:** final unary elements must not retain hidden
branching choices; those choices must be exposed by selecting among the
available deterministic elements.

`ChoicePreservingUnary.PreservesChoices` records the necessary binary law
on closed continuations:

    act b (c + d) = act b c + act b d.

This is a restriction on eligible types, not an axiom imposed on the
whole unary sort. Constants are not excluded by requiring preservation
of the empty sum. Nor are fixed branching side trees prohibited merely
because their vertices have rank greater than one.

**Proved:** words of eligible unary types preserve binary choices; finite
expressions of eligible unary actions and choices are accepted exactly
when all their path evaluations are accepted, assuming the accepting set
tests a sum by testing both summands. The eligible subtype remains finite
when the ambient unary sort is finite. These statements concern finite
expressions; they do not assert the cyclic counterpart.

**Extremal construction strengthened:** the split-witness lower bound now
holds for every positive rank, including rank one. `accepting_parallel`
therefore uses extremal selection uniformly. The previous rank-one case,
which returned the original arbitrary unary value, has been removed.
Furthermore, `SplitExtremal.acceptance_iff_dataBelow` gives an exact test:
the witness is accepted at normal data y iff its chosen extremal data x
satisfy DataBelow x y. Necessity uses both comparison lemmas; sufficiency
uses acceptance preservation and monotonicity.

**Resolved by a second extremal selection:** `ExtremalUnaryTypes.replacement`
refines any unary value in an accepting context to a smaller rank-one split
extremal witness. `SelectedChoicePreservation.selected_preserves_choices`
proves the displayed binary law for these witnesses, with no extra
continuity or distributivity hypothesis.

The proof uses the principal normal-context test. For a planted prefix t
and continuation c, the incoming and outgoing pieces both contain t and a
rank-zero copy of c; that copy is initial only in the outgoing piece.
Unmarked copies must be retained. Both marked and unmarked lifts preserve
sums, so the data for c+d are the meet of the separate data. Extremality
turns that meet into conjunction of acceptance tests. Normalization of
arbitrary testing contexts and contextual order separation yield the
class equality. This argument establishes the law for closed c,d.

`SelectedParallel.accepting_parallel` performs this second selection on
each component in its current composed context. Acceptance is preserved
at every step, and pointwise monotonicity retains the parallel lower bound.
The revised `ExpandedTransitions.automaton` now requires selected components
in every legal transition. Its local choice theorem and its complete
algebraic run-existence proof have been updated to this stronger condition.
`edge_preserves_choices` proves the binary law for every legal run edge.
The finite codes still cover the ambient unary sort; legal transitions
use only selected values.

**Paper change:** insert the rank-one component-refinement argument before
fixing the unary transition types in §6.3, and restrict those transitions
accordingly. Do not infer the binary law merely from a component having
rank one. This resolves the outstanding component-selection question.
Cyclic branch soundness, identification of the two finite path
presentations, and construction of the algebraic infinite-word parity
condition remain open; the closed binary law alone is not recorded as a
proof of these further statements.

## 16. Split choices in cyclic presentations before testing branches

**Location:** §6.3, the soundness proof's reduction to branch observations.

**Proved:** `ContextChoices.accepting_union` applies a selected unary
value to a context whose outgoing hole edges are restricted to two target
sets. Acceptance for their union is equivalent to acceptance for each
restriction. This permits feedback and self-loops and retains every
vertex, including vertices made unreachable by the restriction.

The normal incoming piece is unchanged. The outgoing piece has the union
of the two sets of initial vertices; the hole's loop set is likewise a
union. `FiniteMarkUnion.evaluation_union` identifies such a union of marks
with the meet of the separate values by folding two copies of the common
graph through a surjective cover. Thus the entire normal datum is the
meet of the two data, and the selected type's principal acceptance test
proves the equivalence. This is stronger than the earlier law on closed
continuations and directly addresses feedback.

`GraphChoices.finite_choices` iterates the step through any finite set of
vertices in a unary/nullary presentation with selected unary labels.
Taking all vertices gives an equivalence with acceptance of every
functional restriction. `admissible_test` shows that it suffices to retain
one existing successor whenever an outgoing edge exists. Other choices
are covered by reverse morphism monotonicity from such a completion.
These results are valid for cyclic presentations; no acyclicity assumption
or additional continuity axiom is used.

`RunPresentations.selected` verifies that every unary label of an actual
legal run presentation is selected. `functional_test` transfers the
functional-restriction criterion to the evaluated run.

**Remaining in soundness:** relate each admissible functional restriction
to the finite and regular infinite branch observations. The decomposition
must account for multiple initial vertices and for vertices made
unreachable by restricting edges: their unary representatives may still
contribute roots after expansion. A suitable covering family of marked
and unmarked path/cycle observations is needed. The new theorem does not
silently discard these vertices.

## 17. Identify terminating path graphs with the finite-word evaluator

**Location:** §6.3, the finite part of the word condition Ω.

**Proved:** `FinitePathEvaluation.evaluation` identifies the evaluation of
the direct finite path graph with the fold of unary actions ending in its
nullary value. Its proof constructs the prefix-flattening isomorphism and
uses associativity. `RunBranchObservations.path_evaluation` applies this
to the existing finite branch observations, including a branch of length
zero.

`RunWordCondition.condition` encodes those actions and accepting values
in the finite type alphabet and combines their evaluator with a supplied
parity condition. `finite_path_iff` proves that its finite acceptance is
exactly acceptance of the actual branch observation graph; `infinite_iff`
retains the supplied infinite-word condition. This closes the previously
outstanding direct/recursive finite-path identification. Construction of
the algebraic infinite-word condition and its parity realization remains
open, as does the observation-to-functional-graph soundness step in item 16.

## Validation of this revision

`lax build . --replay` passed on 2026-09-18: 131 concepts, 307 proofs,
305 with background axioms only and two with explicitly unresolved
dependencies. Five statement obligations remain unproved. The fourteen new cyclic-choice and finite-path proofs use
only `propext`, `Classical.choice`, and `Quot.sound`. The six existing generated constructor-helper warnings
are unchanged.
