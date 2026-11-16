# Substitution without intermediate pruning

This file preserves the repair history. The current submission completes
Theorem 2, its transitive proof dependencies, and the total executable
translation under the finite-invariance promise. See [PLAN.md](PLAN.md)
and [validation-report.json](validation-report.json) for current coverage
and validation. References below to unfinished automata, modal translation,
or effectivity describe earlier checkpoints.

## Historical checkpoint: 13 November 2026

The 2026-11-13 revision now proves canonical extremal direction
decomposition, extremality of the directions, the path criterion with
unmarked tails, and the revised syntactic automaton property. See the
coverage table at the start of [PLAN.md](PLAN.md). The notes below retain
the earlier repair history; their references to an open graph path
criterion are superseded by `ExtremalPaths.path_criterion`. Construction
of the algebraic infinite-word parity condition is now proved by
`AlgebraicOmegaWords` and `AlgebraicBranchCondition`, using attributed
Safra and appearance-record proofs. Agreement with finite branch-graph
evaluation and Theorem 103 are now proved through `UnaryGraphEvaluation`,
`UnarySystemEvaluation`, and `RunAcceptance`. Clone normalization and
its guarantee of runs on every accepted presentation are now proved in
`CloneNormalization`. The closed witness also proves Lemma 91 in rank
zero. The acceptance arena and its nested fixed-point characterization
are proved. Its equivalence with automaton runs and translation to
formulas over the input remain open. One-step formulas and finite
fixed-point elimination are proved. Generic extended
context decomposition and replacement, revised-bound small-profile
refinement, and fully supported flattening have also been proved.

Paper revisions are tracked in [PAPER_CHANGES.md](PAPER_CHANGES.md), including proved replacements and open downstream changes.

The user authorized choosing a working repair of the flattening issue.
Finite presentations retain all vertices through substitution; only the
final yield observation restricts to reachable vertices. The original
reachable development remains separate and has not been silently changed.

## Verified repair

- Associative substitution, atomic units, naturality, context composition,
  extension by presentation-valued labels, and contextual congruence.
- Contextual quotient evaluation, its partial order, monotonicity, and
  recognition on the original reachable deterministic systems.
- Disjoint union induces meet. Acceptance is an upward-closed meet filter;
  the empty presentation is accepted. If the closed sort is finite, the
  accepting filter is principal.
- Evaluation reverses morphisms. It is invariant under locally surjective
  covers that are also globally surjective on outer vertices. The extra
  surjectivity accounts for roots inside labels at unreachable vertices.
- Planting invariance, order separation, and a boundary-preserving
  decomposition retaining all vertices of all unary pieces.
- Algebraic normal forms, finite extremal choice over the unary sort,
  Delta's determinism, both comparison inequalities, and the resulting
  automaton property for the contextual quotient when its unary sort is
  finite. No yield-continuity axiom is used in this argument.

- Bounded optimal flatten-resolutions, initial and root observation transfer,
  and bounded-profile refinement of contextual equivalence. Root entries in
  unreachable outer components are retained through a separate starting-copy
  construction. Both repaired and original reachable contextual quotients are
  rankwise finite for unfold-invariant recognizable languages.
- Regularization of an arbitrary finite recognizing algebra through its
  generated subalgebra and the quotient by polynomial acceptance tests.
  The automaton property therefore applies without an unfolding-invariance
  assumption on the original recognizing algebra.

The full paper is not yet formalized. MSO recognition, ranked encoding correctness, and the reverse logical
implication are proved. The automata constructions and their external
dependencies remain outstanding.

## Next obligations

1. The corrected resolution, bounded-profile refinement, and regularization
   arguments are complete, with fibre bound |B₁|+1. Continue the deterministic
   normal-form and unary branch-type constructions using variable-splitting
   resolutions. The nonlinear diagnostic illustrates why direct resolutions
   alone do not compose; it requires no change of choice semantics.
   The complete yield-context congruence is now proved. The unary normal
   form is also proved for the original continuity-bearing SetAlgebra
   interface; applying it to the repaired quotient is still outstanding.
2. Develop the deterministic-value and regular-word constructions needed
   for the actual unfold-automaton, using verified laws instead of assuming
   the original continuity requirement. Infinite pair Ramsey and stable
   idempotent factorization of words in a finite monoid are now proved.
3. Complete the parity-game and algebra-to-mu-calculus translations
   and effectivity claims. Preserve the original main statements; do not
   replace them with conditional or weakened results.
4. Review the original reachable syntactic-algebra obligations separately.
   The new automaton property does not instantiate its stronger old record.

## Source diagnostics

`REVIEW_ISSUES.md` records three independent checked problems: hole boundary
information is lost in the literal decomposition; intermediate pruning
breaks flattening associativity; and the outer-yield inclusion (*) used in
the syntactic continuity proof fails even for reachable input patterns.
Each diagnostic is kernel-checked without paper-statement assumptions.
The unpruned repair bypasses the third inclusion in its automaton-property
argument; it does not establish the paper's unrestricted continuity axiom.


## Finite families in expanded representatives

Follow v6 Corollary 46, keeping finite sums inside the context. The
flatten-resolution finite approximation underlying its proof is now
checked in `FiniteResolutionApproximation`. `ResolutionFamilies` and
`FiniteResolutionNormalForms` give finite actual-resolution families
preserving bounded profiles and contextual classes for finite
unfolding-invariant recognizers. `ExpandedContinuity` identifies expanded
evaluation and proves representative-independent contextual acceptance.
The full context/yield equality of Corollary 46 is now proved in
`YieldContinuity`, including arbitrary yields and root entries. The
connection to the remaining automata constructions still requires work;
no atomic-label continuity field has been added to the repaired algebra.


The corollary now also holds for the unpruned testing contexts:
`FiniteYieldContinuity` retains unreachable vertices until the final
observation. `FiniteContinuityOrder` gives the associated acceptance and
order criteria, and `ExpandedContinuity.finite_approximation` applies
them to evaluation of expanded representatives. The criteria quantify
over finite sums of base-alphabet yields. They do not collapse these to
single outer yields or establish the old unary normal form.


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


## Outcome of the original-continuity bridge attempt

`OriginalContinuityBridgeAudit.no_original_syntactic_algebra` now
refutes the original continuity-bearing syntactic-algebra existence
statement for an explicit unfolding-invariant language. The proof uses
a closing context with two differently labelled leaves to separate the
expanded unary-choice presentations at the level of syntactic classes.
This replaces the earlier open question about whether their different
yields actually give different classes. Original continuity and the
quotient-evaluation law force equality of these classes, so they cannot
both hold with the current semantics. Retain the proved expanded
continuity interface; further repair must change the algebraic argument
or the syntactic semantics, rather than assume the missing bridge.


## Expanded interface adopted (2026-09-18)

`ExpandedSyntacticAlgebra` now packages quotient substitution with expanded
continuity, proves existence and representative availability, and supplies
recognition, expanded yield order, finite resolution normal forms for
evaluations, and the syntactic automaton-property corollary. The original
continuity-bearing existence declarations were removed from the active
concept statements. The original generic set-algebra remains an explicitly
conditional interface. See PAPER_CHANGES.md for the replacement formulas
and the remaining transition-construction obligation.


## Iterated replacements and certificates (2026-09-18)

`FiniteVertexReplacement` proves the simultaneous local replacement step
on a finite presentation, using its actual surrounding contexts at every
stage. `FiniteDeterministicElements` proves realization by unary/nullary
presentations and substitution closure. `ExpandedCertificates` proves
soundness and completeness of the expanded-yield certificate criterion,
including equivalence to membership in the original language on systems.
The next automata obligation is to replace that branching-yield test by
the required finite-state branch condition; no path-only reduction is
asserted. See PAPER_CHANGES.md, items 9–10.


## Parallel successor witnesses (2026-09-18)

The local transition question is resolved by changing the witness: give
Uᵢ a private rooted m₀ vertex instead of one shared root feeding every
component. `SplitExtremal` proves the extremal comparisons and acceptance
preservation for this split witness. `ParallelReplacement.accepting_parallel`
provides an accepted parallel tuple below the original value. This matches
the branch-selection role described in Example 81 without claiming a
parallel normal form for every deterministic value. The next obligation
is run soundness for the resulting transition construction, followed by
the finite parity word condition. See PAPER_CHANGES.md, item 12.


## Actual runs and finite word evaluation (2026-09-18)

`ExpandedTransitions` provides the revised finite-type transition table,
its local acceptance-preserving choices, and the equivalence between input
membership and existence of a legal run with an accepted evaluated value.
This is separate from `Run.Accepting` for a word condition.
`RunPresentations` proves evaluation and unary-rank properties and transfers
acceptance to morphism observations. `FiniteBranchWords` constructs the
finite-state terminating-word test and proves agreement with path evaluation.
Next: finite and lasso observation maps, infinite-word condition and parity
representation, and soundness of the resulting branch tests. See the exact
scope and remaining obligations in PAPER_CHANGES.md, item 13.
