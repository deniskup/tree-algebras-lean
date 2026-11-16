# Formalization plan and coverage

The user clarified the completion target on 14 November 2026: **Theorem 2
and effectivity, including their supporting lemmas**. This scope is complete.
The full numbered inventory is retained separately in `paper-coverage.json`;
unrestricted Theorem 1 and exhaustive side-statement alignment are outside
this clarified target.

The active source is `main_tree_algebra_longversion.pdf` (56 pages), SHA-256
`09ffc3269d3548b28b92a913c3f1335156fa5fa3a2eeaebe1421e984e6699ff3`.
The final replay counts, capture digest, source hashes and axiom audits are
recorded in `validation-report.json`: 213 concepts, 244 proof modules and
566 ground proofs. No declared statement is unproved or relative.
The 77 retained helper warnings concern generated structure lemmas,
ancillary word-automaton/parity-game lemmas, and one shared simplification
lemma used during proof elaboration. Four unused local lemmas were removed
and three copies of that simplification lemma were consolidated into one
in the pre-submission review. Compiler correctness
has one Archive statement, at the main effective endpoint; the compiler
module supplies its reusable proof helper.
The shared `FinitePresentations.FlattenedVertex` abbreviation also keeps
the two formerly unrenderable dependent signatures readable in the Archive
inspector, without changing their mathematical types.

| Paper stage | Checked modules | Status |
| --- | --- | --- |
| §2, supported systems and unpruned substitution | `SupportedSystems`, `FinitePresentations`, `SupportedMorphisms`, `SystemMonad`, `SupportPorts` | Ground |
| §3, supported algebra recognition | `SupportedAlgebras`, `SupportEvaluation`, `SubstitutionProfiles`, `SupportedCompletion` | Ground |
| §4, yield-syntactic algebra and finite profiles | `FiniteSyntacticAlgebra`, `SetSystemAlgebras`, `BoundedProfileRefinement`, `SupportedProfiles` | Ground |
| §5, extremal situations and automaton property | `ExtendedContexts`, `ExtremalSituations`, `ClosedExtremal`, `DirectionProjections`, `ExtremalPaths` | Ground |
| §6.2, MSO recognition | `SetLogicTranslation`, `SetLogicRecognition`, `MSORecognition` | Ground |
| §6.3, algebra to automata | `OmegaProducts`, `AlgebraicBranchCondition`, `RunAcceptance`, `AlgebraToAutomaton` | Ground |
| §6.4, cloning and modal translation | `CloneNormalization`, `AutomatonRunGame`, `CloneGameRun`, `ModalGameTranslation`, `BisimAutomatonTheorem` | Ground |
| Theorem 2 | `MainTheorems.finite_bisimulation_invariant_mso` | Both implications ground |
| Effectivity: quantitative algebra/profile bounds | `QuantitativeRecognition`, `QuantitativeProfiles` | Ground, numeric bounds computed from syntax |
| Effectivity: finite automaton bounds | `QuantitativeDeterminization`, `QuantitativeWordConditions`, `QuantitativeAutomata` | Ground |
| Effectivity: finite model/separation bound | `ParityGameSimulation`, `ModalSmallModels`, `QuantitativeFiniteTheorem` | Ground, derived from finite positional games |
| Effectivity: executable selection | `FiniteModelChecking`, `FiniteModalData`, `FiniteTesting`, `EffectiveFiniteTranslation` | Total compiler and promised correctness ground |
| Main effective endpoint | `MainTheorems.effective_finite_bisimulation_invariant_mso` | Ground |

The algorithm accepts an explicitly encoded finite vocabulary. It never
requires a decision procedure for bisimulation invariance. Finite table
completeness supplies one correct candidate under that promise; the
pair-separation bound proves that every passing selected candidate is
correct on all finite reachable systems.

The small-model proof uses two alternating simulations. First merge the
input vertices at each word state and transfer a winning strategy. A
positional strategy chooses one local transition per word state. Retain
its supported successors and restrict to reachable states. A second
simulation proves acceptance of the resulting model, whose size is at
most the number of word states. No unrestricted-tree theorem or assumed
mu-calculus satisfiability result is used.

`audit/RevisedStructure.lean` covers the revised endpoints and both main
theorems. `audit/EffectiveFiniteTranslation.lean` executes the finite
components and prints the main proof axioms. The complete declared proof
network must remain ground; paper-statement axioms are interface declarations
whose implementations are supplied in the proof package.

The broader inventory now has 59 matched numbered claims and three partial
alignments (Theorem 1 and Lemmas 42/47). Lemmas 46, 81 and 82 now have explicit
supported endpoints. That inventory does not alter the complete checked
route for the clarified target.

The following sections are historical plans, preserved with their earlier
numbering and checkpoint status. Their open-item descriptions are superseded
by this status and the validation report.

## Earlier development plan (v6)

Target: Colcombet–Doumane–Kuperberg, arXiv:2407.12677v6. Keep the full
transitive scope; do not regard an assumed concept statement as a proof.
Follow `/home/denis/lax/lax_instructions.txt`: prepare and review concepts,
then freeze approved interfaces and implement proofs. Significant changes
after that point need explicit confirmation.

## Draft concepts by part of the paper

| Paper part | Modules | Current coverage |
| --- | --- | --- |
| 2.1–2.2 | RankedSystems | Ranked sets, finite reachable presentations, deterministic systems, atomic systems, relabelling, sum, plant, uproot |
| 2.3–2.5 | Morphisms, MorphismTheorems | Morphisms, local surjectivity, isomorphism, unfolding, regular-tree quotient, direct resolutions, yields; composition, pullback, equivalence and yield statements |
| 2.6–2.9 | Flattening, Resolutions, FlatteningTheorems, PresentationCovers, ContextDecomposition | Concrete flattening, one-hole contexts, plugging, renaming, resolutions, flatten-resolutions; preservation and congruence statements |
| 3 | Algebras | Evaluation, isomorphism invariance, unit/associativity, algebra morphisms, recognition, language unfold-invariance |
| 4.1 | SetAlgebras, SetAlgebraTheorems, EvaluationTheorems | All set-algebra axioms, derived meet/order, order and yield statements |
| 4.2–4.3 | SyntacticOrder, Resolutions, SyntacticAlgebraTheorems | Contextual preorder, quotient, quotient-evaluation specification, profiles, small profiles, finiteness/refinement statements |
| 5 | AutomatonProperty, AutomatonPropertyTheorem, ExtremalContexts | Deterministic elements, automaton property, plant invariance, order separation, principal sufficient-condition and syntactic statements |
| 6.1 | TransitionSystems, TransitionEncoding, EncodingTheorems, RankedBisimulation, BisimulationQuotient, RankedLifting | Ranked encoding and both directions of bisimulation equivalence proved through a common finite quotient and direction duplication |
| 6.2 | MonadicSecondOrder, SetLogic, SetLogicTranslation, SetLogicRecognition, MSORecognition, PathAlgebra, RecognitionProjection | Full MSO recognition proved, with singleton translation, finite atomic algebras, Boolean closure and set projection |
| 6.3 | UnfoldAutomata, AlgebraToAutomaton | Finite type sets, parity word condition, runs/branches, recognition statement |
| 6.4 | BisimAutomata, BisimAutomatonTheorem, ModalMuCalculus, AlgebraToMuCalculus, MuCalculusTheorems, FiniteBisimulationTheorem | Full mu-calculus syntax/semantics, algebra-to-mu statement, standard reverse-direction dependencies, main equivalence |

Two hundred and seventy statements now have Archive proofs using background axioms
only, including the complete boundary-preserving automaton-property
argument. Its algebraic decomposition, extremal choice, both Delta
inequalities, and boundary and unary-piece comparisons are proved.
Two further proofs expose unresolved dependencies: the algebra-to-mu
reduction and the main logical equivalence. Syntactic rankwise finiteness
is now proved without paper-statement assumptions.
Acceptance, yields of sums, and syntactic recognition conditional on a
syntactic algebra are now ground as well. All four independent source
diagnostics in `audit/` are kernel-checked. There are 277 declared statements:
272 have Archive proofs (270 ground and two relative), and 5 have no proof.

The literal flattening associativity lemma fails with intermediate
reachability pruning. The user authorized a repair. FinitePresentations, FiniteContexts,
FiniteContextualOrder, FiniteSyntacticAlgebra, and FiniteAcceptance now
provide an unpruned substitution algebra with proved context, quotient,
order, meet, morphism, and cover laws. FinitePlant, FiniteEvaluation,
FiniteDecomposition, FiniteNormalForms, and FiniteExtremal now support a
complete proof of its automaton property under finiteness of the unary
sort, without continuity. Rankwise finiteness for unfold-invariant recognizable languages is proved;
the actual automata obligations remain. See
REPAIR_PLAN.md. Do not silently identify this algebra with the original
record containing the unverified continuity requirement.

## Work needed before the concept scope is complete

1. The repaired structural and algebraic decomposition and the complete
   extremal-context argument are proved. Keep their difference from the
   literal v6 construction explicit; see EXTREMAL_REPAIR.md.
2. The repaired syntactic substitution algebra and its automaton property
   and rankwise finiteness are proved for unfold-invariant recognizable languages.
   Review the additional old set-algebra requirements separately.
3. Smallification and optimal flatten-resolution from Section 4.3 are proved.
   DeterministicPieces proves the empty/identity versus unary-system split
   and compression preserving loop flags with bound |B₁|+1. FiniteProfiles
   proves finiteness for every fixed bound; SystemEvaluation proves renaming
   congruence. DeterministicNormalForms proves the complete optional-unary
   normal form, including arbitrary deterministic substitution. ContinuationCompression proves evaluation preservation and the full local
   smallification lemma, including arbitrary letter maps into a recognising
   algebra. ResolutionCompression preserves flatten-resolution witnesses
   and fibre bounds. OptimalResolutions supplies the optimal outer construction.
   RootExpansion and the observation-transfer modules handle initial and root
   entries, including unreachable outer components. BoundedProfileRefinement
   proves refinement and rankwise finiteness of the repaired quotient.
   ReachableFiniteness transfers finiteness to the original reachable quotient.
   The original profile bound without the additional identity value remains open.
4. Regularization now converts an arbitrary finite recognizing algebra into
   an unfolding-invariant one. GeneratedAlgebra restricts to realized values;
   PolynomialContexts and PolynomialQuotient give evaluation congruence and
   quotient algebra laws. PolynomialUnfolding supplies unfolding invariance.
   The automaton-property theorem now applies with the paper’s ordinary
   recognizability hypothesis. Continue the deterministic-element normalization and unary branch-type
   construction using resolutions with variable-origin maps. The nonlinear
   example is the paper’s motivation for resolutions, and is now checked
   positively as an explicit flatten-resolution (see REVIEW_ISSUES.md).
   ResolutionLifting proves renaming lift and resolution transfer;
   YieldSubstitution and YieldObservations now prove flattening monotonicity
   and the original yield-context congruence, including root yields.
   UnarySystems proves uniqueness of variable exits and yield decomposition
   into variable-specific copies. DeterministicElements now proves the
   positive-rank unary normal form under the original explicit SetAlgebra
   hypothesis, including continuity. Instantiating that hypothesis for the
   repaired quotient remains an open obligation.
5. Develop the compression construction and the modal parity acceptance-game
   translation from Section 6.4. The duplication condition and the two
   top-level bisim-automaton statements are present, but their construction
   and game interfaces are not yet defined.
6. InfiniteRamsey now proves the infinite pair-coloring theorem, and
   WordFactorization proves idempotent block factorization in a finite
   monoid, with a stable nonempty prefix. WordParity proves the unique
   least recurring priority, prefix-shift invariance of recurrence, the
   recurring minimum-priority cycle, and its acceptance criterion.
   PeriodicPaths constructs an ultimately periodic witness with the same
   minimum recurring priority, proving the periodic-path test.
   UnfoldBranches applies that test to unfold-automaton runs through the
   product of vertices, directions, and word-automaton states.
   AlgebraicTransitions defines the finite-type transition table and proves
   its context acceptance lemma under an explicit set-algebra automaton
   property. Constructing its word condition and the full recognition
   equivalence remain outstanding.
   Section 6.1 is now ground: EncodingBisimulation proves the full ranked
   versus ordinary bisimulation equivalence. The main logical proof now
   uses ground encoding and mu-calculus support, with only MSO recognition
   and algebra-to-mu remaining as its two explicit assumptions.
   Continue the regular-word
   acceptance and finite parity-game facts used in Sections 6.3–6.4;
   expose substantial dependencies as separate concepts.
7. Add the effectivity claim and its coding/size-bound definitions. The present
   existential main statement does not assert a computable translation.
8. Review all formal statements against active v6 TeX (ignore commented-out
   earlier versions). Inspect the generated pages and obtain concept sign-off.

## Proof route after interface review

1. Structural system lemmas: morphisms, pullbacks, flattening, resolutions (including the proved deterministic resolution factorization),
   context congruence, continuity of yields.
2. Algebraic lemmas: meet/order laws, syntactic set-algebra construction and
   recognition, small-profile bounds, and syntactic rankwise finiteness.
3. Automaton property: repaired context normal form, extremal choices,
   deterministic witnesses, and acceptance preservation.
4. Automata: regular branch conditions, both recognition implications,
   bisimulation normal form, modal automata and mu-calculus translation.
5. Logic: MSO recognition by induction, encoding correctness, mu-to-MSO
   translation and bisimulation invariance; assemble the finite main theorem.
6. Effectivity, remaining paper statements, and full dependency audit.

Proofs may temporarily depend on separately declared Lax statements, but a
final submission is complete only when the transitive proof network closes
using the permitted background axioms. No `sorry`, custom hidden axiom,
circular proof, or definitional replacement of the main theorem is acceptable.

## Library survey

The local Lax database was searched for tree algebras, bisimulation, modal
mu-calculus, parity games and Ramsey theory. No matching tree-algebra or
bisimulation development was located. `lax-345067` is a registered finite
Ramsey submission in the current environment, at
`https://github.com/lax-archive/lax-submissions`, folder `finite-ramsey-v4-33`,
commit `feabf43dcd6967ac912b2064003ea715e06e58f9`. Its suitability for the
infinite-word factorisation argument has not been established; it has not
been added as a dependency. Mathlib supplies finite types, quotients,
relations, complete lattices, cardinalities and elementary parity facts.

## Validation

Run `lax build .` for both packages and all Archive inspections. Run the
standalone context-decomposition audit separately. On completion, inspect
all proof axiom sets and the complete transitive proof network. A passing
concept build alone is not evidence that a paper theorem has been proved.

## Additional logic foundations

The encoding/bisimulation equivalence is now a ground proof in both
directions. Finite bisimulation quotients and ranked morphism liftings
supply the reverse direction. Boolean closure, inverse relabelling, the
nonempty powerset algebra, existential projection, and the initial-label
algebra are proved. The translation from mixed MSO syntax to pure
second-order syntax is proved, including singleton definability. The
recognition induction has explicit atomic-language hypotheses, all of
which are now discharged using initial-label and finite path-summary
algebras. MSORecognition.mso_recognizable is a ground proof. The main
logical equivalence now depends only on algebra_to_mu; that theorem still
depends on the two bisim-automaton construction/translation statements.
The 2026-09-18 replay checks 117 concepts, 272 Archive proofs (270 ground),
and 277 statements, leaving five statements without proofs.

Finite-semigroup factorization now also preserves a recurrent vertex at
all block boundaries. The pending continuity/unary-normal-form question
is isolated in REVIEW_ISSUES.md and audit/NonlinearSubstitution.lean; the
conditional distributivity consequence is checked without paper axioms.


The expanded-representative route follows Corollary 46: finite sums of
yields stay inside the context, preserving independent choices at
multiple occurrences. The underlying flatten-resolution approximation
is proved in `FiniteResolutionApproximation`; the full context equality is proved in `YieldContinuity`, including
root yields and arbitrary finite families of yields. Finite resolution families preserving bounded profiles
and contextual classes are proved in `FiniteResolutionNormalForms`.
`ExpandedContinuity` proves the associated representative-independent
acceptance statements. These do not supply the original atomic-label
continuity hypothesis for the unary normal-form theorem.


## Expanded continuity via Corollary 46

`YieldContinuity.continuity` proves the corollary for the paper's
reachable set-contexts. `InitialResolutionApproximation` and
`RootResolutionApproximation` prove finite support for observations of
arbitrary finite presentations. `FiniteYieldContinuity` therefore
extends the corollary to the unpruned contexts used by the repaired
quotient. `FiniteContinuityOrder` characterizes contextual acceptance
and order by finite sums of yields. Finally,
`ExpandedContinuity.finite_approximation` applies this characterization
to the evaluation of a chosen expansion. These proofs preserve finite
sums inside each testing context; they do not use inclusion (*).

The remaining distinction is between this base-alphabet approximation
law and continuity on atomic algebra labels. The latter still implies
the unary distributivity law isolated in the audit. Applying the old
unary normal-form theorem to the repaired quotient remains unjustified.


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


The subsequent original-continuity bridge audit is conclusive:
`OriginalContinuityBridgeAudit.no_original_syntactic_algebra` refutes
`syntactic_algebra_exists` with the current definitions, for the checked
unfolding-invariant language `OriginalContinuityBridgeAudit.language`.
The original existence declaration has now been removed and replaced by
`ExpandedSyntacticAlgebra.syntactic_algebra_exists`, with a ground proof.
The original syntactic automaton-property existence declaration has likewise
been replaced by the proved expanded-interface corollary. Its failure
does not affect the ground proofs for the repaired substitution algebra
or the expanded continuity law. See REVIEW_ISSUES.md for the closed
context and the exact contradiction.


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


## Mathematical question at the transition construction

A further audit of §6.3 separates local transition completeness from run
soundness. The extremal witness includes a rooted m₀ vertex pointing to
all Uᵢ components, whose expansion retains mixed choices. A specialized
parallel replacement theorem or a finite construction encoding that joint
condition is still needed. The false general unary-distributivity law
cannot be used. See PAPER_CHANGES.md, item 11, for the precise obligations
and the question sent to the author. No new theorem or axiom was added
merely to assume this conversion.


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


## Branch graphs and parity plumbing (2026-09-18)

`RunBranchObservations` proves the terminating and regular infinite branch
observation maps, and their acceptance consequences. `RegularBranchWords`
proves finite graph representation of periodic branches and reduction of
all infinite-branch parity tests to these graphs. `CombinedWordCondition`
combines the finite evaluator with an arbitrary parity condition.

The author question about the expanded-continuity soundness bridge is
recorded in PAPER_CHANGES.md, item 14. No proof of the end-of-§6.3 theorem
has been registered. The algebraic infinite-word condition, its parity
realization, the direct/recursive finite-path identification, and that
soundness bridge remain open.


## Choice-preserving selected unary types (2026-09-18)

The author requires final unary types to expose all branching choices.
`ChoicePreservingUnary` formalizes the necessary law on closed
continuations and proves the finite-expression branch test. The subtype
is finite. The split extremal lower bound now includes rank one, and
`accepting_parallel` no longer returns an arbitrary unary value in that
case. The exact extremal acceptance characterization is proved.

The component-selection step is now proved by a second, rank-one extremal
refinement. `SelectedChoicePreservation` proves choice preservation on
closed continuations; `SelectedParallel` preserves acceptance and the
parallel lower bound while refining every component. Legal transitions
now require the selected components, and their existence and algebraic
run characterization have been re-proved with that restriction.

Next: cyclic branch soundness, the direct/recursive finite-path
identification, and the algebraic infinite-word condition with its parity
realization. There is no pending author question about component selection.
See PAPER_CHANGES.md, item 15, for the proof and required paper change.


## Cyclic choice splitting and finite path identification (2026-09-18)

Fourteen further statements are proved. `ContextChoices` splits outgoing
choices at a selected unary hole, including self-loops and feedback.
`GraphChoices` iterates this over finite cyclic graphs and restricts the
test to choices of existing successors. `RunPresentations.functional_test`
applies it to actual legal runs. All vertices remain in the restrictions.

`FinitePathEvaluation` and `RunBranchObservations.path_evaluation` identify
the direct finite path with the recursive word evaluator.
`RunWordCondition` now tests those paths with finite encoded actions and
retains any supplied infinite-word parity condition.

Next: prove that accepted finite/regular branch observations provide
acceptance of each admissible functional run restriction. Use a covering
family of path/cycle components, with unmarked components for vertices
that become unreachable after successor selection; do not prune them
before evaluation. Then construct the algebraic infinite-word condition
and its parity realization. See PAPER_CHANGES.md, items 16–17.
