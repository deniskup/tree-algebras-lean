# Formalization plan and coverage

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
| 6.1 | TransitionSystems, TransitionEncoding, EncodingTheorems | Usual bisimulation, ranked decoding, generated ranked bisimilarity, encoding and equivalence statements |
| 6.2 | MonadicSecondOrder, MSORecognition | Full MSO syntax/semantics and the recognition statement |
| 6.3 | UnfoldAutomata, AlgebraToAutomaton | Finite type sets, parity word condition, runs/branches, recognition statement |
| 6.4 | BisimAutomata, BisimAutomatonTheorem, ModalMuCalculus, AlgebraToMuCalculus, MuCalculusTheorems, FiniteBisimulationTheorem | Full mu-calculus syntax/semantics, algebra-to-mu statement, standard reverse-direction dependencies, main equivalence |

One hundred and sixty-seven statements now have Archive proofs using background axioms
only, including the complete boundary-preserving automaton-property
argument. Its algebraic decomposition, extremal choice, both Delta
inequalities, and boundary and unary-piece comparisons are proved.
Two further proofs expose unresolved dependencies: the algebra-to-mu
reduction and the main logical equivalence. Syntactic rankwise finiteness
is now proved without paper-statement assumptions.
Acceptance, yields of sums, and syntactic recognition conditional on a
syntactic algebra are now ground as well. All four independent source
diagnostics in `audit/` are kernel-checked. There are 179 declared statements:
169 have Archive proofs (167 ground and two relative), and 10 have no proof.

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
   recognizability hypothesis. The next issue is the deterministic-element
   normalization used to extract unary branch types: nonlinear substitution
   does not distribute over variable choices (see REVIEW_ISSUES.md).
5. Develop the compression construction and the modal parity acceptance-game
   translation from Section 6.4. The duplication condition and the two
   top-level bisim-automaton statements are present, but their construction
   and game interfaces are not yet defined.
6. Formalize the regular-word acceptance facts, Ramsey factorisation and
   finite parity-game facts used in Sections 6.3–6.4; expose substantial
   dependencies as separate concepts rather than opaque assumptions.
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
