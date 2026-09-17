# Substitution without intermediate pruning

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

The full paper is not yet formalized. Rankwise finiteness, the automata and
logic constructions, and their external dependencies remain outstanding.

## Next obligations

1. Complete the resolution and small-profile refinement arguments to prove
   finiteness of the contextual quotient. Finite variable compression and
   variable-renaming laws are now available. Bounded small-profile quotients
   are finite also for unpruned presentations, and every contextual class
   has a reachable representative. Refinement of contextual equivalence
   by those bounded profiles still needs proof. Treat empty unary pieces and
   direct hole loops carefully in context smallification.
2. Develop the deterministic-value and regular-word constructions needed
   for the actual unfold-automaton, using verified laws instead of assuming
   the original continuity requirement.
3. Complete the bisimulation, MSO, parity-game, and mu-calculus translations
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
