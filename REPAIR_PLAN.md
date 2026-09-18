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
