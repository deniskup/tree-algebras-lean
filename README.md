# Tree algebras and bisimulation-invariant MSO on finite graphs

Local Lax submission **lax-369799**, based on **arXiv:2407.12677v6**.

## Current status

This is a **concept draft**, not a completed formalization. The principal
statements and substantial supporting definitions have been written in
Lean. Seventeen supporting statements have proofs using only background
axioms; three further proofs have explicit unresolved dependencies. The
two main results remain open. A successful build checks the definitions, statement types, proof
terms, and Archive format; it does not discharge unproved statement
obligations. The concepts are not frozen or signed off.

Validation is being refreshed with `lax build tree-algebras --replay`.
The current development has 28 concepts and 20 Archive proofs: 17 use
background axioms only and three have explicit paper-statement dependencies.
The reverse direction of the logical equivalence is proved, as are all
six morphism/yield results and the first two flattening results. Eighteen
statement obligations have no proof yet. The independent context-decomposition
audit also passes with background axioms only.

The intended scope remains both main results of the paper and their
transitive proof dependencies. Technical constructions and external
automata/game-theoretic dependencies still need development. See
[PLAN.md](PLAN.md) for coverage and [REVIEW_ISSUES.md](REVIEW_ISSUES.md) for a
kernel-checked boundary case in the paper's context-decomposition lemma.

## Review entry points

- [Decomposition preserving all hole marks and self-loops](concepts/Lax369799/ContextDecomposition.lean),
  with [its proofs](proofs/Lax369799Proofs/ContextDecomposition.lean)

- [Morphism and yield proofs](proofs/Lax369799Proofs/Yields.lean),
  [pullbacks](proofs/Lax369799Proofs/Pullbacks.lean), and
  [flattening proofs](proofs/Lax369799Proofs/Flattening.lean)
- [Mu-calculus to MSO translation](proofs/Lax369799Proofs/MuToMSO.lean) and
  [bisimulation invariance](proofs/Lax369799Proofs/MuBisimulation.lean)
- [Finite MSO/bisimulation theorem](concepts/Lax369799/FiniteBisimulationTheorem.lean)
- [MSO syntax and semantics](concepts/Lax369799/MonadicSecondOrder.lean)
- [Mu-calculus syntax and semantics](concepts/Lax369799/ModalMuCalculus.lean)
- [Systems](concepts/Lax369799/RankedSystems.lean),
  [morphisms and yields](concepts/Lax369799/Morphisms.lean), and
  [flattening](concepts/Lax369799/Flattening.lean)
- [Algebras](concepts/Lax369799/Algebras.lean) and
  [set-algebras](concepts/Lax369799/SetAlgebras.lean)
- [Algebra-to-automaton theorem](concepts/Lax369799/AlgebraToAutomaton.lean)
- [Algebra-to-mu-calculus theorem](concepts/Lax369799/AlgebraToMuCalculus.lean)

## Representation choices

Finite vertex sets are enumerated by `Fin size`. This makes systems a
ranked set in the same universe as their labels, so iterated systems and
flattening have ordinary Lean types. Isomorphism invariance removes any
mathematical dependence on the enumeration. System constructions first
use a finite presentation, then restrict to its reachable part. Directions
and variables use zero-based indices.

MSO and the modal mu-calculus are syntactic inductive types with explicit
semantics, not uninterpreted predicates. The main theorem quantifies over
finite reachable transition systems and a finite proposition alphabet.
The mu-calculus uses positive fixed-point variables in negation normal
form and the standard least/greatest fixed-point semantics.

Unfold-automaton runs may choose another finite representative of the
same regular tree. Their acceptance checks every finite maximal branch
and every infinite branch. A deterministic parity word automaton supplies
the regular branch condition; equivalence with the paper's arbitrary
omega-regular conditions is a dependency to prove, not an assumption
hidden in a definition.

## Commands

```sh
lax build .
# Kernel check of the independent source diagnostic:
(cd concepts && lake env lean ../audit/ContextDecomposition.lean)
```

`reference/` contains the exact downloaded source archive, its SHA-256
provenance, and extracted TeX. It is ignored by Git and is not a declared
Archive paper. The Lean submission is Apache-2.0; upstream source material
retains its original notices. The author list is left empty for review.
Nothing has been submitted to or registered with the public Archive.
