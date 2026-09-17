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
