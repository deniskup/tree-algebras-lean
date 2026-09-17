# Extending the extremal-context argument

This records the continuation of the checked boundary-preserving
context decomposition. `ExtremalContexts.lean` now defines the planted
normal contexts, the components Uᵢ, and Delta. Delta's determinism has a
ground proof. Finite minimization over boundary data and unary values is
proved using the ground set-algebra order laws. The algebraic normal form, both comparison inequalities, and the resulting
automaton-property theorem now have ground Archive proofs.

Plant invariance lets the automaton-property proof work with planted
contexts. After planting, the hole's two marks merge into a single root
flag r. Retain also its set L of self-loop directions. The algebraic
normal form is written N(r,L;m₀,…,mₖ): the vertex m₀ is
root, each unary mᵢ points to the hole, the hole's direction i points to
mᵢ (i≥1), the hole has self-loops in L, and the hole is root if r holds.
There are no initial vertices. This is a set-context with an ordinary
hole vertex.

The proved algebraic decomposition lemma identifies the value of
N(r,L;p₀,…,pₖ)[b] with that of plant(C[b]) for every b. Here pᵢ are the
values of the unary pieces, after removing their hole alphabet and
trimming them. Its proof uses the evaluation/congruence lemmas; it does
not follow just by applying evaluation to the existing structural cover.

For the extremal choice, minimize over BOTH the unary tuple and the
boundary data. Order the unary values by the algebra order, and boundary
data by reverse inclusion: adding a root mark or a self-loop makes the
context smaller. There are finitely many possibilities at fixed k.
Minimize among accepting choices below the data of plant(C). Minimality
then has three consequences whenever the corresponding extension remains
accepting:

- Replacing mᵢ by mᵢ ∧ t forces mᵢ ≤ t.
- Adding the root mark forces it to have already been present.
- Adding loop i forces i to have already belonged to L.

Modify the paper's Uᵢ by adding the loops L at its central a-vertex.
Keep its initial a-vertex, the mⱼ loops, and the extra exit in direction i.
Construct Delta from the Uᵢ as in the paper, with root m₀; additionally,
make every central a-vertex a root when r holds. These extra root marks
can also be placed on the Uᵢ vertices of the outer unary presentation.
Consequently Delta still evaluates to a deterministic element: its
components Uᵢ are unary, and its outer presentation uses unary labels.

The projection N(r,L;m)[Delta] → N(r,L;m)[a] preserves all added
marks and edges: each copied a maps to the hole position occupied by a,
and a glued exit from a loop direction maps to the retained self-loop.
This is the acceptance-preservation half of the original argument.

For the comparison with an arbitrary planted D = N(r',L';t), the usual
subsystem of plant(D[Delta]) around Uᵢ still gives mᵢ ≤ tᵢ. The subsystem
used for m₀ also remains available. Two further subsystems are needed:
if r' holds, a central a in Uᵢ is root, giving acceptance of N with its
hole made root; and if i belongs to L', the exit of Uᵢ returns to its own
initial a, giving acceptance of N with loop i added. Boundary minimality
therefore gives r' → r and L' ⊆ L. Together with mᵢ ≤ tᵢ, these
relations provide the final context comparison.

These subsystem maps, the algebraic normal form, the extremal choice,
and the final inequalities have all been checked by kernel replay. Fixing boundary data
throughout minimization would omit the last two minimality conclusions
and would not justify comparison with arbitrary contexts D.

The implementation is in `AlgebraicDecomposition.lean`, `DeltaContext.lean`,
`DeltaComparison.lean`, and `AutomatonProperty.lean` under the proof namespace.
For each unary comparison, a two-vertex unary system evaluates to the meet
of the extremal and testing values. Its flattening embeds into the test
of Delta. Extremality then yields the unary inequality. The proof of
`automaton_property` no longer assumes any paper statement.
