# Substitution without intermediate pruning

The user authorized choosing a working repair of the flattening issue.
The first verified step is `FinitePresentations`: arbitrary finite
presentations, with reachability kept as an additional property.
Flattening retains all vertices. `UntrimmedFlattening` proves the
associativity isomorphism, both atomic unit isomorphisms, and naturality.
FiniteContexts now proves composition and extension by system-valued
labels. FiniteContextualOrder proves contextual congruence, acceptance,
isomorphism invariance, and simultaneous monotonicity of flattening.
FiniteSyntacticAlgebra constructs the quotient substitution algebra and
proves recognition; FiniteAcceptance instantiates it with yield acceptance.

The old reachable `SetSystem` definitions and their conditional algebra
proofs remain intact while this repair is developed. They must not be
identified with the new presentations without a proved bridge.

## Next obligations

1. Contexts, contextual equivalence, quotient evaluation, and recognition
   are proved. These constructions allow unreachable holes and preserve
   roots introduced by later substitutions.
2. The quotient partial order, monotone evaluation, accepting-filter
   properties, and meet characterization are proved. Covers lift through
   substitution in a fixed context, giving contextual idempotence of sum.
   Recognition is now explicitly connected to deterministic reachable
   systems and the original regular-tree language. Rankwise finiteness
   remains open.
3. Check each additional set-algebra law against this construction before
   making it an interface requirement. In particular, old local covers
   may miss unreachable vertices carrying rooted labels; old continuity
   over yields can ignore those contributions. Neither law transfers
   merely by removing pruning.
4. Adapt the finite extremal-context and automata arguments to the laws
   actually proved. The original conditional proof of the automaton
   property is available, but does not by itself supply an instance of
   the repaired algebra.
5. Preserve the finite-graph/MSO main statements. Do not present a weaker
   conditional statement or an unproved new algebra law as their proof.

Validation checkpoint: full Archive kernel replay passes with 39 concepts,
77 proofs (74 ground, three relative), and the three intentional generated
constructor-helper warnings.
