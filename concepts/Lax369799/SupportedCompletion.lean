import Lax369799.SupportEvaluation

/-!
---
title: Extending supported algebras and preserving recognition
type: theorem
---
The quotient of arbitrary systems by their supported-evaluation profiles
is an algebra. Evaluation chooses inner representatives and flattens;
substitution congruence and the deterministic substitution laws make it
well defined and associative. The construction preserves finite sorts
and closed recognition. Recognizability using the fully supported systems
of Definition 6 is therefore equivalent to recognizability using arbitrary
deterministic presentations.
-/

namespace Lax369799.SupportedCompletion
open RankedSystems Morphisms
open SupportEvaluation (Carrier classMap)

axiom algebra {B : RankedSet} (E : SupportedAlgebras.Algebra B) :
    ∃ D : Algebras.Algebra (Carrier E), ∀ n (P : System (System B) n) (U : System B n),
      Lax369799.Flattening.SystemFlattening P U →
        D.eval n (relabelSystem (classMap E) P) = classMap E n U

axiom legacy_recognizable {A : RankedSet} (L : Algebras.Language A)
    (hL : SupportedAlgebras.Recognizable L) : Algebras.Recognizable L

axiom recognizable_iff {A : RankedSet} (L : Algebras.Language A) :
    SupportedAlgebras.Recognizable L ↔ Algebras.Recognizable L

/-- Map a letter to the class of its atomic presentation. -/
def letter {B : RankedSet} (E : SupportedAlgebras.Algebra B) : RankedMap B (Carrier E) :=
  fun n b => classMap E n (atomicSystem b)

open SupportEvaluation (Equivalent)

axiom profile_morphism {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) {n : ℕ} (S T : System B n)
    (f : Morphism S.val T.val) : Equivalent E S T

axiom profile_unfold {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) {n : ℕ} (S T : System B n)
    (h : UnfoldEquivalent S.val T.val) : Equivalent E S T

axiom eval_letters {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (D : Algebras.Algebra (Carrier E))
    (hD : ∀ n (P : System (System B) n) (U : System B n),
      Flattening.SystemFlattening P U → D.eval n (relabelSystem (classMap E) P) = classMap E n U)
    {n : ℕ} (S : System B n) :
    D.eval n (relabelSystem (letter E) S) = classMap E n S

axiom regular_completion {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) :
    ∃ D : Algebras.Algebra (Carrier E), Algebras.UnfoldInvariant D ∧
      ∀ n (S : System B n), D.eval n (relabelSystem (letter E) S) = classMap E n S

axiom unary_card_bound {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) : Nat.card (Carrier E 1) ≤ Nat.card (B 0) + Nat.card (B 1)

end Lax369799.SupportedCompletion
