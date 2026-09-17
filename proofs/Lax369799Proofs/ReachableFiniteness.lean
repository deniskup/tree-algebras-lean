import Lax369799Proofs.BoundedProfileRefinement
import Lax369799Proofs.FiniteProfiles

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.ReachableFiniteness
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.SyntacticOrder
open Lax369799.FinitePresentations

private def context {A : RankedSet} {k n : ℕ} (C : Lax369799.Flattening.SetContext A k n) :
    Lax369799.FiniteContexts.Context A k n := ⟨ofSetSystem C.system, C.one_hole⟩

private theorem plug_acceptance {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) (F : Set (B 0)) (L : Language A) (hL : Recognizes E η F L)
    {n : ℕ} (C : Lax369799.Flattening.SetContext A n 0) (S : SetSystem A n) :
    Lax369799.FiniteAcceptance.Accepting L (Lax369799.FiniteContexts.plug (context C) (ofSetSystem S)) ↔
      Accepting L (Lax369799.Flattening.plug C S) := by
  let P := (relabel (Lax369799.FiniteContexts.substitution (ofSetSystem S)) (ofSetSystem C.system)).graph
  have he := BoundedProfileRefinement.enumerate_acceptance E hE η F L hL (flattenPresentation P)
  have hsub : Lax369799.FiniteContexts.substitution (ofSetSystem S) =
      fun k a => ofSetSystem (Lax369799.Flattening.substitution S k a) := by
    funext k a
    cases a with
    | inl a => rfl
    | inr e => cases e with | up e => cases e; rfl
  have hg : trim (flattenPresentation P) = Lax369799.Flattening.plug C S := by
    exact congrArg (fun f : RankedMap (Lax369799.Flattening.WithHole A n) (FiniteSystem A) =>
      trim (flattenPresentation (relabel f (ofSetSystem C.system)).graph)) hsub
  exact he.trans ((AcceptanceObservations.accepting_iff_values E hE η F L hL
    (flattenPresentation P)).symm.trans (by rw [hg]))

private theorem equivalent {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) (F : Set (B 0)) (L : Language A) (hL : Recognizes E η F L)
    {n : ℕ} (S T : SetSystem A n)
    (h : Lax369799.FiniteContextualOrder.Equivalent (Lax369799.FiniteAcceptance.Accepting L)
      (ofSetSystem S) (ofSetSystem T)) : SyntacticEquivalent L S T := by
  constructor
  · intro C hc
    exact (plug_acceptance E hE η F L hL C T).mp
      (h.1 (context C) ((plug_acceptance E hE η F L hL C S).mpr hc))
  · intro C hc
    exact (plug_acceptance E hE η F L hL C S).mp
      (h.2 (context C) ((plug_acceptance E hE η F L hL C T).mpr hc))

/--
---
conclusion: Lax369799.SyntacticAlgebraTheorems.syntactic_rankwise_finite
---
Every class of the finite-presentation contextual quotient has a reachable
representative. Equality of such classes implies equality in the original
reachable contextual quotient, since every original context is a finite
context with the same final observation. This gives a surjection from the
finite repaired quotient onto the original syntactic quotient.
-/
theorem syntactic_rankwise_finite {A : RankedSet} (L : Language A)
    (hL : RegularTreeRecognizable L) : RankwiseFinite (SyntacticCarrier L) := by
  classical
  have hf := BoundedProfileRefinement.finite_carrier L hL
  obtain ⟨B, E, η, F, _, hE, hrec⟩ := hL
  intro n
  let Y := Lax369799.FiniteContextualOrder.Carrier (Lax369799.FiniteAcceptance.Accepting L) n
  let : Finite Y := hf n
  let st : Setoid (FiniteSystem A n) := {
    r := Lax369799.FiniteContextualOrder.Equivalent (Lax369799.FiniteAcceptance.Accepting L)
    iseqv := ⟨fun _ => ⟨fun _ h => h, fun _ h => h⟩,
      fun h => ⟨h.2, h.1⟩,
      fun h h' => ⟨fun C hc => h'.1 C (h.1 C hc), fun C hc => h.2 C (h'.2 C hc)⟩⟩ }
  let representative (a : Y) := Classical.choose (FiniteProfiles.reachable_representative L a)
  have rep (a : Y) : Lax369799.FiniteContextualOrder.quotientMap
      (Lax369799.FiniteAcceptance.Accepting L) n (ofSetSystem (representative a)) = a :=
    Classical.choose_spec (FiniteProfiles.reachable_representative L a)
  let f : Y → SyntacticCarrier L n := fun a => syntacticMap L n (representative a)
  apply Finite.of_surjective f
  intro x
  induction x using Quot.inductionOn with
  | h S =>
    let a : Y := Lax369799.FiniteContextualOrder.quotientMap
      (Lax369799.FiniteAcceptance.Accepting L) n (ofSetSystem S)
    refine ⟨a, Quot.sound (equivalent E hE η F L hrec (representative a) S ?_)⟩
    exact @Quotient.exact _ st _ _ (rep a)

end Lax369799Proofs.ReachableFiniteness
