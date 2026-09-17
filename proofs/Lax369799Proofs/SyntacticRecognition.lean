import Lax369799.SyntacticAlgebraTheorems
import Lax369799Proofs.SumYields

namespace Lax369799Proofs.SyntacticRecognition
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.Algebras Lax369799.SetAlgebras Lax369799.SyntacticOrder

private def acceptedClass {A : RankedSet} (L : Language A) : Set (SyntacticCarrier L 0) :=
  fun q => Quot.lift (Accepting L) (fun _ _ h => propext
    ⟨Acceptance.syntactic_acceptance L h.1, Acceptance.syntactic_acceptance L h.2⟩) q

private theorem map_unfold {A : RankedSet} (L : Language A) {n : ℕ}
    (S T : SetSystem A n) (h : UnfoldEquivalent S T) :
    syntacticMap L n S = syntacticMap L n T := by
  apply Quot.sound
  have hc (C : SetContext A n 0) := Acceptance.accepting_unfold L _ _
    (ContextCongruence.unfold_context_congruence C S T h)
  exact ⟨fun C => (hc C).mp, fun C => (hc C).mpr⟩

private theorem map_sum {A : RankedSet} (L : Language A) (E : SyntacticAlgebra L)
    {n : ℕ} (S T : SetSystem A n) :
    syntacticMap L n (sum S T) = meet E.algebra (syntacticMap L n S) (syntacticMap L n T) := by
  obtain ⟨c, hc⟩ := SumEvaluation.binary_flatten_cover S T
  have he := map_unfold L (sum S T) (flatten (SumEvaluation.binary S T))
    ⟨_, ⟨c, hc⟩, ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩⟩
  rw [he, ← E.evaluates]
  exact SumEvaluation.eval_binary_labels E.algebra (syntacticMap L) S T

/--
---
conclusion: Lax369799.SyntacticAlgebraTheorems.syntactic_recognition
---
Acceptance descends through the syntactic equivalence. The quotient map
sends disjoint union to meet, while acceptance of a disjoint union is the
conjunction of acceptance of its summands. These facts give the filter
properties. On deterministic systems acceptance is language membership.
-/
theorem syntactic_recognition {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (E : SyntacticAlgebra L) :
    ∃ F : Set (SyntacticCarrier L 0),
      (∀ S, syntacticMap L 0 S ∈ F ↔ Accepting L S) ∧
      (∀ T : System A 0, syntacticMap L 0 T.val ∈ F ↔ T ∈ L) ∧
      (∀ a b, a ∈ F → Below E.algebra a b → b ∈ F) ∧
      (∀ a b, a ∈ F → b ∈ F → meet E.algebra a b ∈ F) := by
  refine ⟨acceptedClass L, fun _ => Iff.rfl,
    fun T => Acceptance.accepting_system L hL T, ?_, ?_⟩
  · intro a b
    induction a using Quot.inductionOn with
    | h S =>
      induction b using Quot.inductionOn with
      | h T =>
        intro hS hST
        have he : syntacticMap L 0 (sum S T) = syntacticMap L 0 S :=
          (map_sum L E S T).trans hST
        have ha : syntacticMap L 0 (sum S T) ∈ acceptedClass L := he.symm ▸ hS
        exact ((SumYields.accepting_sum L S T).mp ha).2
  · intro a b
    induction a using Quot.inductionOn with
    | h S =>
      induction b using Quot.inductionOn with
      | h T =>
        intro hS hT
        have ha : syntacticMap L 0 (sum S T) ∈ acceptedClass L :=
          (SumYields.accepting_sum L S T).mpr ⟨hS, hT⟩
        exact Eq.mp (congrArg (fun q => q ∈ acceptedClass L) (map_sum L E S T)) ha

end Lax369799Proofs.SyntacticRecognition
