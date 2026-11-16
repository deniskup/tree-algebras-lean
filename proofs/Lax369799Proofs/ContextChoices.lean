import Lax369799.ContextChoices
import Lax369799Proofs.FiniteMarkUnion
import Lax369799Proofs.ExtremalUnaryTypes

namespace Lax369799Proofs.ContextChoices
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance
open FiniteNormalForms FiniteDecomposition FiniteSyntacticAlgebra
open ExpandedSyntacticAlgebra
open ExtremalContexts (Data)

open Lax369799.ContextChoices

private theorem body_edge {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (p : Set C.system.Vertex) (i : Fin (k + 1)) (v : BodyVertex C) (d : ℕ)
    (t : BodyVertex C ⊕ Fin 1) :
    (ordinaryPiece (restrict C p) i).edge v d t ↔ (ordinaryPiece C i).edge v d t := by
  cases t with
  | inl w => exact and_iff_left (fun h => False.elim (v.property h))
  | inr j => exact and_iff_left (fun h => False.elim (v.property h))

private theorem piece_union {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (C : Context (Carrier (Accepting L)) k 0)
    (p q : Set C.system.Vertex) (i : Fin (k + 1)) :
    pieceValue E.algebra (restrict C (p ∪ q)) i =
      sumValue E.algebra (pieceValue E.algebra (restrict C p) i)
        (pieceValue E.algebra (restrict C q) i) := by
  apply FiniteMarkUnion.evaluation_union L E
    (ordinaryPiece (restrict C p) i) (ordinaryPiece (restrict C q) i)
    (ordinaryPiece (restrict C (p ∪ q)) i)
  · intro v
    exact ⟨rfl, rfl⟩
  · intro v
    change ((i = 0 ∧ _) ∨ ∃ d : Fin k, i = d.succ ∧
      (C.system.graph.edge (holeVertex C) d.val (.inl v.val) ∧
        (holeVertex C = holeVertex C → v.val ∈ p ∪ q))) ↔ _
    simp only [Set.mem_union, forall_const, FiniteNormalForms.ordinaryPiece,
      FiniteDecomposition.piece, restrict, holeVertex]
    constructor
    · rintro (h | ⟨d, hi, he, hp | hq⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨d, hi, he, hp⟩)
      · exact Or.inr (Or.inr ⟨d, hi, he, hq⟩)
    · rintro ((h | ⟨d, hi, he, hp⟩) | (h | ⟨d, hi, he, hq⟩))
      · exact Or.inl h
      · exact Or.inr ⟨d, hi, he, Or.inl hp⟩
      · exact Or.inl h
      · exact Or.inr ⟨d, hi, he, Or.inr hq⟩
  · intro v
    exact ⟨Or.inl, fun h => h.elim id id⟩
  · intro v d t
    exact ⟨(body_edge C p i v d t).trans (body_edge C (p ∪ q) i v d t).symm,
      (body_edge C q i v d t).trans (body_edge C (p ∪ q) i v d t).symm⟩

private theorem data_union {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (C : Context (Carrier (Accepting L)) k 0)
    (p q : Set C.system.Vertex) :
    (⟨plantedBoundary (restrict C (p ∪ q)), pieceValue E.algebra (restrict C (p ∪ q))⟩ :
      Data (Carrier (Accepting L)) k) = SplitExtremal.meetData E.algebra
        ⟨plantedBoundary (restrict C p), pieceValue E.algebra (restrict C p)⟩
        ⟨plantedBoundary (restrict C q), pieceValue E.algebra (restrict C q)⟩ := by
  apply Prod.ext
  · change plantedBoundary (restrict C (p ∪ q)) =
      ⟨(plantedBoundary (restrict C p)).root ∨ (plantedBoundary (restrict C q)).root,
        (plantedBoundary (restrict C p)).loops ∪ (plantedBoundary (restrict C q)).loops⟩
    unfold plantedBoundary boundary restrict holeVertex
    congr 1
    · apply propext; tauto
    · ext d
      change (_ ∧ (_ → _ ∨ _)) ↔ (_ ∧ (_ → _)) ∨ (_ ∧ (_ → _))
      simp only [true_implies]
      tauto
  · funext i
    exact piece_union L E C p q i

/--
---
conclusion: Lax369799.ContextChoices.accepting_union
---
Normal decomposition turns target union into meet of boundary and piece
data. The principal extremal acceptance test preserves that meet.
-/
theorem accepting_union {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : ExtremalUnaryTypes.Selected L E b)
    (C : Context (Carrier (Accepting L)) 1 0) (p q : Set C.system.Vertex) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (plug (restrict C (p ∪ q)) (atomic b))) ↔
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug (restrict C p) (atomic b))) ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug (restrict C q) (atomic b))) := by
  have hc := fun n (S T : FiniteSystem (Carrier (Accepting L)) n) f hf =>
    FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates (S := S) (T := T) f hf
  have hn (D : Context (Carrier (Accepting L)) 1 0) :
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug D (atomic b))) ↔
        FiniteExtremal.Accepts (Accepting L) E.algebra b
          ⟨plantedBoundary D, pieceValue E.algebra D⟩ := by
    unfold FiniteExtremal.Accepts FiniteExtremal.value
    rw [FiniteNormalForms.algebraic_decomposition E.algebra hc]
    exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).symm
  rw [hn, hn, hn, data_union L E C p q]
  obtain ⟨a, x, hx, rfl⟩ := hb
  exact SplitExtremal.accepting_meetData L E.algebra E.evaluates (by omega) x _ _ a hx

/--
---
conclusion: Lax369799.ContextChoices.accepting_finite
---
Iterate binary splitting over a nonempty finite set of target vertices.
-/
theorem accepting_finite {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : ExtremalUnaryTypes.Selected L E b)
    (C : Context (Carrier (Accepting L)) 1 0) (s : Finset C.system.Vertex) (hs : s.Nonempty) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (plug (restrict C (↑s)) (atomic b))) ↔
      ∀ v ∈ s, AcceptingClass (Accepting L)
        (E.algebra.eval 0 (plug (restrict C {v}) (atomic b))) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert v s hv ih =>
    by_cases hne : s.Nonempty
    · have he : (↑(insert v s) : Set C.system.Vertex) = {v} ∪ (↑s : Set C.system.Vertex) := by
        ext w; simp
      rw [he, accepting_union L E b hb C, ih hne]
      simp
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      simp

private theorem restrict_univ {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    restrict C Set.univ = C := by
  cases C with
  | mk S h =>
    dsimp only [restrict]
    congr 1
    cases S
    congr 1
    congr 1
    funext v d t
    cases t with
    | inl w =>
      apply propext
      exact ⟨And.left, fun he => ⟨he, fun _ => True.intro⟩⟩
    | inr j => exact Fin.elim0 j

/--
---
conclusion: Lax369799.ContextChoices.accepting_all_choices
---
The context contains its hole, so its vertex set is nonempty. Apply
finite splitting to all targets.
-/
theorem accepting_all_choices {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : ExtremalUnaryTypes.Selected L E b)
    (C : Context (Carrier (Accepting L)) 1 0) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic b))) ↔
      ∀ v : C.system.Vertex, AcceptingClass (Accepting L)
        (E.algebra.eval 0 (plug (restrict C {v}) (atomic b))) := by
  classical
  have hs : (Finset.univ : Finset C.system.Vertex).Nonempty :=
    ⟨holeVertex C, Finset.mem_univ _⟩
  have h := accepting_finite L E b hb C Finset.univ hs
  simpa only [Finset.coe_univ, restrict_univ, Finset.mem_univ, forall_true_left] using h

end Lax369799Proofs.ContextChoices
