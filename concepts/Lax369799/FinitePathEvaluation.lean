import Lax369799.FiniteBranchWords

/-!
---
title: Evaluation of finite path graphs
type: theorem
---
The graph with one vertex for each unary letter and a final nullary
vertex evaluates to the iterated unary action on the nullary value.
-/
namespace Lax369799.FinitePathEvaluation
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra FiniteBranchWords

def path {A : RankedSet} {k : ℕ} (w : Fin k → A 1) (a : A 0) : FiniteSystem A 0 where
  size := k + 1
  graph := {
    label := Fin.lastCases ⟨0, a⟩ (fun i => ⟨1, w i⟩)
    initial := {0}
    root := ∅
    edge := fun v d t => ∃ i : Fin k, v = i.castSucc ∧ d = 0 ∧ t = .inl i.succ
    direction_valid := by rintro v d t ⟨i, rfl, rfl, rfl⟩; simp }


axiom evaluation {A : RankedSet} (E : Algebra A) {k : ℕ}
    (w : Fin k → A 1) (a : A 0) :
    E.eval 0 (path w a) = value E (List.ofFn w) a

end Lax369799.FinitePathEvaluation
