import Lax369799.PeriodicPaths

/-!
---
title: Periodic branch test for unfold-automata
type: theorem
---
On a finite system, checking the parity condition on ultimately periodic
branches suffices for all infinite branches. Periodicity records both the
vertex and the chosen outgoing direction.
-/
namespace Lax369799.UnfoldBranches
open RankedSystems UnfoldAutomata

def Periodic {A : RankedSet} {S : System A 0} (b : InfiniteBranch S) : Prop :=
  PeriodicPaths.UltimatelyPeriodic
    (fun n => (⟨b.vertex n, b.direction n⟩ : (v : S.val.Vertex) × Fin (Rank S v)))

axiom periodic_test {A : RankedSet} (M : UnfoldAutomaton A) (S : System A 0) (r : Run M S) :
    (∀ b : InfiniteBranch S, Periodic b → M.condition.AcceptsInfinite
      (fun n => r.edgeType (b.vertex n) (b.direction n))) ↔
    (∀ b : InfiniteBranch S, M.condition.AcceptsInfinite
      (fun n => r.edgeType (b.vertex n) (b.direction n)))

end Lax369799.UnfoldBranches
