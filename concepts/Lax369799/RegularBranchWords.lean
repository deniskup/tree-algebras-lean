import Lax369799.RunBranchObservations
import Lax369799.UnfoldBranches

/-!
---
title: Testing infinite runs on finite branch graphs
type: theorem
---
A finite branch graph unfolds to an ultimately periodic branch, and every
ultimately periodic branch has such a presentation. Thus a parity condition
holds on all infinite branches exactly when it holds on the unfoldings of
all finite branch graphs.
-/
namespace Lax369799.RegularBranchWords
open RankedSystems (RankedSet System)
open UnfoldAutomata RunBranchObservations

def position {A : RankedSet} {S : System A 0} (b : RegularBranch S) : ℕ → Fin b.size
  | 0 => b.start
  | n + 1 => b.next (position b n)

def trace {A : RankedSet} {S : System A 0} (b : RegularBranch S) : InfiniteBranch S where
  vertex := fun n => b.vertex (position b n)
  direction := fun n => b.direction (position b n)
  starts := b.starts
  follows := fun n => b.follows (position b n)

axiom periodic {A : RankedSet} {S : System A 0} (b : RegularBranch S) :
    UnfoldBranches.Periodic (trace b)

axiom represents {A : RankedSet} {S : System A 0} (b : InfiniteBranch S)
    (hb : UnfoldBranches.Periodic b) :
    ∃ c : RegularBranch S, ∀ n,
      (⟨(trace c).vertex n, (trace c).direction n⟩ : (v : S.val.Vertex) × Fin (Rank S v)) =
        ⟨b.vertex n, b.direction n⟩

axiom regular_test {A : RankedSet} (M : UnfoldAutomaton A) (S : System A 0) (r : Run M S) :
    (∀ b : RegularBranch S, M.condition.AcceptsInfinite
      (fun n => r.edgeType ((trace b).vertex n) ((trace b).direction n))) ↔
    (∀ b : InfiniteBranch S, M.condition.AcceptsInfinite
      (fun n => r.edgeType (b.vertex n) (b.direction n)))

end Lax369799.RegularBranchWords
