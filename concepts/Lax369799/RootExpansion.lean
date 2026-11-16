import Lax369799.FinitePresentations
import Lax369799.PresentationCovers

/-!
---
title: Root entries in substituted presentations
type: theorem
---
To observe the roots of a substitution, give every outer vertex a separate
starting copy whose inner roots become initial. Subsequent outer transitions
go to ordinary copies, where inner initial vertices remain initial. Outer
roots also start at their ordinary copies. All root marks in the expanded
presentation are removed. This preserves root observations even at vertices
that were unreachable in the original outer presentation.
-/
namespace Lax369799.RootExpansion
open RankedSystems FinitePresentations

def startAtRoots {A : RankedSet} {n : ℕ} {V : Type} (G : Presentation A n V) :
    Presentation A n V := { G with initial := G.root, root := ∅ }

def component {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) (start : Bool) : FiniteSystem A n where
  size := S.size
  graph := { S.graph with initial := if start then S.graph.root else S.graph.initial, root := ∅ }

def pattern {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FiniteSystem A) n V) : Presentation (FiniteSystem A) n (Bool × V) where
  label := fun v => ⟨(P.label v.2).1, component (Inner P v.2) v.1⟩
  initial := fun v => if v.1 then True else P.root v.2
  root := ∅
  edge := fun v d t => ∃ s, P.edge v.2 d s ∧ t = Sum.map (fun w => (false, w)) id s
  direction_valid := by rintro v d t ⟨s, hs, _⟩; exact P.direction_valid _ _ _ hs

axiom expansion_cover {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FiniteSystem A) n V) :
    Nonempty (PresentationCovers.Cover (flattenPresentation (pattern P))
      (startAtRoots (flattenPresentation P)))

axiom expansion_folding {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FiniteSystem A) n V) :
    ∃ f : PresentationCovers.Cover (flattenPresentation (pattern P))
      (startAtRoots (flattenPresentation P)), Function.Surjective f.toFun

end Lax369799.RootExpansion
