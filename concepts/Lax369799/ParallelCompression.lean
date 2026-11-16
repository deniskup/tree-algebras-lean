import Lax369799.PortReindexing
import Lax369799.CloneTransitions
import Lax369799.DeterministicElements

/-!
---
title: Evaluation after compressing parallel tuples
type: theorem
---
Taking the meet of each block in a parallel tuple has the same evaluation
as renaming all ports in that block to one output. This is the local
substitution identity used to compress a duplicated run in Lemma 108.
-/
namespace Lax369799.ParallelCompression
open RankedSystems (RankedSet)
open FinitePresentations SetSystemAlgebras CloneTransitions PortReindexing
variable {A : RankedSet} {n k : ℕ} (b : Fin (n * k) → A 1)

axiom evaluation (E : SetAlgebra A) :
    E.eval n (ofSetSystem (DeterministicElements.parallel (compress E b))) =
      E.eval n (rename (ofSetSystem (DeterministicElements.parallel b)) (fun i => i.divNat))

end Lax369799.ParallelCompression
