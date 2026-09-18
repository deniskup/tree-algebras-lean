import Lax369799.InitialAlgebra
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
---
title: Finite path-summary algebras
type: theorem
---
An element records, for each entry state, the possible final states and
variable exits with their states. Evaluation follows a finite path through
the system, composing local summaries. This gives a rankwise-finite algebra
when the state set is finite, suitable for recognizing local predicates
along paths from the initial vertex.
-/
namespace Lax369799.PathAlgebra
open RankedSystems Algebras InitialAlgebra

abbrev Result (Q : Type) (n : ℕ) := Q ⊕ (Fin n × Q)
abbrev Carrier (Q : Type) : RankedSet := fun n => Q → Set (Result Q n)

def Halt {Q : Type} (a : Symbol (Carrier Q)) (q r : Q) : Prop :=
  Sum.inl r ∈ a.2 q

def Exit {Q : Type} (a : Symbol (Carrier Q)) (d : ℕ) (q r : Q) : Prop :=
  ∃ i : Fin a.1, i.val = d ∧ Sum.inr (i, r) ∈ a.2 q

inductive Run {Q V : Type} {n : ℕ} (G : Presentation (Carrier Q) n V) :
    V → Q → Result Q n → Prop
  | halt {v q r} (h : Halt (G.label v) q r) : Run G v q (.inl r)
  | exit {v q r i} (d : ℕ)
      (h : Exit (G.label v) d q r) (he : G.edge v d (.inr i)) :
      Run G v q (.inr (i, r))
  | step {v w q r out} (d : ℕ)
      (h : Exit (G.label v) d q r) (he : G.edge v d (.inl w))
      (tail : Run G w r out) : Run G v q out

noncomputable def evaluate {Q : Type} (n : ℕ) (S : System (Carrier Q) n) : Carrier Q n :=
  fun q out => Run S.val.graph (initial S) q out

axiom algebra (Q : Type) : ∃ E : Algebra (Carrier Q), E.eval = evaluate

axiom finite_carrier (Q : Type) [Finite Q] : RankwiseFinite (Carrier Q)

end Lax369799.PathAlgebra
