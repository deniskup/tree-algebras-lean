import Lax369799.Algebras

/-!
---
title: The initial-label algebra
type: theorem
---
A constant ranked set carries an algebra that reads only the label of the
initial vertex. Finite instances recognize initial-vertex predicates.
-/
namespace Lax369799.InitialAlgebra
open RankedSystems Algebras

noncomputable def initial {A : RankedSet} {n : ℕ} (S : System A n) : S.val.Vertex :=
  Classical.choose S.property.1

noncomputable def evaluate {C : Type} (n : ℕ) (S : System (fun _ => C) n) : C :=
  (S.val.graph.label (initial S)).2

axiom algebra (C : Type) : ∃ E : Algebra (fun _ => C), E.eval = evaluate

axiom recognizes {A : RankedSet} (p : ∀ n, A n → Prop) :
  Recognizable {S : System A 0 | p _ (S.val.graph.label (initial S)).2}

end Lax369799.InitialAlgebra
