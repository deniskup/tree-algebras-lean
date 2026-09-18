import Lax369799.Morphisms
import Mathlib.Data.Fintype.Prod

/-!
---
title: Variable exits of unary systems
type: theorem
---
A deterministic system whose labels have rank at most one follows a single
path from its initial vertex. Consequently all its variable exits use the
same variable. This is the path property used in the characterization of
deterministic algebra elements in Section 5.1.
-/
namespace Lax369799.UnarySystems
open RankedSystems Morphisms

axiom unique_exit {A : RankedSet} {n : ℕ} (S : System A n)
    (hS : ∀ v, (S.val.graph.label v).1 ≤ 1)
    {v w : S.val.Vertex} {d e : ℕ} {i j : Fin n}
    (hi : S.val.graph.edge v d (.inr i)) (hj : S.val.graph.edge w e (.inr j)) : i = j

/-- One copy for each variable, retaining only exits to that variable. -/
def variablePieces {A : RankedSet} {n : ℕ} {V : Type} (G : Presentation A n V) :
    Presentation A n (Fin n × V) where
  label := fun v => G.label v.2
  initial := fun v => G.initial v.2
  root := fun v => G.root v.2
  edge := fun v d t => ∃ s, G.edge v.2 d s ∧
    (∀ i, s = .inr i → i = v.1) ∧ t = Sum.map (fun w => (v.1, w)) id s
  direction_valid := by rintro v d t ⟨s, hs, _, _⟩; exact G.direction_valid _ _ _ hs

axiom variable_decomposition {A : RankedSet} {n : ℕ} (hn : 0 < n)
    {V : Type} [Fintype V] (G : Presentation A n V)
    (hG : ∀ v, (G.label v).1 ≤ 1) :
    YieldEquivalent (trim G) (trim (variablePieces G))

end Lax369799.UnarySystems
