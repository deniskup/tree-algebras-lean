import Lax369799.FinitePresentations
import Lax369799.Renaming

/-!
---
title: Substitution after restricting inner output ports
type: theorem
---
Renaming the outputs of each inner system and restricting the matching
outer directions produce isomorphic flattened presentations. This holds
for arbitrary port maps and retains roots and output variables. The
restricted outer presentation has a deterministic reachable restriction
when the original outer presentation is deterministic.
-/

namespace Lax369799.SupportPorts
open RankedSystems

def expanded {A B : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation A n V) (m : V → ℕ)
    (σ : ∀ v, Fin (m v) → Fin (G.label v).1)
    (S : ∀ v, System B (m v)) : Presentation (System B) n V where
  label := fun v => ⟨(G.label v).1, Renaming.renameSystem (σ v) (S v)⟩
  initial := G.initial
  root := G.root
  edge := G.edge
  direction_valid := G.direction_valid

def restricted {A B : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation A n V) (m : V → ℕ)
    (σ : ∀ v, Fin (m v) → Fin (G.label v).1)
    (S : ∀ v, System B (m v)) : Presentation (System B) n V where
  label := fun v => ⟨m v, S v⟩
  initial := G.initial
  root := G.root
  edge := fun v d t => ∃ i : Fin (m v), d = i.val ∧ G.edge v (σ v i).val t
  direction_valid := by rintro v d t ⟨i, rfl, _⟩; exact i.isLt

def flattened {B : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation (System B) n V) :
    Presentation B n ((v : V) × (G.label v).2.val.Vertex) :=
  FinitePresentations.flattenPresentation {
    G with label := fun v => ⟨(G.label v).1,
      FinitePresentations.ofSetSystem (G.label v).2.val⟩ }

axiom flatten_iso {A B : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation A n V) (m : V → ℕ)
    (σ : ∀ v, Fin (m v) → Fin (G.label v).1) (S : ∀ v, System B (m v)) :
    Nonempty (FinitePresentations.PresentationIso
      (flattened (expanded G m σ S)) (flattened (restricted G m σ S)))

axiom restricted_system {A B : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (m : V → ℕ)
    (σ : ∀ v, Fin (m v) → Fin (G.label v).1) (S : ∀ v, System B (m v))
    (r : V) (hi : G.initial = {r}) (hr : G.root = ∅)
    (ht : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t) :
    ∃ T : System (System B) n, T.val = trim (restricted G m σ S)

end Lax369799.SupportPorts

