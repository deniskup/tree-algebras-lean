import Lax369799.ContextRelabelling
import Lax369799.ContextSmallification

/-!
---
title: Contexts obtained by marking a vertex
type: theorem
---
Replacing the label of a selected vertex by the hole preserves its rank,
marks, edges, and reachability. Filling the hole by the original letter
recovers the system. This permits local changes to an outer deterministic
system before flattening its labels.
-/
namespace Lax369799.VertexContexts
open RankedSystems Flattening SystemEvaluation

noncomputable def atVertex {A : RankedSet} {n : ℕ} (S : System A n) (v : S.val.Vertex) :
    SetContext A (S.val.graph.label v).1 n := by
  classical
  let G : Presentation (WithHole A (S.val.graph.label v).1) n S.val.Vertex := {
    label := fun w => ⟨(S.val.graph.label w).1,
      if h : w = v then Sum.inr ⟨by rw [h]⟩ else Sum.inl (S.val.graph.label w).2⟩
    initial := S.val.graph.initial
    root := S.val.graph.root
    edge := S.val.graph.edge
    direction_valid := S.val.graph.direction_valid }
  refine ⟨⟨S.val.size, G, S.val.reachable⟩, v, ?_, ?_⟩
  · exact ⟨⟨rfl⟩, by simp [G]⟩
  · intro w hw
    by_contra h
    obtain ⟨p, hp⟩ := hw
    simp only [G, dif_neg h] at hp
    cases hp

axiom deterministic {A : RankedSet} {n : ℕ} (S : System A n) (v : S.val.Vertex) :
    (atVertex S v).system.Deterministic

axiom fill_vertex {A : RankedSet} {n : ℕ} (S : System A n) (v : S.val.Vertex) :
    relabel (fillLetter (S.val.graph.label v).2) (atVertex S v).system = S.val

axiom smallification {A : RankedSet} (E : Algebras.Algebra A) (hE : Algebras.UnfoldInvariant E)
    [Finite (A 1)] (S : System A 0) (v : S.val.Vertex) {n : ℕ}
    (σ : Fin (S.val.graph.label v).1 → Fin n) :
    ∃ (m' : ℕ) (τ : Fin (S.val.graph.label v).1 → Fin m')
      (sectionMap : Fin m' → Fin (S.val.graph.label v).1),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card (A 1) + 1) ∧
      ∃ T : System A 0,
        T.val = relabel (fillLetter (E.eval _
          (Renaming.renameSystem (sectionMap ∘ τ) (atomicSystem (S.val.graph.label v).2))))
          (atVertex S v).system ∧ E.eval 0 S = E.eval 0 T

end Lax369799.VertexContexts
