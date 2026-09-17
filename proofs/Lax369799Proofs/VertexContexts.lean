import Lax369799.VertexContexts
import Lax369799Proofs.ContinuationCompression

namespace Lax369799Proofs.VertexContexts
open Lax369799.RankedSystems Lax369799.Flattening Lax369799.SystemEvaluation
open Lax369799.VertexContexts

/--
---
conclusion: Lax369799.VertexContexts.deterministic
---
Only the selected label changes, and its rank is preserved.
-/
theorem deterministic {A : RankedSet} {n : ℕ} (S : System A n) (v : S.val.Vertex) :
    (atVertex S v).system.Deterministic := S.property

/--
---
conclusion: Lax369799.VertexContexts.fill_vertex
---
At the selected vertex the original letter fills the hole; every other
vertex carries its unchanged ordinary letter.
-/
theorem fill_vertex {A : RankedSet} {n : ℕ} (S : System A n) (v : S.val.Vertex) :
    relabel (fillLetter (S.val.graph.label v).2) (atVertex S v).system = S.val := by
  classical
  have hl : (relabel (fillLetter (S.val.graph.label v).2) (atVertex S v).system).graph.label =
      S.val.graph.label := by
    funext w
    change S.val.Vertex at w
    by_cases h : w = v
    · subst w
      simp [relabel, atVertex, fillLetter]
    · simp [relabel, atVertex, fillLetter, h]
  cases S with
  | mk S hS =>
    cases S with
    | mk size G hr =>
      cases G
      dsimp only [atVertex, relabel] at hl ⊢
      congr 1
      congr 1

/--
---
conclusion: Lax369799.VertexContexts.smallification
---
Mark the selected outer vertex and apply context smallification to its
atomic label. Context evaluation and the unit law identify the original
system and the system with its locally renamed label value.
-/
theorem smallification {A : RankedSet} (E : Lax369799.Algebras.Algebra A)
    (hE : Lax369799.Algebras.UnfoldInvariant E) [Finite (A 1)]
    (S : System A 0) (v : S.val.Vertex) {n : ℕ}
    (σ : Fin (S.val.graph.label v).1 → Fin n) :
    ∃ (m' : ℕ) (τ : Fin (S.val.graph.label v).1 → Fin m')
      (sectionMap : Fin m' → Fin (S.val.graph.label v).1),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card (A 1) + 1) ∧
      ∃ T : System A 0,
        T.val = relabel (fillLetter (E.eval _
          (Lax369799.Renaming.renameSystem (sectionMap ∘ τ) (atomicSystem (S.val.graph.label v).2))))
          (atVertex S v).system ∧ E.eval 0 S = E.eval 0 T := by
  let C := atVertex S v
  have hC : C.system.Deterministic := deterministic S v
  let a := (S.val.graph.label v).2
  obtain ⟨m', τ, sectionMap, hs, hσ, hb, U, V, hU, hV, he⟩ :=
    ContinuationCompression.context_smallification E hE C hC (atomicSystem a) σ
  let R := Lax369799.Renaming.renameSystem (sectionMap ∘ τ) (atomicSystem a)
  obtain ⟨U', hU', eU⟩ := SystemEvaluation.context_evaluation E C hC (atomicSystem a)
  obtain ⟨V', hV', eV⟩ := SystemEvaluation.context_evaluation E C hC R
  have hu : U = U' := Subtype.ext (hU.trans hU'.symm)
  have hv : V = V' := Subtype.ext (hV.trans hV'.symm)
  have hfill : relabelSystem (fillLetter a) ⟨C.system, hC⟩ = S :=
    Subtype.ext (fill_vertex S v)
  rw [E.unit, hfill] at eU
  let T := relabelSystem (fillLetter (E.eval _ R)) ⟨C.system, hC⟩
  refine ⟨m', τ, sectionMap, hs, hσ, hb, T, rfl, ?_⟩
  rw [hu, hv] at he
  exact eU.symm.trans (he.trans eV)

end Lax369799Proofs.VertexContexts
