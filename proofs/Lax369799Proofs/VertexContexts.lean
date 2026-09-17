import Lax369799.VertexContexts

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

end Lax369799Proofs.VertexContexts
