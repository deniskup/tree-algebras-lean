import Lax369799.Renaming

/-!
---
title: Compression of the variables of flatten-resolutions
type: theorem
---
Rename the variables of each inner system and retain one outer edge for
each new variable. If the selected representatives preserve the original
variable maps, the resulting outer system is still a flatten-resolution.
Uniform bounds on the representative fibres pass to the new resolution.
-/
namespace Lax369799.ResolutionCompression
open RankedSystems Resolutions Renaming

def compressedPresentation {A : RankedSet} {n : ℕ} (T : System (System A) n)
    (arity : T.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.graph.label v).1 → Fin (arity v))
    (sectionMap : ∀ v, Fin (arity v) → Fin (T.val.graph.label v).1) :
    Presentation (System A) n T.val.Vertex where
  label := fun v => ⟨arity v, renameSystem (τ v) (T.val.graph.label v).2⟩
  initial := T.val.graph.initial
  root := T.val.graph.root
  edge := fun v d t => ∃ i : Fin (arity v), d = i.val ∧ T.val.graph.edge v (sectionMap v i).val t
  direction_valid := by rintro v d t ⟨i, rfl, _⟩; exact i.isLt

def backPresentation {A : RankedSet} {n : ℕ} (T : System (System A) n)
    (arity : T.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.graph.label v).1 → Fin (arity v))
    (sectionMap : ∀ v, Fin (arity v) → Fin (T.val.graph.label v).1) :
    Presentation (System A) n T.val.Vertex := {
  T.val.graph with label := fun v => ⟨(T.val.graph.label v).1,
    renameSystem (sectionMap v ∘ τ v) (T.val.graph.label v).2⟩ }


axiom compress_flatten_resolution {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (T : System (System A) n) (r : FlattenResolution S T)
    (arity : T.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.graph.label v).1 → Fin (arity v))
    (sectionMap : ∀ v, Fin (arity v) → Fin (T.val.graph.label v).1)
    (hσ : ∀ v i, r.variableMap v (sectionMap v (τ v i)) = r.variableMap v i)
    (bound : ℕ) (hb : ∀ v j, Nat.card {i // r.variableMap v (sectionMap v i) = j} ≤ bound) :
    ∃ U : System (System A) n,
      U.val = trim (compressedPresentation T arity τ sectionMap) ∧
      ∃ r' : FlattenResolution S U,
        ∀ v j, Nat.card {i // r'.variableMap v i = j} ≤ bound

axiom evaluation {A : RankedSet} (E : Algebras.Algebra A) (hE : Algebras.UnfoldInvariant E) {n : ℕ}
    (T : System (System A) n) (arity : T.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.graph.label v).1 → Fin (arity v))
    (sectionMap : ∀ v, Fin (arity v) → Fin (T.val.graph.label v).1) :
    ∃ U V : System (System A) n,
      U.val = trim (backPresentation T arity τ sectionMap) ∧
      V.val = trim (compressedPresentation T arity τ sectionMap) ∧
      E.eval n (relabelSystem E.eval U) = E.eval n (relabelSystem E.eval V)

end Lax369799.ResolutionCompression
