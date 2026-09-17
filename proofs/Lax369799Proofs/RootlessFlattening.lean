import Lax369799.RootlessFlattening
import Lax369799Proofs.FiniteOuterMorphisms
import Lax369799Proofs.FiniteAcceptance
import Lax369799Proofs.Flattening

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.RootlessFlattening
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.PresentationCovers
open Lax369799.RootlessFlattening
open Lax369799Proofs.Pullbacks

noncomputable def rawCover {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (Lax369799.FinitePresentations.FiniteSystem A) n V)
    (h : ∀ v, (Lax369799.FinitePresentations.Inner P v).graph.root = ∅) :
    Cover (Flattening.graph (trim (trimLabels P)))
      (Lax369799.FinitePresentations.flattenPresentation P) := by
  classical
  let Q : Presentation (Lax369799.FinitePresentations.FiniteSystem A) n V := {
    P with label := fun v => ⟨(P.label v).1,
      Lax369799.FinitePresentations.ofSetSystem (trim (Lax369799.FinitePresentations.Inner P v).graph)⟩ }
  have hQ (v : V) : (Lax369799.FinitePresentations.Inner Q v).graph.root = ∅ := by
    ext u
    change (trim (Lax369799.FinitePresentations.Inner P v).graph).Vertex at u
    change (Lax369799.FinitePresentations.Inner P v).graph.root
      (vertex (Lax369799.FinitePresentations.Inner P v).graph u) ↔ False
    rw [h]
    rfl
  let outer := FiniteOuterMorphisms.flattenCoverRootlessRaw (FiniteAcceptance.trimProjection Q) hQ
  let inner := FiniteCovers.substituteCover P
    (fun v => (trim (Lax369799.FinitePresentations.Inner P v).graph).graph)
    (fun v => (Lax369799.FinitePresentations.Inner P v).graph)
    (fun v => FiniteAcceptance.trimProjection (Lax369799.FinitePresentations.Inner P v).graph)
  exact FiniteCovers.compose outer inner

/--
---
conclusion: Lax369799.RootlessFlattening.flatten_cover
---
Restrict the inner presentations using their canonical covers. Restrict
the outer pattern using the root-free outer-cover lemma, then compose
these covers and restrict the flattened presentations to reachable vertices.
-/
theorem flatten_cover {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (Lax369799.FinitePresentations.FiniteSystem A) n V)
    (h : ∀ v, (Lax369799.FinitePresentations.Inner P v).graph.root = ∅) :
    UnfoldsTo (trim (Lax369799.FinitePresentations.flattenPresentation P))
      (Lax369799.Flattening.flatten (trim (trimLabels P))) := by
  let f := rawCover P h
  let g : Map _ _ := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  exact ⟨trimMap g, trimMap_surjective g f.initial_lift f.root_lift f.edge_lift⟩

end Lax369799Proofs.RootlessFlattening
