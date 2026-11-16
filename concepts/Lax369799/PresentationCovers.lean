import Lax369799.Morphisms

/-!
---
title: Locally surjective maps of finite presentations
type: definition
---
A cover of presentations preserves labels, initial vertices, roots, and
edges, and is surjective on initial vertices, roots, and each successor
set. Presentations may contain unreachable vertices. Restricting the
source of a cover to its reachable part still covers a reachable target.
This permits finite constructions to be checked before enumerating and
removing unreachable vertices.
-/

namespace Lax369799.PresentationCovers
open RankedSystems Morphisms

structure Cover {A : RankedSet} {n : ℕ} {V W : Type}
    (S : Presentation A n V) (T : Presentation A n W) where
  toFun : V → W
  label : ∀ v, T.label (toFun v) = S.label v
  initial : ∀ v, v ∈ S.initial → toFun v ∈ T.initial
  root : ∀ v, v ∈ S.root → toFun v ∈ T.root
  edge : ∀ v d t, S.edge v d t → T.edge (toFun v) d (Sum.map toFun id t)
  initial_lift : ∀ w, w ∈ T.initial → ∃ v, v ∈ S.initial ∧ toFun v = w
  root_lift : ∀ w, w ∈ T.root → ∃ v, v ∈ S.root ∧ toFun v = w
  edge_lift : ∀ v d t, T.edge (toFun v) d t →
    ∃ s, S.edge v d s ∧ Sum.map toFun id s = t

axiom surjective_of_reachable {A : RankedSet} {n : ℕ} {V W : Type}
    {S : Presentation A n V} {T : Presentation A n W} (f : Cover S T)
    (hT : ∀ w, T.Reachable w) : Function.Surjective f.toFun

axiom trim_cover {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (S : Presentation A n V) (T : SetSystem A n) (f : Cover S T.graph) :
    UnfoldsTo T (trim S)

end Lax369799.PresentationCovers
