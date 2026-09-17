import Lax369799.FiniteProfiles

/-!
---
title: Initial and root observations of set-systems
type: theorem
---
Initial resolutions do not depend on root marks. Removing these marks
and restricting to initial reachability therefore preserves the complete
initial profile. Root observations can be treated separately by making
roots initial, as in uprooting.
-/
namespace Lax369799.RootObservations
open RankedSystems Morphisms Resolutions

noncomputable def initialPart {A : RankedSet} {n : ℕ} (S : SetSystem A n) : SetSystem A n :=
  trim { S.graph with root := ∅ }

axiom resolution_initial_part {A : RankedSet} {m n : ℕ} (S : SetSystem A n)
    (T : System A m) (σ : Fin m → Fin n) :
    IsResolution (initialPart S) T σ ↔ IsResolution S T σ

axiom initial_profile {A B : RankedSet} (ρ : ∀ n, System A n → B n) {n : ℕ}
    (S : SetSystem A n) : Profile ρ (initialPart S) = Profile ρ S

axiom rootless_outer_cover {A : RankedSet} {n : ℕ}
    (S T : FinitePresentations.FiniteSystem (FinitePresentations.FiniteSystem A) n)
    (f : PresentationCovers.Cover S.graph T.graph)
    (h : ∀ w, (FinitePresentations.Inner T.graph w).graph.root = ∅) :
    Nonempty (PresentationCovers.Cover (FinitePresentations.flatten S).graph
      (FinitePresentations.flatten T).graph)

end Lax369799.RootObservations
