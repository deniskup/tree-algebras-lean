import Lax369799.ResolutionFamilies
import Lax369799.BoundedProfileRefinement

/-!
---
title: Normal forms retaining split-variable resolutions
type: theorem
---
A finite disjoint family of initial and planted root resolutions can
preserve every bounded profile of a presentation. Each component is a
whole deterministic system; its internal branching is retained.
-/
namespace Lax369799.FiniteResolutionNormalForms
open RankedSystems Morphisms FinitePresentations FiniteProfiles

structure Component {A : RankedSet} {n : ℕ} (S : SetSystem A n) where
  system : System A n
  rooted : Bool
  resolves : DirectResolution (if rooted then RankedSystems.uproot S else S) system

def familyGraph {A : RankedSet} {n : ℕ} {I : Type} {S : SetSystem A n}
    (c : I → Component S) : Presentation A n ((i : I) × (c i).system.val.Vertex) where
  label := fun v => ((c v.1).system.val.graph.label v.2)
  initial := fun v => (c v.1).rooted = false ∧ v.2 ∈ (c v.1).system.val.graph.initial
  root := fun v => (c v.1).rooted = true ∧ v.2 ∈ (c v.1).system.val.graph.initial
  edge := fun v d t => ∃ s, (c v.1).system.val.graph.edge v.2 d s ∧
    t = Sum.map (Sigma.mk v.1) id s
  direction_valid := by rintro v d t ⟨s, hs, _⟩; exact (c v.1).system.val.graph.direction_valid v.2 d s hs

noncomputable def family {A : RankedSet} {n : ℕ} {I : Type} [Fintype I]
    {S : SetSystem A n} (c : I → Component S) : FiniteSystem A n := enumerate (familyGraph c)

axiom bounded_normal_form {A B : RankedSet} (hB : RankwiseFinite B) (bound : ℕ)
    (ρ : ∀ n, System A n → B n) {n : ℕ} (S : FiniteSystem A n) :
    ∃ (k : ℕ) (c : Fin k → Component (trim S.graph)),
      BoundedProfileEquivalent bound ρ S (family c)

axiom contextual_normal_form {A B : RankedSet} (E : Algebras.Algebra B)
    (hE : Algebras.UnfoldInvariant E) (hB : RankwiseFinite B)
    (η : RankedMap A B) (F : Set (B 0)) (L : Algebras.Language A)
    (hL : Algebras.Recognizes E η F L) {n : ℕ} (S : FiniteSystem A n) :
    ∃ (k : ℕ) (c : Fin k → Component (trim S.graph)),
      FiniteContextualOrder.quotientMap (FiniteAcceptance.Accepting L) n S =
        FiniteContextualOrder.quotientMap (FiniteAcceptance.Accepting L) n (family c)

end Lax369799.FiniteResolutionNormalForms
