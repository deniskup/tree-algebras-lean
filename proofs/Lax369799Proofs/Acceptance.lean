import Lax369799.AcceptanceTheorems
import Lax369799Proofs.Yields
import Lax369799Proofs.AtomicFlattening
import Lax369799Proofs.Evaluation

namespace Lax369799Proofs.Acceptance
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.Algebras Lax369799.SyntacticOrder
open Lax369799Proofs.MorphismTheorems

private theorem system_ne_plant {A : RankedSet} {n : ℕ} (S T : System A n) :
    S.val ≠ plant T.val := by
  intro h
  obtain ⟨i, hi⟩ := S.property.1
  have he : S.val.graph.initial = ∅ := by rw [h]; rfl
  have hh : i ∈ S.val.graph.initial := by rw [hi]; rfl
  rw [he] at hh
  exact hh

/--
---
conclusion: Lax369799.AcceptanceTheorems.accepting_system
---
A system is one of its own yields. Every initial yield of a system is
unfold-equivalent to it, while no root yield exists because it has no
roots. Unfold invariance of the language gives the equivalence.
-/
theorem accepting_system {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (S : System A 0) :
    Accepting L S.val ↔ S ∈ L := by
  constructor
  · intro h
    obtain ⟨U, hU, he⟩ := h S.val (Or.inl ⟨S,
      ⟨S, ⟨identity S.val⟩, ⟨identity S.val, identity_surjective S.val⟩⟩, rfl⟩)
    rcases he with he | he
    · have he : S = U := Subtype.ext he
      exact he.symm ▸ hU
    · exact False.elim (system_ne_plant S U he)
  · intro hS T hT
    rcases hT with ⟨U, ⟨D, ⟨d⟩, hu⟩, rfl⟩ | ⟨U, ⟨D, ⟨d⟩, _⟩, rfl⟩
    · have he : UnfoldEquivalent S.val U.val :=
        ⟨D.val, ⟨d, system_morphism_locally_surjective D S d⟩, hu⟩
      exact ⟨U, (hL S U he).mp hS, Or.inl rfl⟩
    · obtain ⟨i, hi⟩ := D.property.1
      have hh := d.initial i (by rw [hi]; rfl)
      change S.val.graph.root _ at hh
      have hn : ∀ v : S.val.Vertex, v ∉ S.val.graph.root := by
        intro v
        rw [S.property.2.1]
        exact id
      exact False.elim (hn _ hh)

/--
---
conclusion: Lax369799.AcceptanceTheorems.accepting_unfold
---
Locally surjective maps identify yields; a common cover therefore
identifies all acceptance tests.
-/
theorem accepting_unfold {A : RankedSet} (L : Language A)
    (S T : SetSystem A 0) (h : UnfoldEquivalent S T) :
    Accepting L S ↔ Accepting L T := by
  obtain ⟨U, ⟨s, hs⟩, ⟨t, ht⟩⟩ := h
  have he (V) := ((Yields.morphism_yields s).2 hs V).symm.trans
    ((Yields.morphism_yields t).2 ht V)
  exact ⟨fun h V hv => h V ((he V).mpr hv), fun h V hv => h V ((he V).mp hv)⟩

/--
---
conclusion: Lax369799.AcceptanceTheorems.syntactic_morphism
---
Lift the morphism through each test context. Its yield inclusion reverses
the universal acceptance condition.
-/
theorem syntactic_morphism {A : RankedSet} (L : Language A) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) : SyntacticBelow L T S := by
  intro C h U hU
  exact h U ((Yields.morphism_yields (Evaluation.plug_morphism C f)).1 U hU)

private def identityContext (A : RankedSet) (n : ℕ) : SetContext A n n where
  system := atomic (A := WithHole A n) (Sum.inr ⟨rfl⟩)
  one_hole := ⟨(0 : Fin 1), ⟨⟨rfl⟩, rfl⟩, fun _ _ => Subsingleton.elim (α := Fin 1) _ _⟩

private theorem identity_cover {A : RankedSet} {n : ℕ} (S : SetSystem A n) :
    UnfoldsTo S (plug (identityContext A n) S) := by
  have he : relabel (substitution S) (identityContext A n).system = atomic S := rfl
  unfold plug
  rw [he]
  exact AtomicFlattening.outer_atomic_cover S

/--
---
conclusion: Lax369799.AcceptanceTheorems.syntactic_acceptance
---
Test the syntactic comparison in the context consisting of a single
initial hole. Its substitution covers the argument itself.
-/
theorem syntactic_acceptance {A : RankedSet} (L : Language A)
    {S T : SetSystem A 0} (h : SyntacticBelow L S T) :
    Accepting L S → Accepting L T := by
  intro hs
  have cover (U : SetSystem A 0) :
      Accepting L (plug (identityContext A 0) U) ↔ Accepting L U := by
    obtain ⟨f, hf⟩ := identity_cover U
    exact accepting_unfold L _ _
      ⟨_, ⟨identity _, identity_surjective _⟩, ⟨f, hf⟩⟩
  exact (cover T).mp (h (identityContext A 0) ((cover S).mpr hs))

end Lax369799Proofs.Acceptance
