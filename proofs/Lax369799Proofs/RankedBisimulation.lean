import Lax369799.RankedBisimulation
import Lax369799Proofs.SystemSubstitution

namespace Lax369799Proofs.RankedBisimulation
open Lax369799.RankedSystems Lax369799.Morphisms
open Lax369799.TransitionSystems Lax369799.TransitionEncoding

/--
---
conclusion: Lax369799.RankedBisimulation.bisimilarity_equivalence
---
Use equality, reverse a bisimulation, and compose two bisimulations by
existential quantification over the intermediate vertex.
-/
theorem bisimilarity_equivalence (P : Type) : Equivalence (@Bisimilar P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    refine ⟨Eq, rfl, ?_⟩
    rintro v w rfl
    exact ⟨rfl, fun v' h => ⟨v', h, rfl⟩, fun w' h => ⟨w', h, rfl⟩⟩
  · rintro S T ⟨R, hinit, hR⟩
    refine ⟨fun v w => R w v, hinit, ?_⟩
    intro v w h
    have hh := hR w v h
    exact ⟨hh.1.symm, hh.2.2, hh.2.1⟩
  · rintro S T U ⟨R, hR0, hR⟩ ⟨Q, hQ0, hQ⟩
    refine ⟨fun v z => ∃ w, R v w ∧ Q w z, ⟨_, hR0, hQ0⟩, ?_⟩
    rintro v z ⟨w, hr, hq⟩
    have hr := hR v w hr
    have hq := hQ w z hq
    refine ⟨hr.1.trans hq.1, ?_, ?_⟩
    · intro v' hv
      obtain ⟨w', hw, hr'⟩ := hr.2.1 v' hv
      obtain ⟨z', hz, hq'⟩ := hq.2.1 w' hw
      exact ⟨z', hz, w', hr', hq'⟩
    · intro z' hz
      obtain ⟨w', hw, hq'⟩ := hq.2.2 z' hz
      obtain ⟨v', hv, hr'⟩ := hr.2.2 w' hw
      exact ⟨v', hv, w', hr', hq'⟩

theorem morphism_decode {P : Type} (S T : System (TransitionAlphabet P) 0)
    (f : Morphism S.val T.val) : Bisimilar (decode S) (decode T) := by
  have hf := MorphismTheorems.system_morphism_locally_surjective S T f
  have hS : (decode S).initial ∈ S.val.graph.initial := by
    rw [Classical.choose_spec S.property.1]
    rfl
  have hinit : f.toFun (decode S).initial = (decode T).initial := by
    have h := f.initial _ hS
    rw [Classical.choose_spec T.property.1] at h
    exact h
  refine ⟨fun v w => f.toFun v = w, hinit, ?_⟩
  rintro v w rfl
  refine ⟨?_, ?_, ?_⟩
  · exact (congrArg (fun a : Symbol (TransitionAlphabet P) => a.2) (f.label v)).symm
  · rintro v' ⟨d, hd⟩
    exact ⟨f.toFun v', ⟨d, f.edge v d (.inl v') hd⟩, rfl⟩
  · rintro w' ⟨d, hd⟩
    obtain ⟨t, ht, he⟩ := hf.2.2 v d (.inl w') hd
    cases t with
    | inl v' => exact ⟨v', ⟨d, ht⟩, Sum.inl.inj he⟩
    | inr i => exact Fin.elim0 i

private theorem isomorphic_decode {P : Type} (S T : TransitionSystem P)
    (h : Isomorphic S T) : Bisimilar S T := by
  obtain ⟨e, he, hv, hedge⟩ := h
  refine ⟨fun v w => e v = w, he, ?_⟩
  rintro v w rfl
  refine ⟨hv v, fun v' h => ⟨e v', (hedge v v').mp h, rfl⟩, ?_⟩
  intro w' h
  obtain ⟨v', rfl⟩ := e.surjective w'
  exact ⟨v', (hedge v v').mpr h, rfl⟩

/--
---
conclusion: Lax369799.RankedBisimulation.ranked_forward
---
A ranked system morphism is locally surjective and decodes to a
bisimulation. A common ranked unfolding therefore gives bisimilar
decodings. Isomorphisms and equivalence closure preserve bisimilarity.
-/
theorem ranked_forward {P : Type} (S T : System (TransitionAlphabet P) 0)
    (h : RankedBisimilar S T) : Bisimilar (decode S) (decode T) := by
  induction h with
  | rel S T h =>
    rcases h with h | h
    · obtain ⟨R, ⟨s⟩, ⟨t⟩⟩ := SystemSubstitution.common_system S T h
      exact (bisimilarity_equivalence P).trans
        ((bisimilarity_equivalence P).symm (morphism_decode R S s)) (morphism_decode R T t)
    · exact isomorphic_decode _ _ h
  | refl S => exact (bisimilarity_equivalence P).refl _
  | symm S T h ih => exact (bisimilarity_equivalence P).symm ih
  | trans S T U hst htu ihst ihtu => exact (bisimilarity_equivalence P).trans ihst ihtu

end Lax369799Proofs.RankedBisimulation
