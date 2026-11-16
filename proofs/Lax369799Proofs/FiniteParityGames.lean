import Lax369799.FiniteParityGames
import Lax369799Proofs.ParityDeterminacy

namespace Lax369799Proofs.FiniteParityGames
open Lax369799.FiniteParityGames WordAutomata

/--
---
conclusion: Lax369799.FiniteParityGames.positional_determinacy
---
Apply the finite-arena Zielonka proof to the whole arena. The proof of
that construction is adapted from the ancillary Lean development of
Bojańczyk, Casares, Manthe and Parys (2026).
-/
theorem positional_determinacy {V : Type} [Finite V] (G : Game V) :
    ∃ f g : V → V, G.Legal true f ∧ G.Legal false g ∧
      ∀ v, G.WinsFrom true f v ∨ G.WinsFrom false g v := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let a : FinGame.Arena V := ⟨G.eve, G.edge, G.priority⟩
  have hclosed : a.Closed Set.univ := by
    intro v _
    obtain ⟨w, hw⟩ := G.total v
    exact ⟨w, Set.mem_univ _, hw⟩
  obtain ⟨f, g, hf, hg, hwin⟩ := FinGame.Arena.determined a Set.univ hclosed
  refine ⟨f, g, ?_, ?_, fun v => ?_⟩
  · intro v hv
    exact (hf v (Set.mem_univ _) (hv.mpr rfl)).2
  · intro v hv
    exact (hg v (Set.mem_univ _) (fun h => Bool.false_ne_true (hv.mp h))).2
  · rcases hwin v (Set.mem_univ _) with h | h
    · left
      intro p hp hp0 hc
      have he := h p ⟨hp, fun _ => Set.mem_univ _⟩ hp0
        (fun n hn => hc n ⟨fun _ => rfl, fun _ => hn⟩)
      change G.EveWins p at he
      exact ⟨fun _ => rfl, fun _ => he⟩
    · right
      intro p hp hp0 hc
      have he := h p ⟨hp, fun _ => Set.mem_univ _⟩ hp0
        (fun n hn => hc n ⟨fun h => (hn h).elim,
          fun h => (Bool.false_ne_true h).elim⟩)
      change ¬ G.EveWins p at he
      exact ⟨fun h => (he h).elim, fun h => Bool.false_ne_true h |>.elim⟩

end Lax369799Proofs.FiniteParityGames
