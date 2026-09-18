import Lax369799.UnfoldBranches
import Lax369799Proofs.PeriodicPaths
import Mathlib.Data.Fintype.Prod

namespace Lax369799Proofs.UnfoldBranches
open Lax369799.RankedSystems Lax369799.UnfoldAutomata Lax369799.UnfoldBranches

/--
---
conclusion: Lax369799.UnfoldBranches.periodic_test
---
Take the product of vertices, chosen directions, and word-automaton states.
Its transition relation preserves system edges and updates the word state.
A periodic witness in this finite product projects to a periodic branch
with the same least recurring priority.
-/
theorem periodic_test {A : RankedSet} (M : UnfoldAutomaton A) (S : System A 0) (r : Run M S) :
    (∀ b : InfiniteBranch S, Periodic b → M.condition.AcceptsInfinite
      (fun n => r.edgeType (b.vertex n) (b.direction n))) ↔
    (∀ b : InfiniteBranch S, M.condition.AcceptsInfinite
      (fun n => r.edgeType (b.vertex n) (b.direction n))) := by
  constructor
  · intro h b
    let V := (v : S.val.Vertex) × Fin (Rank S v)
    let Q := V × Fin M.condition.states
    let word := fun n => r.edgeType (b.vertex n) (b.direction n)
    let path : ℕ → Q := fun n => (⟨b.vertex n, b.direction n⟩, M.condition.run word n)
    let priority : Q → ℕ := fun q => M.condition.priority q.2
    let edge : Q → Q → Prop := fun q q' =>
      S.val.graph.edge q.1.1 q.1.2.val (.inl q'.1.1) ∧
        q'.2 = M.condition.step q.2 (.inl (r.edgeType q.1.1 q.1.2))
    have hp : ∀ n, edge (path n) (path (n + 1)) := fun n => ⟨b.follows n, rfl⟩
    obtain ⟨c, hc, _⟩ := WordParity.least_recurring priority path
    obtain ⟨path', hstart, hstep, hperiod, hc'⟩ :=
      PeriodicPaths.periodic_witness edge priority path hp c hc
    let b' : InfiniteBranch S := {
      vertex := fun n => (path' n).1.1
      direction := fun n => (path' n).1.2
      starts := by
        rw [hstart]
        exact b.starts
      follows := fun n => (hstep n).1 }
    let word' := fun n => r.edgeType (b'.vertex n) (b'.direction n)
    have hstate : ∀ n, M.condition.run word' n = (path' n).2 := by
      intro n
      induction n with
      | zero => exact (congrArg Prod.snd hstart).symm
      | succ n ih =>
        change M.condition.step (M.condition.run word' n) (.inl (word' n)) = _
        rw [ih]
        exact (hstep n).2.symm
    have hb' : Periodic b' := by
      obtain ⟨N, p, hp, he⟩ := hperiod
      exact ⟨N, p, hp, fun n hn => congrArg Prod.fst (he n hn)⟩
    have hacc := h b' hb'
    have hmin : Lax369799.WordParity.LeastRecurring
        (fun n => M.condition.priority (M.condition.run word' n)) c := by
      simpa only [hstate] using hc'
    have heven := (WordParity.acceptance_iff M.condition word' c hmin).mp hacc
    exact (WordParity.acceptance_iff M.condition word c hc).mpr heven
  · exact fun h b _ => h b

end Lax369799Proofs.UnfoldBranches
