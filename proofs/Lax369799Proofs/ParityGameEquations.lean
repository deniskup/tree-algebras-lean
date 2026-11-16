import Lax369799.ParityGameEquations
import Lax369799Proofs.ParityFixedPoints

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.ParityGameEquations
open Lax369799.FiniteParityGames Lax369799.ParityWinningRegions
open Lax369799.ParityFixedPoints
attribute [local instance] Classical.propDecidable

open Lax369799.ParityGameEquations

private theorem game_ext {V : Type} {G H : Game V}
    (ho : G.eve = H.eve) (he : G.edge = H.edge) (hp : G.priority = H.priority) : G = H := by
  cases G
  cases H
  cases ho
  cases he
  cases hp
  rfl

private theorem cut_phase {V : Type} (G : Game V) (n : ℕ) (ρ : ℕ → Set V) (X : Set V) :
    phase (cut G (n + 1) ρ) {v | G.priority v = n} true X =
      cut G n (Function.update ρ n X) := by
  apply game_ext
  · rfl
  · funext v w
    rcases lt_trichotomy (G.priority v) n with h | h | h
    · simp [phase, cut, stop, show ¬ n ≤ G.priority v by omega,
        show ¬ n < G.priority v by omega, show G.priority v ≠ n by omega]
    · simp [phase, cut, stop, h]
    · simp [phase, cut, stop, show n ≤ G.priority v by omega,
        show n < G.priority v by omega, show G.priority v ≠ n by omega]
  · funext v
    rcases lt_trichotomy (G.priority v) n with h | h | h
    · simp [phase, cut, stop, show ¬ n ≤ G.priority v by omega,
        show ¬ n < G.priority v by omega, show G.priority v ≠ n by omega]
    · simp [phase, cut, stop, pre, Owned, h]
    · simp [phase, cut, stop, show n ≤ G.priority v by omega,
        show n < G.priority v by omega, show G.priority v ≠ n by omega]

/--
---
conclusion: Lax369799.ParityGameEquations.solve_cut
---
Induct on the priority cutoff. The zero case consists only of absorbing positions. The induction step is the proved one-priority elimination theorem, with a boundary valuation updated at that priority.
-/
theorem solve_cut {V : Type} [Finite V] (G : Game V) (n : ℕ) (ρ : ℕ → Set V) :
    (Winning (cut G n ρ) true : Set V) = solve G n ρ := by
  induction n generalizing ρ with
  | zero =>
    ext v
    exact (ParityFixedPoints.terminal_winning G _ _ true v (Nat.zero_le _)).trans
      (by simp only [solve, iff_true]; rfl)
  | succ n ih =>
    let C : Set V := {v | G.priority v = n}
    have hC : ∀ v ∈ C, (cut G (n + 1) ρ).priority v = n := by
      intro v hv
      change G.priority v = n at hv
      simp [cut, stop, hv]
    have hbound : ∀ v, n < (cut G (n + 1) ρ).priority v →
        ∀ w, (cut G (n + 1) ρ).edge v w → w = v := by
      intro v hv w hw
      by_cases hs : n + 1 ≤ G.priority v
      · simpa only [cut, stop, Set.mem_ofPred_eq, if_pos hs] using hw
      · have hg : (cut G (n + 1) ρ).priority v = G.priority v := by simp only [cut, stop, Set.mem_ofPred_eq, if_neg hs]
        rw [hg] at hv
        omega
    have hF : ∀ X : Set V,
        (Winning (phase (cut G (n + 1) ρ) C true X) true : Set V) =
          solve G n (Function.update ρ n X) := by
      intro X
      rw [show C = {v | G.priority v = n} from rfl, cut_phase]
      exact ih _
    by_cases hp : Even n
    · have he := ParityFixedPoints.greatest (cut G (n + 1) ρ) C n hC hbound hp
      simpa only [solve, if_pos hp, hF] using he
    · have he := ParityFixedPoints.least (cut G (n + 1) ρ) C n hC hbound hp
      simpa only [solve, if_neg hp, hF] using he

/--
---
conclusion: Lax369799.ParityGameEquations.winning
---
Above every priority the stopped arena is the original arena. The nested equations therefore give exactly its positional winning region.
-/
theorem winning {V : Type} [Finite V] (G : Game V) (n : ℕ)
    (hn : ∀ v, G.priority v < n) (ρ : ℕ → Set V) :
    (Winning G true : Set V) = solve G n ρ := by
  have he : cut G n ρ = G := by
    apply game_ext
    · rfl
    · funext v w
      simp [cut, stop, show ¬ n ≤ G.priority v from Nat.not_le.mpr (hn v)]
    · funext v
      simp [cut, stop, show ¬ n ≤ G.priority v from Nat.not_le.mpr (hn v)]
  have h := solve_cut G n ρ
  rwa [he] at h

end Lax369799Proofs.ParityGameEquations
