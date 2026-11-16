import Lax369799.FiniteProfiles

/-!
---
title: Finite families of split-variable resolutions
type: theorem
---
A bounded profile can be represented by finitely many actual resolutions,
retaining each resolution's variable map. A rank-n representative needs
only resolutions of rank at most n times the fibre bound. In particular,
unary representatives may require multi-variable resolutions; these are
retained rather than replaced by unary branches.
-/
namespace Lax369799.ResolutionFamilies
open RankedSystems Resolutions FiniteProfiles

structure Witness {A : RankedSet} {n : ℕ} (S : SetSystem A n) where
  arity : ℕ
  system : System A arity
  variableMap : Fin arity → Fin n
  resolves : IsResolution S system variableMap

def Witness.entry {A B : RankedSet} (ρ : ∀ n, System A n → B n) {n : ℕ}
    {S : SetSystem A n} (w : Witness S) : ProfileEntry B n :=
  ⟨w.arity, ρ w.arity w.system, w.variableMap⟩

axiom finite_family {A B : RankedSet} (hB : RankwiseFinite B) (bound : ℕ)
    (ρ : ∀ n, System A n → B n) {n : ℕ} (S : SetSystem A n) :
    ∃ (k : ℕ) (w : Fin k → Witness S),
      (∀ i, (w i).arity ≤ n * bound) ∧
      BoundedProfile bound ρ S = Set.range (fun i => (w i).entry ρ)

end Lax369799.ResolutionFamilies
