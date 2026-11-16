import Lax369799.SupportedYields
import Lax369799.FiniteYieldContinuity

/-!
---
title: Finite yield approximation with supported witnesses
type: theorem
---
Corollary 50 for unpruned contexts. Each approximating component records
a fully supported system, its variable map, and its initial or root
yield witness. The disjoint sum realizes those maps before insertion.
Both initial and root target yields retain their original variable map.
-/

namespace Lax369799.SupportedYieldContinuity
open RankedSystems FinitePresentations SupportedMorphisms SupportedYields

structure Component {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) where
  arity : ℕ
  system : SupportedSystems.System A arity
  variableMap : Fin arity → Fin n
  rooted : Bool
  yields : if rooted then RootYield S system variableMap else InitialYield S system variableMap

def Component.realize {A : RankedSet} {n : ℕ} {S : FiniteSystem A n} (c : Component S) : SetSystem A n :=
  if c.rooted then RankedSystems.plant (Renaming.renameSystem c.variableMap c.system.val).val
    else (Renaming.renameSystem c.variableMap c.system.val).val

noncomputable def realizationSum {A : RankedSet} {n m : ℕ} {S : FiniteSystem A n}
    (F : Fin m → Component S) : FiniteSystem A n :=
  ofSetSystem (YieldContinuity.finiteSum (fun i => (F i).realize))


open FiniteContexts

axiom initial_continuity {A : RankedSet} {k n r : ℕ} (C : Context A k n)
    (S : FiniteSystem A k) (U : SupportedSystems.System A r) (σ : Fin r → Fin n) :
    InitialYield (plug C S) U σ ↔
      ∃ (m : ℕ) (F : Fin m → Component S), InitialYield (plug C (realizationSum F)) U σ

axiom root_continuity {A : RankedSet} {k n r : ℕ} (C : Context A k n)
    (S : FiniteSystem A k) (U : SupportedSystems.System A r) (σ : Fin r → Fin n) :
    RootYield (plug C S) U σ ↔
      ∃ (m : ℕ) (F : Fin m → Component S), RootYield (plug C (realizationSum F)) U σ

end Lax369799.SupportedYieldContinuity
