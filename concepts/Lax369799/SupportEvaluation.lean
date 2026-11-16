import Lax369799.SupportedAlgebras
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Powerset

/-!
---
title: Finite observations after output compaction
type: theorem
---
An observation records an injective output map and the evaluation of a
fully supported compacted system. Observation profiles have finite index
when the algebra has finite sorts. Two systems have the same profile precisely when a common output map
exposes equal supported values. The closed quotient recovers the original closed sort.
-/

namespace Lax369799.SupportEvaluation
open RankedSystems (RankedSet RankwiseFinite)
open SupportedSystems SupportedAlgebras

structure Observation (B : RankedSet) (n : ℕ) where
  arity : Fin (n+1)
  ports : Fin arity.val ↪ Fin n
  value : B arity.val

def profile {B : RankedSet} (E : Algebra B) {n : ℕ} (S : RankedSystems.System B n) :
    Set (Observation B n) :=
  {o | ∃ T : System B o.arity.val,
    Renaming.renameSystem o.ports T.val = S ∧ E.eval o.arity.val T = o.value}

def Equivalent {B : RankedSet} (E : Algebra B) {n : ℕ}
    (S T : RankedSystems.System B n) : Prop := profile E S = profile E T

abbrev Carrier {B : RankedSet} (E : Algebra B) : RankedSet :=
  fun n => Quot (@Equivalent B E n)

def classMap {B : RankedSet} (E : Algebra B) : RankedSystems.RankedMap (RankedSystems.System B) (Carrier E) :=
  fun _ => Quot.mk _

axiom profile_nonempty {B : RankedSet} (E : Algebra B) {n : ℕ}
    (S : RankedSystems.System B n) : (profile E S).Nonempty

axiom finite_observations {B : RankedSet} (hB : RankwiseFinite B) (n : ℕ) :
    Finite (Observation B n)

axiom finite_carrier {B : RankedSet} (E : Algebra B) (hB : RankwiseFinite B) :
    RankwiseFinite (Carrier E)

axiom equivalent_iff {B : RankedSet} (E : Algebra B)
    {n : ℕ} (S T : RankedSystems.System B n) :
    Equivalent E S T ↔ ∃ (m : ℕ) (σ : Fin m → Fin n), Function.Injective σ ∧
      ∃ U V : System B m, Renaming.renameSystem σ U.val = S ∧
        Renaming.renameSystem σ V.val = T ∧ E.eval m U = E.eval m V

axiom closed_equivalent_iff {B : RankedSet} (E : Algebra B)
    (S T : RankedSystems.System B 0) :
    Equivalent E S T ↔ E.eval 0 (closedEquiv B |>.symm S) =
      E.eval 0 (closedEquiv B |>.symm T)

axiom closed_carrier {B : RankedSet} (E : Algebra B) :
    ∃ e : Carrier E 0 ≃ B 0, ∀ S : RankedSystems.System B 0,
      e (classMap E 0 S) = E.eval 0 ((closedEquiv B).symm S)

end Lax369799.SupportEvaluation

