import Lax369799.PriorityCompilation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Finset.Sort

/-!
---
title: Executable modal compilation from finite Boolean tables
type: theorem
---
An explicit encoding orders each finite table type and makes its complete
enumeration executable. Boolean valuation, leaf and support tables compile
to positive modal transitions and then to scalar fixed-point syntax.
Every bounded word condition and its modal tests have such a finite code.
-/

namespace Lax369799.FiniteModalData
open ModalMuCalculus ModalTransitions UnfoldAutomata

def elements (α : Type) [Fintype α] [Encodable α] : List α :=
  letI : LinearOrder α := LinearOrder.lift' (fun a : α => Encodable.encode a) Encodable.encode_injective
  Finset.univ.sort (· ≤ ·)

abbrev Data (P : Type) (u z d p : ℕ) :=
  Fin d × (Fin d → (Fin u ⊕ Fin z) → Fin d) ×
    (Fin d → Fin (p+1)) × (Fin d → Bool) ×
    ((P → Bool) → Fin z → Bool) × ((P → Bool) → (Fin u → Bool) → Bool)

def word {P : Type} {u z d p : ℕ} (t : Data P u z d p) : WordCondition u z where
  states := d
  initial := t.1
  step := t.2.1
  priority := fun q => (t.2.2.1 q).val
  final := {q | t.2.2.2.1 q = true}

def valuationFormula {P : Type} [Fintype P] [Encodable P] {n : ℕ} (ν : P → Bool) : Formula P n :=
  conjunction ((elements P).map (fun a => if ν a then .proposition a else .negProposition a))

def supportFormula {P : Type} {u z d p : ℕ} (t : Data P u z d p) (q : Fin d)
    (B : Fin u → Bool) : Formula P d :=
  let bs := (elements (Fin u)).filter (fun b => B b = true)
  .conj (conjunction (bs.map (fun b => .diamond (.variable (t.2.1 q (.inl b))))))
    (.box (disjunction (bs.map (fun b => .variable (t.2.1 q (.inl b))))))

def transition {P : Type} [Fintype P] [Encodable P] [DecidableEq P] {u z d p : ℕ}
    (t : Data P u z d p) (q : Fin d) : Formula P d :=
  disjunction ((elements (P → Bool)).map (fun ν : P → Bool =>
    .conj (valuationFormula ν) (.disj
      (if ∃ a : Fin z,t.2.2.2.2.1 ν a = true ∧ t.2.2.2.1 (t.2.1 q (.inr a)) = true
        then .box .bot else .bot)
      (disjunction (((elements (Fin u → Bool)).filter (fun B => t.2.2.2.2.2 ν B = true)).map (supportFormula t q))))))

def compile {P : Type} [Fintype P] [Encodable P] [DecidableEq P] {u z d p : ℕ}
    (t : Data P u z d p) : Sentence P :=
  let D := word t
  PriorityCompilation.sentence (fun q => ModalAcceptanceGame.ceiling D - D.priority q)
    (transition t) (ModalAcceptanceGame.ceiling D+1) D.initial

open TransitionEncoding TransitionSystems

axiom exists_table {P : Type} [Fintype P] [Encodable P] [DecidableEq P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (p : ℕ)
    (hp : ∀ q,M.condition.priority q ≤ p) :
    ∃ t : Data P M.unary M.nullary M.condition.states p,
      ∀ S,Models S (compile t) ↔ ParityWinningRegions.Winning (ModalAcceptanceGame.game M S) true
        (ModalAcceptanceGame.position M.condition.initial S.initial)

end Lax369799.FiniteModalData