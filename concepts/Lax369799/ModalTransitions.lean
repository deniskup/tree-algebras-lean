import Lax369799.BisimAutomata
import Lax369799.ModalMuCalculus
import Mathlib.Data.Fintype.Powerset

/-!
---
title: Modal transitions obtained from type supports
type: theorem
---
Section 6.4 replaces each transition tuple by its support. Each type in
the support must occur at some successor, and every successor must have
some type in the support. Nullary transitions test the final word state
and the absence of successors. These conditions are expressible by
finite positive modal formulas.
-/
namespace Lax369799.ModalTransitions
open TransitionEncoding TransitionSystems UnfoldAutomata ModalMuCalculus

def Realized {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (ν : Set P) (B : Set (Fin M.unary)) : Prop :=
  ∃ (n : ℕ) (b : Fin (n + 1) → Fin M.unary), b ∈ M.transition n ν ∧ Set.range b = B

def OneStep {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (q : Fin M.condition.states) (S : TransitionSystem P) (v : S.Vertex)
    (ρ : Fin M.condition.states → Set S.Vertex) : Prop :=
  ((∃ a ∈ M.leafTransition (S.valuation v), M.condition.step q (.inr a) ∈ M.condition.final) ∧
    ∀ w, ¬ S.edge v w) ∨
  ∃ B, Realized M (S.valuation v) B ∧
    (∀ b ∈ B, ∃ w, S.edge v w ∧ w ∈ ρ (M.condition.step q (.inl b))) ∧
    (∀ w, S.edge v w → ∃ b ∈ B, w ∈ ρ (M.condition.step q (.inl b)))

def conjunction {P : Type} {n : ℕ} (l : List (Formula P n)) : Formula P n :=
  l.foldr Formula.conj .top

def disjunction {P : Type} {n : ℕ} (l : List (Formula P n)) : Formula P n :=
  l.foldr Formula.disj .bot

noncomputable def valuationFormula {P : Type} [Fintype P] {n : ℕ} (ν : Set P) : Formula P n := by
  classical
  exact conjunction (Finset.univ.toList.map (fun p =>
    if p ∈ ν then .proposition p else .negProposition p))

noncomputable def supportFormula {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (q : Fin M.condition.states) (B : Set (Fin M.unary)) : Formula P M.condition.states := by
  classical
  let bs := (Finset.univ.filter (fun b => b ∈ B)).toList
  exact .conj
    (conjunction (bs.map (fun b => .diamond (.variable (M.condition.step q (.inl b))))))
    (.box (disjunction (bs.map (fun b => .variable (M.condition.step q (.inl b))))))

noncomputable def transitionFormula {P : Type} [Fintype P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (q : Fin M.condition.states) :
    Formula P M.condition.states := by
  classical
  exact disjunction (Finset.univ.toList.map (fun ν : Set P =>
    Formula.conj (valuationFormula ν) (.disj
      (if ∃ a ∈ M.leafTransition ν, M.condition.step q (.inr a) ∈ M.condition.final
        then .box .bot else .bot)
      (disjunction ((Finset.univ.filter (Realized M ν)).toList.map (supportFormula M q))))))

axiom eval_transition {P : Type} [Fintype P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (q : Fin M.condition.states)
    (S : TransitionSystem P) (ρ : Fin M.condition.states → Set S.Vertex) (v : S.Vertex) :
    v ∈ (transitionFormula M q).eval S ρ ↔ OneStep M q S v ρ

axiom realized_nonempty {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (ν : Set P) (B : Set (Fin M.unary)) (h : Realized M ν B) : B.Nonempty

def marking {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    {S : RankedSystems.System (TransitionAlphabet P) 0} (r : Run M S)
    (q : Fin M.condition.states) (v : S.val.Vertex) :
    Fin M.condition.states → Set S.val.Vertex :=
  fun p => {w | ∃ i, S.val.graph.edge v i.val (.inl w) ∧
    M.condition.step q (.inl (r.edgeType v i)) = p}

axiom run_marking {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    {S : RankedSystems.System (TransitionAlphabet P) 0} (r : Run M S)
    (q : Fin M.condition.states) (v : S.val.Vertex)
    (hfinal : ∀ h : Rank S v = 0,
      M.condition.step q (.inr (r.leafType v h)) ∈ M.condition.final) :
    OneStep M q (decode S) v (marking M r q v)

end Lax369799.ModalTransitions
