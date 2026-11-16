import Lax369799.FiniteSyntacticAlgebra
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

/-!
---
title: Finite-state evaluation of terminating branch words
type: theorem
---
A finite unary word followed by a nullary value is evaluated by iterated
unary application. A deterministic word automaton stores the action of
the prefix on the nullary sort. Its state set is finite whenever that
sort is finite. Infinite words require a separate acceptance condition.
-/
namespace Lax369799.FiniteBranchWords
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra

def application {A : RankedSet} (b : A 1) (a : A 0) : FiniteSystem A 0 where
  size := 2
  graph := {
    label := Fin.cases ⟨1, b⟩ (fun _ => ⟨0, a⟩)
    initial := {0}
    root := ∅
    edge := fun v d t => v = 0 ∧ d = 0 ∧ t = .inl 1
    direction_valid := by rintro v d t ⟨rfl, rfl, _⟩; exact Nat.zero_lt_one }

def act {A : RankedSet} (E : Algebra A) (b : A 1) (a : A 0) : A 0 :=
  E.eval 0 (application b a)

def value {A : RankedSet} (E : Algebra A) (w : List (A 1)) (a : A 0) : A 0 :=
  w.foldr (act E) a

noncomputable def chain {A : RankedSet} : List (A 1) → A 0 → FiniteSystem A 0
  | [], a => atomic a
  | b :: w, a => flatten (application (atomic b) (chain w a))

axiom chain_evaluation {A : RankedSet} (E : Algebra A) (w : List (A 1)) (a : A 0) :
    E.eval 0 (chain w a) = value E w a

abbrev State (Z : Type) := Option ((Z → Z) ⊕ Z)

def machine {U Z : Type} (f : U → Z → Z) (F : Set Z) : DFA (U ⊕ Z) (State Z) where
  start := some (.inl id)
  step := fun s c => match s, c with
    | some (.inl g), .inl b => some (.inl (g ∘ f b))
    | some (.inl g), .inr a => some (.inr (g a))
    | _, _ => none
  accept := {s | ∃ a ∈ F, s = some (.inr a)}

axiom evaluate {U Z : Type} (f : U → Z → Z) (F : Set Z)
    (w : List U) (a : Z) :
    (machine f F).eval (w.map Sum.inl ++ [Sum.inr a]) = some (.inr (w.foldr f a))

axiom accepts {A : RankedSet} (E : Algebra A) (F : Set (A 0))
    (w : List (A 1)) (a : A 0) :
    w.map Sum.inl ++ [Sum.inr a] ∈ (machine (act E) F).accepts ↔ E.eval 0 (chain w a) ∈ F

axiom finite_states {Z : Type} [Finite Z] : Finite (State Z)

end Lax369799.FiniteBranchWords
