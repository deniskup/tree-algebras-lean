import Lax369799.FiniteBranchWords

namespace Lax369799Proofs.FiniteBranchWords
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations
open Lax369799.FiniteSyntacticAlgebra Lax369799.FiniteBranchWords

private theorem eval_prefix {U Z : Type} (f : U → Z → Z) (F : Set Z)
    (w : List U) (g : Z → Z) :
    (machine f F).evalFrom (some (.inl g)) (w.map Sum.inl) =
      some (.inl (fun a => g (w.foldr f a))) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    simpa only [List.map_cons, DFA.evalFrom_cons, machine, ih,
      List.foldr_cons, Function.comp_apply] using ih (g ∘ f b)

/--
---
conclusion: Lax369799.FiniteBranchWords.evaluate
---
The state after a unary prefix is its composed action. Reading the final
nullary letter applies that action and enters the corresponding final state.
-/
theorem evaluate {U Z : Type} (f : U → Z → Z) (F : Set Z)
    (w : List U) (a : Z) :
    (machine f F).eval (w.map Sum.inl ++ [Sum.inr a]) = some (.inr (w.foldr f a)) := by
  rw [DFA.eval, DFA.evalFrom_append_singleton]
  change (machine f F).step ((machine f F).evalFrom (some (.inl id)) (w.map Sum.inl)) (.inr a) = _
  rw [eval_prefix]
  rfl

private theorem relabel_application {A B : RankedSet} (f : Lax369799.RankedSystems.RankedMap A B)
    (b : A 1) (a : A 0) : relabel f (application b a) = application (f 1 b) (f 0 a) := by
  dsimp only [relabel, application]
  congr 1
  congr 1
  funext v
  exact Fin.cases rfl (fun _ => rfl) v

/--
---
conclusion: Lax369799.FiniteBranchWords.chain_evaluation
---
Associativity evaluates each unary prefix before its suffix. Induction
identifies the whole path presentation with iterated unary application.
-/
theorem chain_evaluation {A : RankedSet} (E : Algebra A) (w : List (A 1)) (a : A 0) :
    E.eval 0 (chain w a) = value E w a := by
  induction w with
  | nil => exact E.unit 0 a
  | cons b w ih =>
    change E.eval 0 (flatten (application (atomic b) (chain w a))) = _
    rw [← E.associative, relabel_application, E.unit, ih]
    rfl

/--
---
conclusion: Lax369799.FiniteBranchWords.accepts
---
Acceptance of a terminating branch word is membership of its iterated
unary evaluation in the accepting nullary set.
-/
theorem accepts {A : RankedSet} (E : Algebra A) (F : Set (A 0))
    (w : List (A 1)) (a : A 0) :
    w.map Sum.inl ++ [Sum.inr a] ∈ (machine (act E) F).accepts ↔ E.eval 0 (chain w a) ∈ F := by
  rw [chain_evaluation]
  change (machine (act E) F).eval _ ∈ (machine (act E) F).accept ↔ _
  rw [evaluate]
  change (∃ b ∈ F, some (Sum.inr (value E w a)) = some (Sum.inr b)) ↔ _
  simp

/--
---
conclusion: Lax369799.FiniteBranchWords.finite_states
---
There are finitely many functions on a finite nullary sort, together with
finitely many final values and one dead state.
-/
theorem finite_states {Z : Type} [Finite Z] : Finite (State Z) := by
  classical
  let : Fintype Z := Fintype.ofFinite Z
  exact Finite.of_fintype (State Z)

end Lax369799Proofs.FiniteBranchWords
