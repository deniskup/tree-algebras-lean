import Lax369799Proofs.PriorityCompilation

open Lax369799.ModalMuCalculus Lax369799.PriorityCompilation

private def formulaSize {P : Type} : {n : ℕ} → Formula P n → ℕ
  | _, .top | _, .bot | _, .proposition _ | _, .negProposition _ | _, .variable _ => 1
  | _, .conj φ ψ | _, .disj φ ψ => 1 + formulaSize φ + formulaSize ψ
  | _, .diamond φ | _, .box φ | _, .mu φ | _, .nu φ => 1 + formulaSize φ

-- Compilation of a single even-priority successor equation yields νX.◇X.
-- #eval checks that this syntax compiler has executable code.
#eval formulaSize (sentence (fun _ : Fin 1 => 0)
  (fun _ => (Formula.diamond (.variable 0) : Formula Empty 1)) 1 0)

#print axioms Lax369799Proofs.PriorityCompilation.compile_correct
#print axioms Lax369799Proofs.PriorityCompilation.sentence_correct
