import Lax369799.DeterministicPieces
import Lax369799.SystemEvaluation

/-!
---
title: Deterministic normal forms with identity continuations
type: theorem
---
A closed deterministic context is represented by its hole value and the
optional values of its unary continuations. A missing continuation copies
the hole behavior. Vertex zero is the distinguished hole copy; the next
vertex is the entry continuation; the remaining vertices correspond to
hole directions. Every nonempty unary continuation returns to vertex zero.
-/
namespace Lax369799.DeterministicNormalForms
open RankedSystems Flattening Algebras DeterministicPieces

/-- Missing unary pieces are copies of the distinguished vertex. -/
def label {A : RankedSet} {k : ℕ} (a : A k) (P : Fin (k + 1) → Option (A 1)) :
    Fin (k + 2) → Symbol A :=
  Fin.cases ⟨k, a⟩ (fun i => match P i with
    | none => ⟨k, a⟩
    | some b => ⟨1, b⟩)

def holeNext (k d : ℕ) : Fin (k + 2) :=
  if h : d < k then ⟨d + 2, Nat.add_lt_add_right h 2⟩ else 0

def next {A : RankedSet} {k : ℕ} (_a : A k) (P : Fin (k + 1) → Option (A 1))
    (v : Fin (k + 2)) (d : ℕ) : Fin (k + 2) :=
  Fin.cases (holeNext k d) (fun i => (P i).elim (holeNext k d) (fun _ => 0)) v

def graph {A : RankedSet} {k : ℕ} (a : A k) (P : Fin (k + 1) → Option (A 1)) :
    Presentation A 0 (Fin (k + 2)) where
  label := label a P
  initial := {1}
  root := ∅
  edge := fun v d t => ∃ _hd : d < (label a P v).1, t = .inl (next a P v d)
  direction_valid := fun _ _ _ h => h.choose


axiom pattern_exists {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) :
    ∃ T : System A 0, T.val = trim (graph a P)

axiom normal_form {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {k : ℕ} (C : SetContext A k 0) (hC : C.system.Deterministic) (S : System A k) :
    ∃ U V : System A 0,
      U.val = plug C S.val ∧
      V.val = trim (graph (E.eval k S) (fun i => (continuation C i).map (E.eval 1))) ∧
      E.eval 0 U = E.eval 0 V

end Lax369799.DeterministicNormalForms
