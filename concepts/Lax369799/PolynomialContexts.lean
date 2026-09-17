import Lax369799.Algebras

/-!
---
title: Polynomial contexts of a system algebra
type: theorem
---
Polynomial contexts are functions obtained from a variable and constants by
system evaluation. They may use the variable at several vertices. Testing
all closed polynomial contexts against an accepting set gives a congruence
for evaluation. This construction does not presume unfolding invariance.
-/
namespace Lax369799.PolynomialContexts
open RankedSystems Algebras

abbrev Shape := System (fun _ => Unit)

def withLabels {A B : RankedSet} {n : ℕ} (P : System A n)
    (f : ∀ v, B (P.val.graph.label v).1) : System B n :=
  ⟨{ P.val with graph := { P.val.graph with label := fun v => ⟨(P.val.graph.label v).1, f v⟩ } }, P.property⟩

inductive Polynomial {B : RankedSet} (E : Algebra B) (k : ℕ) : ∀ n, (B k → B n) → Prop
  | variable : Polynomial E k k id
  | constant (n : ℕ) (b : B n) : Polynomial E k n (fun _ => b)
  | evaluation {n : ℕ} (P : Shape n) (f : ∀ v, B k → B (P.val.graph.label v).1)
      (hf : ∀ v, Polynomial E k (P.val.graph.label v).1 (f v)) :
      Polynomial E k n (fun x => E.eval n (withLabels P (fun v => f v x)))

def Equivalent {B : RankedSet} (E : Algebra B) (F : Set (B 0)) {n : ℕ} (a b : B n) : Prop :=
  ∀ p : B n → B 0, Polynomial E n 0 p → (p a ∈ F ↔ p b ∈ F)

axiom composition {B : RankedSet} (E : Algebra B) {k m n : ℕ}
    {f : B m → B n} {g : B k → B m} (hf : Polynomial E m n f) (hg : Polynomial E k m g) :
    Polynomial E k n (f ∘ g)

axiom evaluation_congruence {A B : RankedSet} (E : Algebra B) (F : Set (B 0))
    {n : ℕ} (P : System A n) (q r : ∀ v, B (P.val.graph.label v).1)
    (h : ∀ v, Equivalent E F (q v) (r v)) :
    Equivalent E F (E.eval n (withLabels P q)) (E.eval n (withLabels P r))

end Lax369799.PolynomialContexts
