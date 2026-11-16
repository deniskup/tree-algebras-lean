import Lax369799.UnaryGraphEvaluation
import Lax369799.UnfoldAutomata
import Lax369799.FinitePathEvaluation

/-!
---
title: Algebraic evaluation and the words of a regular branch
type: theorem
---
A closed deterministic system with only unary and nullary labels follows
one branch. Its value is accepted exactly when its terminating branch
word, or its infinite branch word, satisfies the corresponding algebraic
word condition. This includes both chains ending at a nullary vertex and
infinite branches represented by finite graphs.
-/

namespace Lax369799.UnarySystemEvaluation
open RankedSystems (RankedSet System)
open FinitePresentations FiniteSyntacticAlgebra UnfoldAutomata SetSystemAlgebras

def Unary {A : RankedSet} (S : System A 0) : Prop := ∀ v, Rank S v ≤ 1

def unaryLabel {A : RankedSet} {S : System A 0} (hu : Unary S)
    (v : S.val.Vertex) (d : Fin (Rank S v)) : A 1 := by
  have h : Rank S v = 1 := by have := hu v; have := d.isLt; omega
  exact h ▸ (S.val.graph.label v).2

def finiteWord {A : RankedSet} {S : System A 0} (hu : Unary S)
    {k : ℕ} (b : FiniteBranch S k) : List (A 1) :=
  List.ofFn (fun i => unaryLabel hu (b.vertex i.castSucc) (b.direction i))

def leafValue {A : RankedSet} {S : System A 0} {k : ℕ} (b : FiniteBranch S k) : A 0 :=
  b.ends ▸ (S.val.graph.label (b.vertex (Fin.last k))).2

def infiniteWord {A : RankedSet} {S : System A 0} (hu : Unary S)
    (b : InfiniteBranch S) : ℕ → A 1 := fun n => unaryLabel hu (b.vertex n) (b.direction n)

axiom agreement {A : RankedSet} (E : SetAlgebra A)
    (F : Set (A 0)) [Finite (A 1)] (S : System A 0) (hu : Unary S) :
    E.eval 0 (ofSetSystem S.val) ∈ F ↔
      (∀ k (b : FiniteBranch S k), FiniteBranchWords.value E.toAlgebra (finiteWord hu b) (leafValue b) ∈ F) ∧
      (∀ b : InfiniteBranch S, AlgebraicOmegaWords.Accepts E.toAlgebra F (infiniteWord hu b))

end Lax369799.UnarySystemEvaluation
