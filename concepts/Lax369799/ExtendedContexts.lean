import Lax369799.ExtremalSituations

/-!
---
title: Formal unary pieces and extremal accepted situations
type: theorem
---
Definition 65 retains the immediate initial and root exits as two formal
markers alongside an ordinary unary value. A closed context made from
these pieces is an ordinary finite presentation: the initial marker of
piece zero marks the hole initial, a root marker in any piece marks it
root, and an initial marker in direction i adds a self-loop in that
direction. In the syntactic algebra, planting identifies the two hole
marks. Saturating their redundant formal representations relates
Definition 85 exactly to minimal planted situations.
-/

namespace Lax369799.ExtendedContexts
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra
open FiniteAcceptance ExpandedSyntacticAlgebra
open ExtremalContexts (Data)

inductive Marker where
  | initial
  | root
  deriving DecidableEq

instance : Fintype Marker where
  elems := {.initial, .root}
  complete := by intro m; cases m <;> simp

abbrev Piece (A : RankedSet) := A 1 × Set Marker
abbrev Pieces (A : RankedSet) (k : ℕ) := Fin (k + 1) → Piece A

def PieceBelow {A : RankedSet} (F : ClosedProperty A)
    (p q : Piece (Carrier F)) : Prop :=
  ClassBelow F p.1 q.1 ∧ q.2 ⊆ p.2

def context {A : RankedSet} {k : ℕ} (p : Pieces A k) : Context A k 0 where
  system := {
    size := k + 2
    graph := {
      label := (ExtremalContexts.normalPresentation
        (A := A) ⟨False, ∅⟩ (fun i => (p i).1)).label
      initial := fun v => v = (0 : Fin (k + 1)).succ ∨
        (v = 0 ∧ Marker.initial ∈ (p 0).2)
      root := fun v => v = 0 ∧ ∃ i, Marker.root ∈ (p i).2
      edge := (ExtremalContexts.normalPresentation
        ⟨False, {i | Marker.initial ∈ (p i.succ).2}⟩ (fun i => (p i).1)).edge
      direction_valid := (ExtremalContexts.normalPresentation
        ⟨False, {i | Marker.initial ∈ (p i.succ).2}⟩ (fun i => (p i).1)).direction_valid } }
  one_hole := (ExtremalContexts.normalContext
    ⟨False, {i | Marker.initial ∈ (p i.succ).2}⟩ (fun i => (p i).1)).one_hole

def normalize {A : RankedSet} {k : ℕ} (p : Pieces A k) : Data A k :=
  ⟨⟨Marker.initial ∈ (p 0).2 ∨ ∃ i, Marker.root ∈ (p i).2,
    {i | Marker.initial ∈ (p i.succ).2}⟩, fun i => (p i).1⟩

def canonical {A : RankedSet} {k : ℕ} (x : Data A k) : Pieces A k :=
  fun i => ⟨x.2 i, {m | match m with
    | .root => x.1.root
    | .initial => Fin.cases x.1.root (fun j => j ∈ x.1.loops) i}⟩

def Accepted {A : RankedSet} (L : Algebras.Language A) (E : SyntacticAlgebra L)
    {k : ℕ} (p : Pieces (Carrier (Accepting L)) k) (a : Carrier (Accepting L) k) : Prop :=
  AcceptingClass (Accepting L) (E.algebra.eval 0 (plug (context p) (atomic a)))

def IsExtremal {A : RankedSet} (L : Algebras.Language A) (E : SyntacticAlgebra L)
    {k : ℕ} (p : Pieces (Carrier (Accepting L)) k) (a : Carrier (Accepting L) k) : Prop :=
  Accepted L E p a ∧ ∀ q b,
    (∀ i, PieceBelow (Accepting L) (q i) (p i)) → ClassBelow (Accepting L) b a →
    Accepted L E q b → q = p ∧ b = a

def ExtremalElement {A : RankedSet} (L : Algebras.Language A) (E : SyntacticAlgebra L)
    {k : ℕ} (a : Carrier (Accepting L) k) : Prop := ∃ p, IsExtremal L E p a

axiom normalize_canonical {A : RankedSet} {k : ℕ} (x : Data A k) :
    normalize (canonical x) = x

axiom canonical_order {A : RankedSet} (F : ClosedProperty A) {k : ℕ}
    (x : Data (Carrier F) k) (p : Pieces (Carrier F) k) :
    (∀ i, PieceBelow F (canonical x i) (p i)) ↔
      FiniteExtremal.DataBelow F x (normalize p)

axiom acceptance_normalize {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (p : Pieces (Carrier (Accepting L)) k)
    (a : Carrier (Accepting L) k) :
    Accepted L E p a ↔ FiniteExtremal.Accepts (Accepting L) E.algebra a (normalize p)

axiom extremal_iff {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (p : Pieces (Carrier (Accepting L)) k)
    (a : Carrier (Accepting L) k) :
    IsExtremal L E p a ↔ canonical (normalize p) = p ∧
      ExtremalSituations.IsExtremal (Accepting L) E.algebra (normalize p, a)

axiom element_iff {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (a : Carrier (Accepting L) k) :
    ExtremalElement L E a ↔ ExtremalSituations.ExtremalElement (Accepting L) E.algebra a

axiom extremal_choice {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ} (p : Pieces (Carrier (Accepting L)) k)
    (a : Carrier (Accepting L) k) (ha : Accepted L E p a) :
    ∃ q b, IsExtremal L E q b ∧
      (∀ i, PieceBelow (Accepting L) (q i) (p i)) ∧ ClassBelow (Accepting L) b a

axiom replacement {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ}
    (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b, ExtremalElement L E b ∧ ClassBelow (Accepting L) b a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic b)))

axiom simultaneous {A B : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P q)) ↔
      ∃ r : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1,
        (∀ v, ExtremalElement L E (r v) ∧ ClassBelow (Accepting L) (r v) (q v)) ∧
        AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P r))

axiom normal_test {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ}
    (p q : Pieces (Carrier (Accepting L)) k) (a : Carrier (Accepting L) k)
    (ha : IsExtremal L E p a) :
    Accepted L E q a ↔ ∀ i, PieceBelow (Accepting L) (p i) (q i)

end Lax369799.ExtendedContexts
