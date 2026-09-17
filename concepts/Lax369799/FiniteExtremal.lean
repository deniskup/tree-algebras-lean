import Lax369799.FiniteNormalForms

/-!
---
title: Extremal unary data for finite presentations
type: theorem
---
Unary values, the planted hole mark, and its loop directions form a finite
space when the unary quotient sort is finite. Choose an accepting datum
minimal below a given datum, with boundary inclusions reversed.
-/
namespace Lax369799.FiniteExtremal
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra
open ExtremalContexts (Data)
open FiniteNormalForms (normalContext)

def DataBelow {A : RankedSet} (F : ClosedProperty A) {k : ℕ}
    (x y : Data (Carrier F) k) : Prop :=
  (y.1.root → x.1.root) ∧ y.1.loops ⊆ x.1.loops ∧ ∀ i, ClassBelow F (x.2 i) (y.2 i)

noncomputable def value {A : RankedSet} {F : ClosedProperty A} (E : Algebra (Carrier F)) {k : ℕ}
    (a : Carrier F k) (x : Data (Carrier F) k) : Carrier F 0 :=
  E.eval 0 (plug (normalContext x.1 x.2) (atomic a))

def Accepts {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F)) {k : ℕ}
    (a : Carrier F k) (x : Data (Carrier F) k) : Prop := AcceptingClass F (value E a x)

def IsExtremal {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F)) {k : ℕ}
    (a : Carrier F k) (x : Data (Carrier F) k) : Prop :=
  Accepts F E a x ∧ ∀ y, DataBelow F y x → Accepts F E a y → DataBelow F x y

axiom extremal_choice {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F))
    (hfinite : Finite (Carrier F 1)) {k : ℕ} (a : Carrier F k) (x : Data (Carrier F) k)
    (hx : Accepts F E a x) :
    ∃ y : Data (Carrier F) k, DataBelow F y x ∧ Accepts F E a y ∧
      ∀ z : Data (Carrier F) k, DataBelow F z y → Accepts F E a z → DataBelow F y z

axiom data_monotone {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (FiniteAcceptance.Accepting L)) S) =
        quotientMap (FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (x y : Data (Carrier (FiniteAcceptance.Accepting L)) k)
    (h : DataBelow (FiniteAcceptance.Accepting L) x y) (a : Carrier (FiniteAcceptance.Accepting L) k) :
    ClassBelow (FiniteAcceptance.Accepting L) (value E a x) (value E a y)

def Deterministic {A : RankedSet} (E : Algebra A) {n : ℕ} (a : A n) : Prop :=
  ∃ S : FiniteSystem A n, (∀ v, (S.graph.label v).1 ≤ 1) ∧ E.eval n S = a

def deltaPattern {A : RankedSet} {k : ℕ} (B : ExtremalContexts.Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) : FiniteSystem (FiniteSystem A) k :=
  relabel (fun _ => ofSetSystem) (ofSetSystem (ExtremalContexts.deltaPattern B m a))

noncomputable def delta {A : RankedSet} {k : ℕ} (B : ExtremalContexts.Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) : FiniteSystem A k := flatten (deltaPattern B m a)

axiom delta_deterministic {A : RankedSet} (E : Algebra A) {k : ℕ}
    (B : ExtremalContexts.Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :
    Deterministic E (E.eval k (delta B m a))

axiom delta_in_context {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (FiniteAcceptance.Accepting L)) S) =
        quotientMap (FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (x : Data (Carrier (FiniteAcceptance.Accepting L)) k)
    (a : Carrier (FiniteAcceptance.Accepting L) k) :
    ClassBelow (FiniteAcceptance.Accepting L) (value E a x)
      (value E (E.eval k (delta x.1 x.2 a)) x)

axiom delta_boundary_comparison {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (FiniteAcceptance.Accepting L)) S) =
        quotientMap (FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (hk : 1 ≤ k) (x y : Data (Carrier (FiniteAcceptance.Accepting L)) k)
    (a : Carrier (FiniteAcceptance.Accepting L) k)
    (hx : IsExtremal (FiniteAcceptance.Accepting L) E a x)
    (hy : Accepts (FiniteAcceptance.Accepting L) E (E.eval k (delta x.1 x.2 a)) y) :
    (y.1.root → x.1.root) ∧ y.1.loops ⊆ x.1.loops

axiom delta_piece_comparison {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (FiniteAcceptance.Accepting L)) S) =
        quotientMap (FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (hk : 1 ≤ k) (x y : Data (Carrier (FiniteAcceptance.Accepting L)) k)
    (a : Carrier (FiniteAcceptance.Accepting L) k)
    (hx : IsExtremal (FiniteAcceptance.Accepting L) E a x)
    (hy : Accepts (FiniteAcceptance.Accepting L) E (E.eval k (delta x.1 x.2 a)) y) :
    ∀ j, ClassBelow (FiniteAcceptance.Accepting L) (x.2 j) (y.2 j)

axiom delta_below {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (FiniteAcceptance.Accepting L)) S) =
        quotientMap (FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (hk : 2 ≤ k) (x : Data (Carrier (FiniteAcceptance.Accepting L)) k)
    (a : Carrier (FiniteAcceptance.Accepting L) k)
    (hx : IsExtremal (FiniteAcceptance.Accepting L) E a x) :
    ClassBelow (FiniteAcceptance.Accepting L) (E.eval k (delta x.1 x.2 a)) a

end Lax369799.FiniteExtremal
