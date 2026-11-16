import Lax369799.FiniteExtremal
import Lax369799.DeterministicElements

/-!
---
title: Extremal witnesses with separate rooted components
type: theorem
---
Each unary component has its own rooted copy of the incoming context piece.
There is no choice between different successors beneath that root.
-/
namespace Lax369799.SplitExtremal
open RankedSystems (RankedSet)
open FinitePresentations FiniteContextualOrder FiniteSyntacticAlgebra
open ExtremalContexts (Boundary Data)
open FiniteExtremal (IsExtremal Accepts value)

def component {A : RankedSet} {k : ℕ} (B : Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) (i : Fin k) : FiniteSystem A 1 where
  size := k + 2
  graph := {
    label := Fin.cases ⟨k, a⟩ (fun j => ⟨1, m j⟩)
    initial := {0}
    root := fun v => v = (0 : Fin (k + 1)).succ ∨ (v = 0 ∧ B.root)
    edge := fun v d t => Fin.cases
      ((∃ j : Fin k, d = j.val ∧ t = .inl j.succ.succ) ∨
       (∃ j : Fin k, j ∈ B.loops ∧ d = j.val ∧ t = .inl 0) ∨
       (d = i.val ∧ t = .inr 0))
      (fun _ => d = 0 ∧ t = .inl 0) v
    direction_valid := by
      intro v d t
      refine Fin.cases ?_ (fun j => ?_) v
      · rintro (⟨j, rfl, _⟩ | ⟨j, _, rfl, _⟩ | ⟨rfl, _⟩)
        · exact j.isLt
        · exact j.isLt
        · exact i.isLt
      · rintro ⟨rfl, _⟩; exact Nat.zero_lt_one }

def pattern {A : RankedSet} {k : ℕ} (B : Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) : FiniteSystem (FiniteSystem A) k where
  size := k
  graph := {
    label := fun i => ⟨1, component B m a i⟩
    initial := Set.univ
    root := ∅
    edge := fun i d t => d = 0 ∧ t = .inr i
    direction_valid := by rintro i d t ⟨rfl, _⟩; exact Nat.zero_lt_one }

noncomputable def delta {A : RankedSet} {k : ℕ} (B : Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) : FiniteSystem A k := flatten (pattern B m a)

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
    {k : ℕ} (hk : 1 ≤ k) (x : Data (Carrier (FiniteAcceptance.Accepting L)) k)
    (a : Carrier (FiniteAcceptance.Accepting L) k)
    (hx : IsExtremal (FiniteAcceptance.Accepting L) E a x) :
    ClassBelow (FiniteAcceptance.Accepting L) (E.eval k (delta x.1 x.2 a)) a

axiom delta_in_context {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (FiniteAcceptance.Accepting L)) S) =
        quotientMap (FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (x : Data (Carrier (FiniteAcceptance.Accepting L)) k)
    (a : Carrier (FiniteAcceptance.Accepting L) k) :
    ClassBelow (FiniteAcceptance.Accepting L) (value E a x)
      (value E (E.eval k (delta x.1 x.2 a)) x)

axiom parallel_value {A : RankedSet} (E : Algebra A) {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :
    E.eval k (ofSetSystem (DeterministicElements.parallel (fun i => E.eval 1 (component B m a i)))) =
      E.eval k (delta B m a)

/-- The witness accepts precisely the normal data above its extremal datum. -/
axiom acceptance_iff_dataBelow {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (FiniteAcceptance.Accepting L)) S) =
        quotientMap (FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (hk : 1 ≤ k) (x y : Data (Carrier (FiniteAcceptance.Accepting L)) k)
    (a : Carrier (FiniteAcceptance.Accepting L) k)
    (hx : IsExtremal (FiniteAcceptance.Accepting L) E a x) :
    Accepts (FiniteAcceptance.Accepting L) E (E.eval k (delta x.1 x.2 a)) y ↔
      FiniteExtremal.DataBelow (FiniteAcceptance.Accepting L) x y

/-- Meet of normal context data: union the boundary marks and sum the pieces. -/
def meetData {A : RankedSet} (E : Algebra A) {k : ℕ} (y z : Data A k) : Data A k :=
  (⟨y.1.root ∨ z.1.root, y.1.loops ∪ z.1.loops⟩, fun i => sumValue E (y.2 i) (z.2 i))

axiom accepting_meetData {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (FiniteAcceptance.Accepting L)) S) =
        quotientMap (FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (hk : 1 ≤ k) (x y z : Data (Carrier (FiniteAcceptance.Accepting L)) k)
    (a : Carrier (FiniteAcceptance.Accepting L) k)
    (hx : IsExtremal (FiniteAcceptance.Accepting L) E a x) :
    Accepts (FiniteAcceptance.Accepting L) E (E.eval k (delta x.1 x.2 a)) (meetData E y z) ↔
      Accepts (FiniteAcceptance.Accepting L) E (E.eval k (delta x.1 x.2 a)) y ∧
      Accepts (FiniteAcceptance.Accepting L) E (E.eval k (delta x.1 x.2 a)) z

end Lax369799.SplitExtremal
