import Lax369799Proofs.FiniteExtremal
import Lax369799Proofs.FiniteEvaluation

namespace Lax369799Proofs.FiniteDeltaContext
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteSyntacticAlgebra
open Lax369799.ExtremalContexts (Boundary Data)
open Lax369799.FiniteNormalForms (normalContext)
open Lax369799.FiniteExtremal Lax369799Proofs.Pullbacks
open Lax369799Proofs.FiniteNormalForms (letterSubstitution)

private def normal {A : RankedSet} {k : ℕ} (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :=
  relabel (letterSubstitution a) (normalContext B m).system

private abbrev RawVertex {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :=
  (v : (deltaPattern B m a).Vertex) × (Inner (deltaPattern B m a).graph v).Vertex

private def rawPosition {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) : RawVertex B m a → Fin (k + 2) :=
  fun v => Fin.cases (fun _ => (0 : Fin (k + 1)).succ)
    (fun _ u => Fin.cases 0 (fun j => j.succ.succ) u) v.1 v.2

private theorem raw_label {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) (v : RawVertex B m a) :
    (normal B m a).graph.label (rawPosition B m a v) =
      (flattenPresentation (deltaPattern B m a).graph).label v := by
  rcases v with ⟨q, u⟩
  cases q using Fin.cases with
  | zero => rfl
  | succ i => cases u using Fin.cases <;> rfl

private theorem raw_initial {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) (v : RawVertex B m a)
    (h : (flattenPresentation (deltaPattern B m a).graph).initial v) :
    rawPosition B m a v = 0 := by
  rcases v with ⟨q, u⟩
  cases q using Fin.cases with
  | zero => exact False.elim (h.1 rfl)
  | succ i =>
    have hu : u = (0 : Fin (k + 1)) := h.2
    subst u
    rfl

private theorem raw_root {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) (v : RawVertex B m a)
    (h : (flattenPresentation (deltaPattern B m a).graph).root v) :
    (normal B m a).graph.root (rawPosition B m a v) := by
  rcases v with ⟨q, u⟩
  cases q using Fin.cases with
  | zero => exact Or.inl rfl
  | succ i =>
    rcases h with h | ⟨h, hu⟩
    · exact False.elim h
    · have hu : u = (0 : Fin (k + 1)) := hu
      subst u
      rcases h with hi | h
      · exact False.elim (Fin.succ_ne_zero i hi)
      · exact Or.inr ⟨rfl, h⟩

private theorem raw_transition {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k)
    (v w : RawVertex B m a) (d : ℕ)
    (h : (flattenPresentation (deltaPattern B m a).graph).edge v d (.inl w)) :
    (normal B m a).graph.edge (rawPosition B m a v) d (.inl (rawPosition B m a w)) := by
  rcases v with ⟨q, u⟩
  cases q using Fin.cases with
  | zero =>
    rcases h with ⟨u', ⟨i, _, he⟩, _⟩ | ⟨i, ⟨j, hd, he⟩, ht⟩
    · cases he
    · have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      have hij : i = j := Sum.inr.inj he
      subst j
      subst i
      subst d
      rcases ht with ⟨⟨q', u'⟩, ⟨_, l, he⟩, hu, hw⟩ | ⟨l, _, he⟩
      · have hq : q' = l.succ := Sum.inl.inj he
        subst q'
        have hu : u' = (0 : Fin (k + 1)) := hu
        subst u'
        have hw := Sum.inl.inj hw
        subst w
        exact ⟨rfl, rfl⟩
      · cases he
  | succ i =>
    rcases h with ⟨u', hu, hw⟩ | ⟨j, _, ht⟩
    · have hw := Sum.inl.inj hw
      subst w
      cases u using Fin.cases with
      | zero =>
        rcases hu with ⟨j, hd, he⟩ | ⟨j, hj, hd, he⟩ | ⟨_, he⟩
        · have he := Sum.inl.inj he
          subst u'
          subst d
          exact Or.inl ⟨j, rfl, rfl⟩
        · have he := Sum.inl.inj he
          subst u'
          subst d
          exact Or.inr ⟨j, hj, rfl, rfl⟩
        · cases he
      | succ j =>
        obtain ⟨hd, he⟩ := hu
        have he := Sum.inl.inj he
        subst u'
        subst d
        exact ⟨rfl, rfl⟩
    · rcases ht with ⟨w', ⟨_, he⟩, _, _⟩ | ⟨l, _, he⟩ <;> cases he

private theorem raw_exit {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k)
    (v : RawVertex B m a) (d : ℕ) (j : Fin k)
    (h : (flattenPresentation (deltaPattern B m a).graph).edge v d (.inr j)) :
    rawPosition B m a v = 0 ∧ d = j.val := by
  rcases v with ⟨q, u⟩
  rcases h with ⟨_, _, he⟩ | ⟨i, hi, ht⟩
  · cases he
  · rcases ht with ⟨_, _, _, he⟩ | ⟨l, hl, he⟩
    · cases he
    · have he : j = l := Sum.inr.inj he
      subst l
      cases q using Fin.cases with
      | zero =>
        obtain ⟨_, l, he⟩ := hl
        cases he
      | succ l =>
        have hj : j = l := Sum.inr.inj hl.2
        subst l
        cases u using Fin.cases with
        | zero =>
          rcases hi with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨hd, _⟩
          · cases he
          · cases he
          · exact ⟨rfl, hd⟩
        | succ l => cases hi.2

private noncomputable def argumentPattern {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) : FiniteSystem (FiniteSystem A) 0 :=
  relabel (substitution (delta B m a)) (normalContext B m).system

private abbrev ContextVertex {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :=
  (v : (argumentPattern B m a).Vertex) × (Inner (argumentPattern B m a).graph v).Vertex

private noncomputable def contextPosition {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) : ContextVertex B m a → Fin (k + 2) :=
  fun v => Fin.cases
    (fun u => rawPosition B m a ((Fintype.equivFin (RawVertex B m a)).symm u))
    (fun i _ => i.succ) v.1 v.2

private theorem context_initial {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) (v : ContextVertex B m a)
    (h : v.2 ∈ (Inner (argumentPattern B m a).graph v.1).graph.initial) :
    contextPosition B m a v = v.1 := by
  rcases v with ⟨q, u⟩
  cases q using Fin.cases with
  | zero => exact raw_initial B m a _ h
  | succ i => rfl

private theorem context_exit {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) (v : ContextVertex B m a)
    (d : ℕ) (i : Fin ((argumentPattern B m a).graph.label v.1).1)
    (h : (Inner (argumentPattern B m a).graph v.1).graph.edge v.2 d (.inr i)) :
    contextPosition B m a v = v.1 ∧ d = i.val := by
  rcases v with ⟨q, u⟩
  cases q using Fin.cases with
  | zero => exact raw_exit B m a _ d i h
  | succ j =>
    obtain ⟨l, hd, he⟩ := h
    have he : i = l := Sum.inr.inj he
    subst l
    exact ⟨rfl, hd⟩

private noncomputable def contextMap {A : RankedSet} {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :
    Map (flattenPresentation (argumentPattern B m a).graph) (normal B m a).graph where
  toFun := contextPosition B m a
  label := by
    rintro ⟨q, u⟩
    cases q using Fin.cases with
    | zero => exact raw_label B m a _
    | succ i => rfl
  initial := fun _ h => False.elim h.1
  root := by
    intro v h
    rcases h with h | ⟨h, hi⟩
    · rcases v with ⟨q, u⟩
      cases q using Fin.cases with
      | zero => exact raw_root B m a _ h
      | succ i => exact False.elim h
    · rw [context_initial B m a v hi]
      exact h
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · rcases v with ⟨q, u⟩
      cases q using Fin.cases with
      | zero => exact raw_transition B m a _ _ d hw
      | succ i => obtain ⟨j, _, he⟩ := hw; cases he
    · have hv := context_exit B m a v d i hi
      rcases ht with ⟨w, hw, hi, rfl⟩ | ⟨j, _, _⟩
      · change (normal B m a).graph.edge (contextPosition B m a v) d (.inl (contextPosition B m a w))
        rw [hv.1, hv.2, context_initial B m a w hi]
        exact hw
      · exact Fin.elim0 j

/--
---
conclusion: Lax369799.FiniteExtremal.delta_in_context
---
Project each copied argument and unary vertex to its original position.
Root marks and self-loops are preserved. Reverse the resulting morphism
comparison and use context evaluation.
-/
theorem delta_in_context {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Lax369799.FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Lax369799.FiniteAcceptance.Accepting L)) S) =
        quotientMap (Lax369799.FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (x : Data (Carrier (Lax369799.FiniteAcceptance.Accepting L)) k)
    (a : Carrier (Lax369799.FiniteAcceptance.Accepting L) k) :
    ClassBelow (Lax369799.FiniteAcceptance.Accepting L) (value E a x)
      (value E (E.eval k (delta x.1 x.2 a)) x) := by
  have hm := FiniteOuterMorphisms.evaluation_morphism L E hE
    (FiniteMorphisms.fromEnumeration (contextMap x.1 x.2 a))
  change ClassBelow _ (E.eval 0 (normal x.1 x.2 a))
    (E.eval 0 (plug (normalContext x.1 x.2) (delta x.1 x.2 a))) at hm
  rw [FiniteEvaluation.context_evaluation E (normalContext x.1 x.2) (delta x.1 x.2 a)] at hm
  have he := E.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso (normalContext x.1 x.2) a)
  change value E a x = E.eval 0 (normal x.1 x.2 a) at he
  rw [← he] at hm
  exact hm

end Lax369799Proofs.FiniteDeltaContext
