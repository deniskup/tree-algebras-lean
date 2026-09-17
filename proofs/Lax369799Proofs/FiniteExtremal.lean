import Lax369799.FiniteExtremal
import Lax369799Proofs.FiniteNormalForms
import Lax369799Proofs.FiniteOuterMorphisms
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Preorder.Finite

namespace Lax369799Proofs.FiniteExtremal
open Lax369799.RankedSystems (RankedSet RankedMap)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteSyntacticAlgebra Lax369799.FiniteMorphisms
open Lax369799.ExtremalContexts (Boundary Data)
open Lax369799.FiniteNormalForms (normalContext)
open Lax369799.FiniteExtremal
open Lax369799Proofs.FiniteNormalForms (letterSubstitution)

/--
---
conclusion: Lax369799.FiniteExtremal.extremal_choice
---
Finite unary values, a Boolean root mark, and a finite set of loop
directions give a finite preorder. Choose a minimal accepting datum below
the supplied accepting datum.
-/
theorem extremal_choice {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F))
    (hfinite : Finite (Carrier F 1)) {k : ℕ} (a : Carrier F k) (x : Data (Carrier F) k)
    (hx : Accepts F E a x) :
    ∃ y : Data (Carrier F) k, DataBelow F y x ∧ Accepts F E a y ∧
      ∀ z : Data (Carrier F) k, DataBelow F z y → Accepts F E a z → DataBelow F y z := by
  classical
  let := hfinite
  let : Finite (Boundary k) := Finite.of_injective (fun B : Boundary k => (B.root, B.loops)) (by
    rintro ⟨r, l⟩ ⟨r', l'⟩ h
    obtain ⟨hr, hl⟩ := Prod.mk.inj h
    cases hr
    cases hl
    rfl)
  obtain ⟨refl, _, trans⟩ := FiniteContextualOrder.class_order F 1
  let : Preorder (Data (Carrier F) k) := {
    le := DataBelow F
    le_refl := fun x => ⟨id, Set.Subset.rfl, fun i => refl (x.2 i)⟩
    le_trans := fun x y z hxy hyz => ⟨hxy.1 ∘ hyz.1, hyz.2.1.trans hxy.2.1,
      fun i => trans _ _ _ (hxy.2.2 i) (hyz.2.2 i)⟩ }
  obtain ⟨y, hyx, hy, hmin⟩ := Finite.exists_le_minimal (p := Accepts F E a) hx
  exact ⟨y, hyx, hy, fun z hzy hz => hmin hz hzy⟩

private theorem relabel_normal {A B : RankedSet} (f : RankedMap A B) {k : ℕ}
    (D : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :
    relabel f (relabel (letterSubstitution a) (normalContext D m).system) =
      relabel (letterSubstitution (f k a)) (normalContext D (fun i => f 1 (m i))).system := by
  dsimp only [relabel, normalContext, ofSetSystem, Lax369799.ExtremalContexts.normalContext,
    Lax369799.ExtremalContexts.normalSystem, Lax369799.ExtremalContexts.normalPresentation]
  congr 1
  congr 1
  funext v
  cases v using Fin.cases <;> rfl

private def boundaryMap {A : RankedSet} {k : ℕ} (B D : Boundary k)
    (hr : D.root → B.root) (hl : D.loops ⊆ B.loops) (m : Fin (k + 1) → A 1) (a : A k) :
    Morphism (relabel (letterSubstitution a) (normalContext D m).system)
      (relabel (letterSubstitution a) (normalContext B m).system) where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => False.elim h
  root := fun v h => h.elim Or.inl (fun h => Or.inr ⟨h.1, hr h.2⟩)
  edge := by
    intro v d t h
    cases t with
    | inr i => exact Fin.elim0 i
    | inl w =>
      cases v using Fin.cases with
      | zero =>
        rcases h with ⟨i, hd, he⟩ | ⟨i, hi, hd, he⟩
        · exact Or.inl ⟨i, hd, he⟩
        · exact Or.inr ⟨i, hl hi, hd, he⟩
      | succ i => exact h

/--
---
conclusion: Lax369799.FiniteExtremal.data_monotone
---
First increase the unary labels using evaluation monotonicity. Then remove
boundary marks and loops using the reverse morphism comparison.
-/
theorem data_monotone {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Lax369799.FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Lax369799.FiniteAcceptance.Accepting L)) S) =
        quotientMap (Lax369799.FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (x y : Data (Carrier (Lax369799.FiniteAcceptance.Accepting L)) k)
    (h : DataBelow (Lax369799.FiniteAcceptance.Accepting L) x y)
    (a : Carrier (Lax369799.FiniteAcceptance.Accepting L) k) :
    ClassBelow (Lax369799.FiniteAcceptance.Accepting L) (value E a x) (value E a y) := by
  let F := Lax369799.FiniteAcceptance.Accepting L
  change ClassBelow F (E.eval 0 (plug (normalContext x.1 x.2) (atomic a)))
    (E.eval 0 (plug (normalContext y.1 y.2) (atomic a)))
  rw [E.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso (normalContext x.1 x.2) a),
    E.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso (normalContext y.1 y.2) a)]
  let Pairs : RankedSet := fun r => {p : Carrier F r × Carrier F r // ClassBelow F p.1 p.2}
  let fst : RankedMap Pairs (Carrier F) := fun _ p => p.val.1
  let snd : RankedMap Pairs (Carrier F) := fun _ p => p.val.2
  let m : Fin (k + 1) → Pairs 1 := fun i => ⟨(x.2 i, y.2 i), h.2.2 i⟩
  let b : Pairs k := ⟨(a, a), (FiniteContextualOrder.class_order F k).1 a⟩
  let P := relabel (letterSubstitution b) (normalContext x.1 m).system
  have hm := FiniteSyntacticAlgebra.evaluation_monotone F (FiniteAcceptance.accepting_isomorphic L) E hE P
    (fun v => fst _ (P.graph.label v).2) (fun v => snd _ (P.graph.label v).2)
    (fun v => (P.graph.label v).2.property)
  change ClassBelow F (E.eval 0 (relabel fst (relabel (letterSubstitution b) (normalContext x.1 m).system)))
    (E.eval 0 (relabel snd (relabel (letterSubstitution b) (normalContext x.1 m).system))) at hm
  rw [relabel_normal, relabel_normal] at hm
  have hb := FiniteOuterMorphisms.evaluation_morphism L E hE (boundaryMap x.1 y.1 h.1 h.2.1 y.2 a)
  exact (FiniteContextualOrder.class_order F 0).2.2 _ _ _ hm hb

/--
---
conclusion: Lax369799.FiniteExtremal.delta_deterministic
---
Evaluate the unary labels of the witness pattern first. Associativity
identifies this low-rank presentation with the value of its flattening.
-/
theorem delta_deterministic {A : RankedSet} (E : Algebra A) {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :
    Deterministic E (E.eval k (delta B m a)) := by
  refine ⟨relabel E.eval (deltaPattern B m a), ?_, E.associative k (deltaPattern B m a)⟩
  intro v
  refine Fin.cases (Nat.le_refl 1) (fun _ => Nat.le_refl 1) v

end Lax369799Proofs.FiniteExtremal
