import Lax369799.ExtremalSituations
import Lax369799Proofs.ExtremalUnaryTypes
import Lax369799Proofs.FiniteLocalReplacement
import Lax369799Proofs.ClosedExtremal

namespace Lax369799Proofs.ExtremalSituations
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra
open FiniteAcceptance ExpandedSyntacticAlgebra
open ExtremalContexts (Boundary Data)
open Lax369799.ExtremalSituations

private abbrev dataOrder {A : RankedSet} (F : ClosedProperty A) (k : ℕ) :
    PartialOrder (Data (Carrier F) k) where
  le := FiniteExtremal.DataBelow F
  le_refl := fun x => ⟨id, Set.Subset.rfl, fun i => (FiniteContextualOrder.class_order F 1).1 (x.2 i)⟩
  le_trans := fun x y z hxy hyz => ⟨hxy.1 ∘ hyz.1, hyz.2.1.trans hxy.2.1,
    fun i => (FiniteContextualOrder.class_order F 1).2.2 _ _ _ (hxy.2.2 i) (hyz.2.2 i)⟩
  le_antisymm := by
    rintro ⟨⟨r, s⟩, m⟩ ⟨⟨r', s'⟩, m'⟩ h h'
    have hr : r = r' := propext ⟨h'.1, h.1⟩
    have hs : s = s' := Set.Subset.antisymm h'.2.1 h.2.1
    have hm : m = m' := funext (fun i =>
      (FiniteContextualOrder.class_order F 1).2.1 _ _ (h.2.2 i) (h'.2.2 i))
    cases hr
    cases hs
    cases hm
    rfl

private abbrev situationOrder {A : RankedSet} (F : ClosedProperty A) (k : ℕ) :
    PartialOrder (Situation F k) where
  le := Below F
  le_refl := fun x => ⟨(dataOrder F k).le_refl x.1, (FiniteContextualOrder.class_order F k).1 x.2⟩
  le_trans := fun _ _ _ h h' => ⟨(dataOrder F k).le_trans _ _ _ h.1 h'.1,
    (FiniteContextualOrder.class_order F k).2.2 _ _ _ h.2 h'.2⟩
  le_antisymm := fun _ _ h h' => Prod.ext ((dataOrder F k).le_antisymm _ _ h.1 h'.1)
    ((FiniteContextualOrder.class_order F k).2.1 _ _ h.2 h'.2)

/--
---
conclusion: Lax369799.ExtremalSituations.choice
---
Minimize in the finite product of boundary data, unary values, and the
sort of the hole. Antisymmetry turns mutual comparison into equality.
-/
theorem choice {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F))
    (hfinite : ∀ n, Finite (Carrier F n)) {k : ℕ} (x : Situation F k)
    (hx : Accepted F E x) :
    ∃ y, Below F y x ∧ IsExtremal F E y := by
  classical
  let : ∀ n, Finite (Carrier F n) := hfinite
  let : Finite (Boundary k) := Finite.of_injective
    (fun B : Boundary k => (B.root, B.loops)) (by
      rintro ⟨r, s⟩ ⟨r', s'⟩ h
      obtain ⟨hr, hs⟩ := Prod.mk.inj h
      cases hr
      cases hs
      rfl)
  let := situationOrder F k
  obtain ⟨y, hyx, hy, hmin⟩ := Finite.exists_le_minimal (p := Accepted F E) hx
  exact ⟨y, hyx, hy, fun z hzy hz => le_antisymm hzy (hmin hz hzy)⟩

/--
---
conclusion: Lax369799.ExtremalSituations.replacement
---
Normalize and plant the context, minimize the entire accepted situation,
and increase its context data back to the supplied ones.
-/
theorem replacement {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ}
    (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b, ExtremalElement (Accepting L) E.algebra b ∧ ClassBelow (Accepting L) b a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic b))) := by
  let F := Accepting L
  have hc := fun n (S T : FiniteSystem (Carrier F) n) f hf =>
    FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates (S := S) (T := T) f hf
  let x : Data (Carrier F) k :=
    ⟨FiniteNormalForms.plantedBoundary C, FiniteNormalForms.pieceValue E.algebra C⟩
  have hx : Accepted F E.algebra (x, a) := by
    change AcceptingClass F (E.algebra.eval 0 (plug
      (FiniteNormalForms.normalContext x.1 x.2) (atomic a)))
    rw [FiniteNormalForms.algebraic_decomposition E.algebra hc C a]
    exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).mpr ha
  obtain ⟨⟨y, b⟩, hy, hb⟩ := choice F E.algebra
    (BoundedProfileRefinement.finite_carrier_recognizable L hL hrec) (x, a) hx
  refine ⟨b, ⟨y, hb⟩, hy.2, ?_⟩
  have hb' := (FiniteSyntacticAlgebra.accepting_classes F (FiniteAcceptance.accepting_isomorphic L)).2
    _ _ hb.1 (FiniteExtremal.data_monotone L E.algebra E.evaluates y x hy.1 b)
  change AcceptingClass F (E.algebra.eval 0 (plug
    (FiniteNormalForms.normalContext x.1 x.2) (atomic b))) at hb'
  rw [FiniteNormalForms.algebraic_decomposition E.algebra hc C b] at hb'
  exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).mp hb'

/--
---
conclusion: Lax369799.ExtremalSituations.simultaneous
---
Iterate extremal replacement through the finite vertex set. For the
converse, monotonicity and upward closure restore the original labels.
-/
theorem simultaneous {A B : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P q)) ↔
      ∃ r : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1,
        (∀ v, ExtremalElement (Accepting L) E.algebra (r v) ∧
          ClassBelow (Accepting L) (r v) (q v)) ∧
        AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P r)) := by
  constructor
  · intro hq
    exact FiniteLocalReplacement.simultaneous E.algebra
      {a | AcceptingClass (Accepting L) a}
      (fun _ a b => ExtremalElement (Accepting L) E.algebra b ∧ ClassBelow (Accepting L) b a)
      (fun _ C a ha => by
        obtain ⟨b, hb, hba, hacc⟩ := replacement L hL hrec E C a ha
        exact ⟨b, ⟨hb, hba⟩, hacc⟩) P q hq
  · rintro ⟨r, hr, hacc⟩
    exact (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
      (FiniteAcceptance.accepting_isomorphic L)).2 _ _ hacc
      (FiniteSyntacticAlgebra.evaluation_monotone (Accepting L)
        (FiniteAcceptance.accepting_isomorphic L) E.algebra E.evaluates P r q (fun v => (hr v).2))

/--
---
conclusion: Lax369799.ExtremalSituations.fixed_element
---
Keep the hole element fixed in the minimality test.
-/
theorem fixed_element {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F))
    {k : ℕ} (x : Data (Carrier F) k) (a : Carrier F k)
    (hx : IsExtremal F E (x, a)) : FiniteExtremal.IsExtremal F E a x := by
  refine ⟨hx.1, fun y hy hacc => ?_⟩
  have he := hx.2 (y, a) ⟨hy, (FiniteContextualOrder.class_order F k).1 a⟩ hacc
  have hdata : y = x := congrArg Prod.fst he
  subst y
  exact (dataOrder F k).le_refl x

/--
---
conclusion: Lax369799.ExtremalSituations.split_value
---
The split witness decreases the hole element and remains accepted with
the same data. Minimality of the whole situation identifies its value.
-/
theorem split_value {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k)
    (x : Data (Carrier (Accepting L)) k) (a : Carrier (Accepting L) k)
    (hx : IsExtremal (Accepting L) E.algebra (x, a)) :
    E.algebra.eval k (Lax369799.SplitExtremal.delta x.1 x.2 a) = a := by
  have hfixed := fixed_element (Accepting L) E.algebra x a hx
  have hb := SplitExtremal.delta_below L E.algebra E.evaluates hk x a hfixed
  have ha := (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)).2 _ _ hx.1
    (SplitExtremal.delta_in_context L E.algebra E.evaluates x a)
  let b := E.algebra.eval k (Lax369799.SplitExtremal.delta x.1 x.2 a)
  have hbelow : Below (Accepting L) (x, b) (x, a) :=
    ⟨(dataOrder (Accepting L) k).le_refl x, hb⟩
  have he : (x, b) = (x, a) := hx.2 (x, b) hbelow ha
  exact congrArg Prod.snd he

/--
---
conclusion: Lax369799.ExtremalSituations.normal_test
---
Use the closed witness at rank zero and the split witness at positive
rank. Their equalities give the exact normal-context test in every rank.
-/
theorem normal_test {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ}
    (x : Data (Carrier (Accepting L)) k) (a : Carrier (Accepting L) k)
    (hx : IsExtremal (Accepting L) E.algebra (x, a))
    (y : Data (Carrier (Accepting L)) k) :
    FiniteExtremal.Accepts (Accepting L) E.algebra a y ↔
      FiniteExtremal.DataBelow (Accepting L) x y := by
  cases k with
  | zero => exact ClosedExtremal.normal_test L E x a hx y
  | succ k =>
    have hk : 1 ≤ k + 1 := by omega
    have h := SplitExtremal.acceptance_iff_dataBelow L E.algebra E.evaluates hk x y a
      (fixed_element (Accepting L) E.algebra x a hx)
    rwa [split_value L E hk x a hx] at h

/--
---
conclusion: Lax369799.ExtremalSituations.unary_selected
---
A unary extremal element equals its own selected split witness.
-/
theorem unary_selected {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : ExtremalElement (Accepting L) E.algebra b) :
    Lax369799.ExtremalUnaryTypes.Selected L E b := by
  obtain ⟨x, hx⟩ := hb
  exact ⟨b, x, fixed_element (Accepting L) E.algebra x b hx,
    (split_value L E (by omega) x b hx).symm⟩

/--
---
conclusion: Lax369799.ExtremalSituations.parallel_decomposition
---
Evaluate the unary components of the split witness and use its equality
with the extremal element.
-/
theorem parallel_decomposition {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k) (a : Carrier (Accepting L) k)
    (ha : ExtremalElement (Accepting L) E.algebra a) :
    ∃ b : Fin k → Carrier (Accepting L) 1,
      E.algebra.eval k (ofSetSystem (DeterministicElements.parallel b)) = a := by
  obtain ⟨x, hx⟩ := ha
  exact ⟨fun i => E.algebra.eval 1 (Lax369799.SplitExtremal.component x.1 x.2 a i),
    (SplitExtremal.parallel_value E.algebra x.1 x.2 a).trans (split_value L E hk x a hx)⟩

end Lax369799Proofs.ExtremalSituations
