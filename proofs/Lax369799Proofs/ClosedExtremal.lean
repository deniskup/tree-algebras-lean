import Lax369799.ClosedExtremal
import Lax369799Proofs.ExtremalUnaryTypes

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.ClosedExtremal
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra
open FiniteAcceptance ExpandedSyntacticAlgebra
open ExtremalContexts (Boundary Data)
open Lax369799.FiniteNormalForms (normalContext)
open Lax369799.FiniteExtremal (Accepts value DataBelow)
open Pullbacks (Map)
open FiniteNormalForms (letterSubstitution)

open Lax369799.ClosedExtremal

private noncomputable def testPattern {A : RankedSet} (x y : Data A 0) (a : A 0) :=
  relabel (substitution (witness x a)) (normalContext y.1 y.2).system

private noncomputable def rootMap {A : RankedSet} (x y : Data A 0) (a : A 0) (r : Prop)
    (hr : r → x.1.root ∨ y.1.root) :
    Map (relabel (letterSubstitution a) (normalContext ⟨r, ∅⟩ x.2).system).graph
      (flattenPresentation (testPattern x y a).graph) where
  toFun := fun v => ⟨(0 : Fin 2), v⟩
  label := by intro v; fin_cases v <;> rfl
  initial := fun _ h => h.elim
  root := by
    intro v hv
    rcases hv with rfl | ⟨rfl, h⟩
    · exact Or.inl (Or.inl rfl)
    · rcases hr h with h | h
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr ⟨Or.inr ⟨rfl, h⟩, rfl⟩
  edge := by
    intro v d t h
    cases v using Fin.cases with
    | zero =>
      rcases h with ⟨j, _⟩ | ⟨j, _⟩ <;> exact Fin.elim0 j
    | succ i =>
      fin_cases i
      rcases h with ⟨rfl, rfl⟩
      exact Or.inl ⟨(0 : Fin 2), ⟨rfl, rfl, rfl⟩, rfl⟩

private theorem root_bound {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x y : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0) (r : Prop) (hr : r → x.1.root ∨ y.1.root) :
    ClassBelow (Accepting L) (value E.algebra (E.algebra.eval 0 (witness x a)) y)
      (value E.algebra a (⟨r, ∅⟩, x.2)) := by
  have hm := FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates
    (FiniteMorphisms.toEnumeration (rootMap x y a r hr))
  change ClassBelow _ (E.algebra.eval 0 (plug (normalContext y.1 y.2) (witness x a)))
    (E.algebra.eval 0 (relabel (letterSubstitution a) (normalContext ⟨r, ∅⟩ x.2).system)) at hm
  rw [FiniteEvaluation.context_evaluation E.algebra] at hm
  rw [← E.algebra.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso _ a)] at hm
  exact hm

private def pairSystem {A : RankedSet} (b c : A 1) : FiniteSystem A 1 where
  size := 2
  graph := {
    label := fun v => ⟨1, if v = 0 then b else c⟩
    initial := Set.univ
    root := ∅
    edge := fun _ d t => d = 0 ∧ t = .inr 0
    direction_valid := by rintro v d t ⟨rfl, _⟩; exact Nat.zero_lt_one }

private theorem eval_pair {A : RankedSet} (E : Algebra A) (b c : A 1) :
    E.eval 1 (pairSystem b c) = sumValue E b c := by
  apply E.isomorphic
  refine ⟨{ vertex := Equiv.refl _
            label := ?_
            initial := fun _ => Iff.rfl
            root := fun _ => Iff.rfl
            edge := ?_ }⟩
  · intro v; fin_cases v <;> rfl
  · intro v d t
    change (∃ i : Fin 1, d = i.val ∧ Sum.map (Equiv.refl _) id t = .inr i) ↔
      (d = 0 ∧ t = .inr 0)
    constructor
    · rintro ⟨i, hi, he⟩
      fin_cases i
      cases t <;> simp_all
    · rintro ⟨rfl, rfl⟩
      exact ⟨0, rfl, rfl⟩

private noncomputable def doublePattern {A : RankedSet} (x y : Data A 0) (a : A 0) :=
  relabel (letterSubstitution (atomic a))
    (normalContext x.1 (fun i => pairSystem (x.2 i) (y.2 i))).system

private theorem eval_double {A : RankedSet} {F : ClosedProperty A} (E : Algebra (Carrier F))
    (x y : Data (Carrier F) 0) (a : Carrier F 0) :
    E.eval 0 (flatten (doublePattern x y a)) =
      value E a (x.1, fun i => sumValue E (x.2 i) (y.2 i)) := by
  have he : relabel E.eval (doublePattern x y a) =
      relabel (letterSubstitution a)
        (normalContext x.1 (fun i => sumValue E (x.2 i) (y.2 i))).system := by
    dsimp only [doublePattern, relabel, normalContext, ofSetSystem,
      Lax369799.ExtremalContexts.normalContext, Lax369799.ExtremalContexts.normalSystem,
      Lax369799.ExtremalContexts.normalPresentation]
    congr 1
    congr 1
    funext v
    cases v using Fin.cases with
    | zero => exact congrArg (Sigma.mk 0) (E.unit 0 a)
    | succ i => exact congrArg (Sigma.mk 1) (eval_pair E _ _)
  rw [← E.associative, he]
  exact (E.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso _ a)).symm

private noncomputable def doublePosition {A : RankedSet} (x y : Data A 0) (a : A 0) :
    ((v : (doublePattern x y a).Vertex) × (Inner (doublePattern x y a).graph v).Vertex) →
    ((v : (testPattern x y a).Vertex) × (Inner (testPattern x y a).graph v).Vertex) :=
  fun v => Fin.cases (fun _ => ⟨(0 : Fin 2), (0 : Fin 2)⟩)
    (fun _ u => if u = (0 : Fin 2) then ⟨(0 : Fin 2), (1 : Fin 2)⟩
      else ⟨(1 : Fin 2), (0 : Fin 1)⟩) v.1 v.2

private noncomputable def doubleMap {A : RankedSet} (x y : Data A 0) (a : A 0) :
    Map (flattenPresentation (doublePattern x y a).graph)
      (flattenPresentation (testPattern x y a).graph) where
  toFun := doublePosition x y a
  label := by
    rintro ⟨v, u⟩
    fin_cases v <;> fin_cases u <;> rfl
  initial := fun _ h => h.1.elim
  root := by
    rintro ⟨v, u⟩ h
    fin_cases v
    · fin_cases u
      rcases h with h | ⟨h, _⟩
      · exact h.elim
      · rcases h with h | ⟨_, h⟩
        · exact False.elim (by cases h)
        · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · fin_cases u
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨Or.inl rfl, trivial⟩
  edge := by
    rintro ⟨v, u⟩ d t h
    rcases h with ⟨w, hw, _⟩ | ⟨e, he, h⟩
    · fin_cases v
      · obtain ⟨i, _, _⟩ := hw; exact Fin.elim0 i
      · obtain ⟨_, hh⟩ := hw; cases hh
    · fin_cases v
      · exact Fin.elim0 e
      · fin_cases e
        obtain ⟨rfl, _⟩ := he
        rcases h with ⟨⟨w, z⟩, hw, hz, rfl⟩ | ⟨j, _⟩
        · have hw' : w = (0 : Fin 2) := Sum.inl.inj hw.2
          subst w
          fin_cases z
          fin_cases u
          · exact Or.inl ⟨(0 : Fin 2), ⟨rfl, rfl, rfl⟩, rfl⟩
          · exact Or.inr ⟨(0 : Fin 1), ⟨(0 : Fin 1), rfl, rfl⟩,
              Or.inl ⟨⟨(0 : Fin 2), (0 : Fin 2)⟩, ⟨rfl, rfl⟩, rfl, rfl⟩⟩
        · exact Fin.elim0 j

private theorem piece_bound {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x y : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0) :
    ClassBelow (Accepting L) (value E.algebra (E.algebra.eval 0 (witness x a)) y)
      (value E.algebra a (x.1, fun i => sumValue E.algebra (x.2 i) (y.2 i))) := by
  have hm := FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates
    (FiniteMorphisms.enumerateMap (doubleMap x y a))
  change ClassBelow _ (E.algebra.eval 0 (plug (normalContext y.1 y.2) (witness x a)))
    (E.algebra.eval 0 (flatten (doublePattern x y a))) at hm
  rw [FiniteEvaluation.context_evaluation E.algebra, eval_double] at hm
  exact hm

/--
---
conclusion: Lax369799.ClosedExtremal.comparison
---
Embeddings of the original root mark and the sum of the two incoming pieces into the accepting test force both comparisons by extremality.
-/
theorem comparison {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x y : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0)
    (hx : Lax369799.FiniteExtremal.IsExtremal (Accepting L) E.algebra a x)
    (hy : Accepts (Accepting L) E.algebra (E.algebra.eval 0 (witness x a)) y) :
    DataBelow (Accepting L) x y := by
  let F := Accepting L
  have hrefl := (FiniteContextualOrder.class_order F 1).1
  have hup := (FiniteSyntacticAlgebra.accepting_classes F (FiniteAcceptance.accepting_isomorphic L)).2
  refine ⟨?_, fun i => Fin.elim0 i, ?_⟩
  · intro hyr
    let z : Data (Carrier F) 0 := (⟨True, ∅⟩, x.2)
    have hz : DataBelow F z x := ⟨fun _ => trivial, fun i => Fin.elim0 i, fun i => hrefl _⟩
    have ha : Accepts F E.algebra a z := hup _ _ hy
      (root_bound L E x y a True (fun _ => Or.inr hyr))
    exact (hx.2 z hz ha).1 trivial
  · let z : Data (Carrier F) 0 := (x.1, fun i => sumValue E.algebra (x.2 i) (y.2 i))
    have hz : DataBelow F z x := ⟨id, Set.Subset.rfl, fun i =>
      ((FiniteOrderedAlgebra.sum_value_meet L E.algebra E.evaluates _ _ _).mp (hrefl _)).1⟩
    have ha : Accepts F E.algebra a z := hup _ _ hy (piece_bound L E x y a)
    intro i
    exact ((FiniteOrderedAlgebra.sum_value_meet L E.algebra E.evaluates _ _ _).mp
      ((hx.2 z hz ha).2.2 i)).2

private noncomputable def mergeMap {A : RankedSet} (x : Data A 0) (a : A 0) :
    Map (flattenPresentation (testPattern x x a).graph)
      (relabel (letterSubstitution a) (normalContext x.1 x.2).system).graph where
  toFun := fun v => Fin.cases (fun u => u) (fun _ _ => (1 : Fin 2)) v.1 v.2
  label := by rintro ⟨v, u⟩; fin_cases v <;> fin_cases u <;> rfl
  initial := fun _ h => h.1.elim
  root := by
    rintro ⟨v, u⟩ h
    fin_cases v
    · fin_cases u
      · rcases h with (h | ⟨_, h⟩) | ⟨h, _⟩
        · exact False.elim (by cases h)
        · exact Or.inr ⟨rfl, h⟩
        · exact h
      · exact Or.inl rfl
    · fin_cases u
      exact Or.inl rfl
  edge := by
    rintro ⟨v, u⟩ d t h
    rcases h with ⟨w, hw, rfl⟩ | ⟨e, he, h⟩
    · fin_cases v
      · obtain ⟨rfl, rfl, hw⟩ := hw
        have hw' := Sum.inl.inj hw
        subst w
        exact ⟨rfl, rfl⟩
      · obtain ⟨i, _, h⟩ := hw; cases h
    · fin_cases v
      · exact Fin.elim0 e
      · fin_cases e
        obtain ⟨i, hd, _⟩ := he
        fin_cases i
        subst d
        rcases h with ⟨⟨w, z⟩, hw, hz, rfl⟩ | ⟨j, _⟩
        · have hw' : w = (0 : Fin 2) := Sum.inl.inj hw.2
          subst w
          change z = (0 : Fin 2) at hz
          subst z
          exact ⟨rfl, rfl⟩
        · exact Fin.elim0 j

/--
---
conclusion: Lax369799.ClosedExtremal.in_context
---
Merging the copied incoming piece with the outer one preserves labels, roots, and edges, and hence preserves acceptance in the original context.
-/
theorem in_context {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0) :
    ClassBelow (Accepting L) (value E.algebra a x)
      (value E.algebra (E.algebra.eval 0 (witness x a)) x) := by
  have hm := FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates
    (FiniteMorphisms.fromEnumeration (mergeMap x a))
  change ClassBelow _
    (E.algebra.eval 0 (relabel (letterSubstitution a) (normalContext x.1 x.2).system))
    (E.algebra.eval 0 (plug (normalContext x.1 x.2) (witness x a))) at hm
  rw [FiniteEvaluation.context_evaluation E.algebra,
    ← E.algebra.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso _ a)] at hm
  exact hm

/--
---
conclusion: Lax369799.ClosedExtremal.below
---
Normalize any accepting context of the witness. The component comparisons transfer acceptance to the original element; contextual separation gives the order inequality.
-/
theorem below {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0)
    (hx : Lax369799.FiniteExtremal.IsExtremal (Accepting L) E.algebra a x) :
    ClassBelow (Accepting L) (E.algebra.eval 0 (witness x a)) a := by
  let F := Accepting L
  have hF := FiniteAcceptance.accepting_isomorphic L
  have hc := fun n (S T : FiniteSystem (Carrier F) n) f hf =>
    FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates (S := S) (T := T) f hf
  apply FiniteEvaluation.order_separating F hF E.algebra E.evaluates
  intro C hC
  let y : Data (Carrier F) 0 := (Lax369799.FiniteNormalForms.plantedBoundary C,
    Lax369799.FiniteNormalForms.pieceValue E.algebra C)
  have hy : Accepts F E.algebra (E.algebra.eval 0 (witness x a)) y := by
    change AcceptingClass F (E.algebra.eval 0 (plug (normalContext _ _) (atomic _)))
    rw [FiniteNormalForms.algebraic_decomposition E.algebra hc C]
    exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).mpr hC
  have hya : Accepts F E.algebra a y := (FiniteSyntacticAlgebra.accepting_classes F hF).2 _ _ hx.1
    (FiniteExtremal.data_monotone L E.algebra E.evaluates x y (comparison L E x y a hx hy) a)
  change AcceptingClass F (E.algebra.eval 0 (plug (normalContext _ _) (atomic a))) at hya
  rw [FiniteNormalForms.algebraic_decomposition E.algebra hc C a] at hya
  exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).mp hya

private theorem fixedElement {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0)
    (hx : Lax369799.ExtremalSituations.IsExtremal (Accepting L) E.algebra (x, a)) :
    Lax369799.FiniteExtremal.IsExtremal (Accepting L) E.algebra a x := by
  refine ⟨hx.1, fun y hy ha => ?_⟩
  have he := congrArg Prod.fst (hx.2 (y, a)
    ⟨hy, (FiniteContextualOrder.class_order _ 0).1 a⟩ ha)
  change y = x at he
  subst y
  exact ⟨id, Set.Subset.rfl, fun i => (FiniteContextualOrder.class_order _ 1).1 _⟩

/--
---
conclusion: Lax369799.ClosedExtremal.witness_value
---
The witness decreases the hole element and is still accepted with the original data. Minimality of the whole situation identifies the two elements.
-/
theorem witness_value {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0)
    (hx : Lax369799.ExtremalSituations.IsExtremal (Accepting L) E.algebra (x, a)) :
    E.algebra.eval 0 (witness x a) = a := by
  have hb := below L E x a (fixedElement L E x a hx)
  have ha := (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)).2 _ _ hx.1 (in_context L E x a)
  have he := hx.2 (x, E.algebra.eval 0 (witness x a))
    ⟨⟨id, Set.Subset.rfl, fun i => (FiniteContextualOrder.class_order _ 1).1 _⟩, hb⟩ ha
  exact congrArg Prod.snd he

/--
---
conclusion: Lax369799.ClosedExtremal.normal_test
---
Replace the closed witness by its equal extremal value in the comparison theorem. The reverse implication is monotonicity.
-/
theorem normal_test {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0)
    (hx : Lax369799.ExtremalSituations.IsExtremal (Accepting L) E.algebra (x, a))
    (y : Data (Carrier (Accepting L)) 0) :
    Accepts (Accepting L) E.algebra a y ↔ DataBelow (Accepting L) x y := by
  constructor
  · intro hy
    have hy' : Accepts (Accepting L) E.algebra (E.algebra.eval 0 (witness x a)) y := by
      rwa [witness_value L E x a hx]
    exact comparison L E x y a (fixedElement L E x a hx) hy'
  · intro hxy
    exact (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
      (FiniteAcceptance.accepting_isomorphic L)).2 _ _ hx.1
      (FiniteExtremal.data_monotone L E.algebra E.evaluates x y hxy a)

end Lax369799Proofs.ClosedExtremal
