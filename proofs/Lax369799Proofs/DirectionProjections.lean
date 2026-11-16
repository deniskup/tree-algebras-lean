import Lax369799.DirectionProjections
import Lax369799Proofs.ExtendedContexts

namespace Lax369799Proofs.DirectionProjections
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra
open FiniteAcceptance ExpandedSyntacticAlgebra
open Lax369799.DirectionProjections
open Lax369799Proofs.Pullbacks

/--
---
conclusion: Lax369799.DirectionProjections.monotone
---
The projection shape is fixed and only its label increases.
-/
theorem monotone {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (a b : Carrier (Accepting L) k)
    (hab : ClassBelow (Accepting L) a b) (i : Fin k) :
    ClassBelow (Accepting L) (direction E.algebra a i) (direction E.algebra b i) :=
  FiniteSyntacticAlgebra.evaluation_monotone (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) E.algebra E.evaluates
    (projection a i) (fun _ => a) (fun _ => b) (fun _ => hab)

private def directionPattern {A : RankedSet} {k : ℕ} (a : A k) :
    FiniteSystem (FiniteSystem A) k := parallel (projection a)

private def foldDirections {A : RankedSet} {k : ℕ} (a : A k) :
    Map (flattenPresentation (directionPattern a).graph) (atomic a).graph where
  toFun := fun _ => (0 : Fin 1)
  initial := fun _ _ => True.intro
  root := by rintro v (h | h); exact False.elim h; exact False.elim h.1
  label := fun _ => rfl
  edge := by
    intro v d t h
    rcases h with ⟨w, ⟨_, he⟩, _⟩ | ⟨j, ⟨hd, _⟩, ht⟩
    · cases he
    · rcases ht with ⟨w, ⟨_, he⟩, _, _⟩ | ⟨l, ⟨_, he⟩, rfl⟩
      · cases he
      · have hli : l = v.1 := Sum.inr.inj he
        subst l
        exact ⟨v.1, hd, rfl⟩

/--
---
conclusion: Lax369799.DirectionProjections.reconstruction_bound
---
Fold the separate projected copies back to the atomic element. This is
a morphism, so its evaluation reverses the comparison.
-/
theorem reconstruction_bound {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (a : Carrier (Accepting L) k) :
    ClassBelow (Accepting L) a (E.algebra.eval k (parallel (direction E.algebra a))) := by
  have h := FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates
    (FiniteMorphisms.fromEnumeration (foldDirections a))
  change ClassBelow (Accepting L) (E.algebra.eval k (atomic a))
    (E.algebra.eval k (flatten (directionPattern a))) at h
  rw [E.algebra.unit] at h
  rw [← E.algebra.associative k (directionPattern a)] at h
  exact h

private def componentMap {A : RankedSet} {k : ℕ} (b : Fin k → A 1) (i : Fin k) :
    Map (atomic (b i)).graph (flattenPresentation (projection (parallel b) i).graph) where
  toFun := fun _ => ⟨(0 : Fin 1), i⟩
  initial := fun _ _ => ⟨True.intro, True.intro⟩
  root := fun _ => False.elim
  label := fun _ => rfl
  edge := by
    rintro v d t ⟨j, rfl, rfl⟩
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    exact Or.inr ⟨i, ⟨rfl, rfl⟩, Or.inr ⟨0, ⟨rfl, rfl⟩, rfl⟩⟩

/--
---
conclusion: Lax369799.DirectionProjections.parallel_projection_bound
---
The chosen unary component maps into the projection of the parallel
family. Other components are retained, with their exits cut off.
-/
theorem parallel_projection_bound {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (b : Fin k → Carrier (Accepting L) 1) (i : Fin k) :
    ClassBelow (Accepting L) (direction E.algebra (E.algebra.eval k (parallel b)) i) (b i) := by
  have h := FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates
    (FiniteMorphisms.toEnumeration (componentMap b i))
  change ClassBelow (Accepting L) (E.algebra.eval 1 (flatten (projection (parallel b) i)))
    (E.algebra.eval 1 (atomic (b i))) at h
  rw [E.algebra.unit] at h
  rw [← E.algebra.associative 1 (projection (parallel b) i)] at h
  exact h

private theorem parallel_monotone {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (b c : Fin k → Carrier (Accepting L) 1)
    (h : ∀ i, ClassBelow (Accepting L) (b i) (c i)) :
    ClassBelow (Accepting L) (E.algebra.eval k (parallel b)) (E.algebra.eval k (parallel c)) :=
  FiniteSyntacticAlgebra.evaluation_monotone (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) E.algebra E.evaluates (parallel b) b c h

/--
---
conclusion: Lax369799.DirectionProjections.extremal_decomposition
---
An extremal element has a parallel presentation. Each canonical
projection is below its corresponding component; the reverse bound
comes from folding all projected copies to the original element.
-/
theorem extremal_decomposition {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k) (a : Carrier (Accepting L) k)
    (ha : ExtendedContexts.ExtremalElement L E a) :
    E.algebra.eval k (parallel (direction E.algebra a)) = a := by
  obtain ⟨b, hb⟩ := ExtremalSituations.parallel_decomposition L E hk a
    ((ExtendedContexts.element_iff L E a).mp ha)
  change E.algebra.eval k (parallel b) = a at hb
  have hba := parallel_monotone L E (direction E.algebra a) b (fun i => by
    rw [← hb]
    exact parallel_projection_bound L E b i)
  rw [hb] at hba
  exact (FiniteContextualOrder.class_order (Accepting L) k).2.1 _ _ hba
    (reconstruction_bound L E a)

/--
---
conclusion: Lax369799.DirectionProjections.extremal_direction
---
Refine one canonical direction in the surrounding accepting context.
Minimality of the original situation fixes the parallel value. Projecting
back forces the refined unary element to equal the original direction.
-/
theorem extremal_direction {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ} (a : Carrier (Accepting L) k)
    (ha : ExtendedContexts.ExtremalElement L E a) (i : Fin k) :
    ExtendedContexts.ExtremalElement L E (direction E.algebra a i) := by
  classical
  let F := Accepting L
  let b := direction E.algebra a
  let P := parallel b
  have hP : E.algebra.eval k P = a := extremal_decomposition L E (by have hi := i.isLt; omega) a ha
  obtain ⟨x, hx⟩ := (ExtendedContexts.element_iff L E a).mp ha
  let M := FiniteNormalForms.normalContext x.1 x.2
  obtain ⟨C, hc⟩ := FiniteVertexReplacement.vertex_context P b i
  obtain ⟨D, _, hD⟩ := FiniteContexts.composition M C
  have hbase : E.algebra.eval 0 (plug D (atomic (b i))) =
      E.algebra.eval 0 (plug M (atomic a)) := by
    rw [E.algebra.isomorphic _ _ _ (hD _)]
    obtain ⟨f⟩ := hc b (fun _ _ => rfl)
    have hi := UntrimmedFlattening.flatten_labels_iso M.system
      (substitution (plug C (atomic (b i)))) (substitution P) (by
        intro r u
        cases u with
        | inl u => exact ⟨UntrimmedFlattening.isoRefl _⟩
        | inr h => obtain ⟨h⟩ := h; subst r; exact ⟨f⟩)
    change Isomorphic (plug M (plug C (atomic (b i)))) (plug M P) at hi
    rw [E.algebra.isomorphic _ _ _ hi, FiniteEvaluation.context_evaluation, hP]
  have hacc : AcceptingClass F (E.algebra.eval 0 (plug D (atomic (b i)))) := by
    rw [hbase]
    exact hx.1
  obtain ⟨c, hcExt, hcb, hcAcc⟩ := ExtremalSituations.replacement L hL hrec E D (b i) hacc
  let b' := Function.update b i c
  have hsame : ∀ j, j ≠ i → b j = b' j := by intro j hj; simp [b', hj]
  have hci : b' i = c := by simp [b']
  have hval : E.algebra.eval 0 (plug D (atomic c)) =
      E.algebra.eval 0 (plug M (atomic (E.algebra.eval k (parallel b')))) := by
    rw [E.algebra.isomorphic _ _ _ (hD _)]
    have hi := hc b' hsame
    rw [hci] at hi
    obtain ⟨f⟩ := hi
    have hj := UntrimmedFlattening.flatten_labels_iso M.system
      (substitution (plug C (atomic c))) (substitution (parallel b')) (by
        intro r u
        cases u with
        | inl u => exact ⟨UntrimmedFlattening.isoRefl _⟩
        | inr h => obtain ⟨h⟩ := h; subst r; exact ⟨f⟩)
    change Isomorphic (plug M (plug C (atomic c))) (plug M (parallel b')) at hj
    rw [E.algebra.isomorphic _ _ _ hj, FiniteEvaluation.context_evaluation]
  rw [hval] at hcAcc
  have hle : ClassBelow F (E.algebra.eval k (parallel b')) a := by
    rw [← hP]
    apply parallel_monotone L E
    intro j
    by_cases hj : j = i
    · subst j; simpa [b'] using hcb
    · rw [← hsame j hj]
      exact (FiniteContextualOrder.class_order F 1).1 _
  have hbelow : ExtremalSituations.Below F (x, E.algebra.eval k (parallel b')) (x, a) :=
    ⟨⟨id, Set.Subset.rfl, fun j => (FiniteContextualOrder.class_order F 1).1 _⟩, hle⟩
  have he : E.algebra.eval k (parallel b') = a := congrArg Prod.snd (hx.2 _ hbelow hcAcc)
  have hbc : ClassBelow F (b i) c := by
    have h := parallel_projection_bound L E b' i
    rw [he, hci] at h
    exact h
  have hEq : c = b i := (FiniteContextualOrder.class_order F 1).2.1 _ _ hcb hbc
  rw [hEq] at hcExt
  exact (ExtendedContexts.element_iff L E _).mpr hcExt

end Lax369799Proofs.DirectionProjections
