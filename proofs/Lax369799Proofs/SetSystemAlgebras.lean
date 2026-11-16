import Lax369799.SetSystemAlgebras
import Lax369799Proofs.ExpandedSyntacticAlgebra
import Lax369799Proofs.FiniteOuterMorphisms
import Lax369799Proofs.SumCovers

namespace Lax369799Proofs.SetSystemAlgebras
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra FiniteContextualOrder FiniteAcceptance
open Lax369799.SetSystemAlgebras
set_option backward.isDefEq.respectTransparency false

private def identity {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    PresentationCovers.Cover S.graph S.graph where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by intro v d t h; cases t <;> exact h
  initial_lift := fun v h => ⟨v, h, rfl⟩
  root_lift := fun v h => ⟨v, h, rfl⟩
  edge_lift := fun v d t h => ⟨t, h, by cases t <;> rfl⟩

/--
---
conclusion: Lax369799.SetSystemAlgebras.folding_invariance
---
Use the source as a common unfolding, with its identity folding.
-/
theorem folding_invariance {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (S T : FiniteSystem A n) (f : PresentationCovers.Cover S.graph T.graph)
    (hf : Function.Surjective f.toFun) : E.eval n S = E.eval n T :=
  E.unfold_invariant n S T ⟨S, identity S, f, Function.surjective_id, hf⟩

theorem raw_cover {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    {V W : Type} [Fintype V] [Fintype W] {G : RankedSystems.Presentation A n V}
    {H : RankedSystems.Presentation A n W} (f : PresentationCovers.Cover G H)
    (hf : Function.Surjective f.toFun) : E.eval n (enumerate G) = E.eval n (enumerate H) := by
  apply folding_invariance E _ _ (FiniteCovers.enumerateCover f)
  intro w
  obtain ⟨v, hv⟩ := hf ((Fintype.equivFin W).symm w)
  refine ⟨Fintype.equivFin V v, ?_⟩
  change Fintype.equivFin W (f.toFun ((Fintype.equivFin V).symm (Fintype.equivFin V v))) = w
  rw [Equiv.symm_apply_apply, hv, Equiv.apply_symm_apply]

/--
---
conclusion: Lax369799.SetSystemAlgebras.eval_sum
---
Flatten the binary pattern and evaluate its two labels first.
-/
theorem eval_sum {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (S T : FiniteSystem A n) :
    E.eval n (sum S T) = sumValue E.toAlgebra (E.eval n S) (E.eval n T) := by
  have hb : relabel E.eval (binary S T) = binary (E.eval n S) (E.eval n T) := by
    dsimp only [relabel, binary]
    congr 1
    congr 1
    funext v
    exact Fin.cases rfl (fun _ => rfl) v
  exact ((E.associative n (binary S T)).trans
    (E.isomorphic n _ _ (FiniteSums.flatten_binary S T))).symm.trans (congrArg (E.eval n) hb)

private theorem eval_sum_assoc {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (S T U : FiniteSystem A n) :
    E.eval n (sum (sum S T) U) = E.eval n (sum S (sum T U)) := by
  classical
  let left := SumCovers.combineCover
    (FiniteCovers.isoCover (UntrimmedFlattening.reindexIso
      (SumCovers.combine S.graph T.graph) (Fintype.equivFin _)))
    (SumCovers.identity U.graph)
  let right := SumCovers.combineCover (SumCovers.identity S.graph)
    (FiniteCovers.isoCover (UntrimmedFlattening.reindexIso
      (SumCovers.combine T.graph U.graph) (Fintype.equivFin _)))
  have hl : Function.Surjective left.toFun := by
    intro w
    cases w with
    | inl w => exact ⟨.inl ((Fintype.equivFin _).symm w), by
        change Sum.inl (Fintype.equivFin _ ((Fintype.equivFin _).symm w)) = .inl w
        rw [Equiv.apply_symm_apply]⟩
    | inr w => exact ⟨.inr w, rfl⟩
  have hr : Function.Surjective right.toFun := by
    intro w
    cases w with
    | inl w => exact ⟨.inl w, rfl⟩
    | inr w => exact ⟨.inr ((Fintype.equivFin _).symm w), by
        change Sum.inr (Fintype.equivFin _ ((Fintype.equivFin _).symm w)) = .inr w
        rw [Equiv.apply_symm_apply]⟩
  exact (raw_cover E left hl).symm.trans
    ((raw_cover E (SumCovers.associate S.graph T.graph U.graph)
      (Equiv.sumAssoc S.Vertex T.Vertex U.Vertex).surjective).trans (raw_cover E right hr))

/--
---
conclusion: Lax369799.SetSystemAlgebras.meet_laws
---
Disjoint-union associators and swaps preserve evaluation. The identity
morphism gives idempotence. No continuity axiom is used.
-/
theorem meet_laws {A : RankedSet} (E : SetAlgebra A) (n : ℕ) :
    (∀ a b c : A n, sumValue E.toAlgebra (sumValue E.toAlgebra a b) c =
      sumValue E.toAlgebra a (sumValue E.toAlgebra b c)) ∧
    (∀ a b : A n, sumValue E.toAlgebra a b = sumValue E.toAlgebra b a) ∧
    (∀ a : A n, sumValue E.toAlgebra a a = a) := by
  have hunit (a b : A n) : E.eval n (sum (atomic a) (atomic b)) = sumValue E.toAlgebra a b := by
    rw [eval_sum, E.unit, E.unit]
  refine ⟨?_, ?_, ?_⟩
  · intro a b c
    have h := eval_sum_assoc E (atomic a) (atomic b) (atomic c)
    simpa only [eval_sum, E.unit] using h
  · intro a b
    have h := raw_cover E (SumCovers.swap (atomic a).graph (atomic b).graph)
      (Equiv.sumComm (atomic a).Vertex (atomic b).Vertex).surjective
    change E.eval n (sum (atomic a) (atomic b)) = E.eval n (sum (atomic b) (atomic a)) at h
    simpa only [hunit] using h
  · intro a
    let f : FiniteMorphisms.Morphism (atomic a) (atomic a) := {
      toFun := id, label := fun _ => rfl, initial := fun _ h => h,
      root := fun _ h => h, edge := by intro v d t h; cases t <;> exact h }
    have h := E.morphism n (atomic a) (atomic a) ⟨f⟩
    simpa only [E.unit] using h

/--
---
conclusion: Lax369799.SetSystemAlgebras.order_laws
---
The order induced by an associative, commutative, idempotent binary
operation is a partial order, and that operation computes its meet.
-/
theorem order_laws {A : RankedSet} (E : SetAlgebra A) (n : ℕ) :
    (∀ a : A n, Below E a a) ∧
    (∀ a b : A n, Below E a b → Below E b a → a = b) ∧
    (∀ a b c : A n, Below E a b → Below E b c → Below E a c) ∧
    (∀ a b c : A n, Below E c (sumValue E.toAlgebra a b) ↔ Below E c a ∧ Below E c b) := by
  obtain ⟨assoc, comm, idem⟩ := meet_laws E n
  let meet := fun a b : A n => sumValue E.toAlgebra a b
  change ∀ a b c, meet (meet a b) c = meet a (meet b c) at assoc
  change ∀ a b, meet a b = meet b a at comm
  change ∀ a, meet a a = a at idem
  change (∀ a, meet a a = a) ∧
    (∀ a b, meet a b = a → meet b a = b → a = b) ∧
    (∀ a b c, meet a b = a → meet b c = b → meet a c = a) ∧
    (∀ a b c, meet c (meet a b) = c ↔ meet c a = c ∧ meet c b = c)
  have trans (a b c : A n) (hab : meet a b = a) (hbc : meet b c = b) : meet a c = a := by
    calc
      meet a c = meet (meet a b) c := by rw [hab]
      _ = meet a (meet b c) := assoc a b c
      _ = a := by rw [hbc, hab]
  refine ⟨idem, fun a b hab hba => hab.symm.trans ((comm a b).trans hba), trans, ?_⟩
  intro a b c
  constructor
  · intro h
    constructor
    · apply trans c (meet a b) a h
      rw [comm a b, assoc b a a, idem, comm]
    · apply trans c (meet a b) b h
      rw [assoc, idem]
  · rintro ⟨ha, hb⟩
    rw [← assoc, ha, hb]

/--
---
conclusion: Lax369799.SetSystemAlgebras.evaluation_monotone
---
Expand each label as the binary sum of the old and new value. This sum
evaluates to the old value, while the new-labelled graph maps into the
expanded presentation by selecting its second copy at every vertex.
-/
theorem evaluation_monotone {A B : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (P : FiniteSystem B n) (q r : ∀ v : P.Vertex, A (P.graph.label v).1)
    (h : ∀ v, Below E (q v) (r v)) :
    Below E (E.eval n (withLabels P q)) (E.eval n (withLabels P r)) := by
  let Q := withLabels P (fun v => binary (q v) (r v))
  let raw : Lax369799Proofs.Pullbacks.Map (withLabels P r).graph (flattenPresentation Q.graph) := {
    toFun := fun v => ⟨v, (1 : Fin 2)⟩
    initial := fun _ hi => ⟨hi, True.intro⟩
    root := fun _ hr => Or.inr ⟨hr, True.intro⟩
    label := fun _ => rfl
    edge := by
      intro v d t ht
      let i : Fin (P.graph.label v).1 := ⟨d, P.graph.direction_valid v d t ht⟩
      refine Or.inr ⟨i, ⟨i, rfl, rfl⟩, ?_⟩
      cases t with
      | inl w => exact Or.inl ⟨⟨w, (1 : Fin 2)⟩, ht, True.intro, rfl⟩
      | inr j => exact Or.inr ⟨j, ht, rfl⟩ }
  have hm := E.morphism n _ _ ⟨FiniteMorphisms.toEnumeration raw⟩
  change Below E (E.eval n (flatten Q)) (E.eval n (withLabels P r)) at hm
  rw [← E.associative n Q] at hm
  have he : relabel E.eval Q = withLabels P q := by
    dsimp only [relabel, withLabels, Q]
    congr 1
    congr 1
    funext v
    exact congrArg (Sigma.mk (P.graph.label v).1) (h v)
  rwa [he] at hm

/--
---
conclusion: Lax369799.SetSystemAlgebras.syntactic_order
---
The meet characterization and antisymmetry identify the contextual order
with the order induced by disjoint union.
-/
theorem syntactic_order {A : RankedSet} (L : Algebras.Language A)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) {n : ℕ}
    (a b : Carrier (Accepting L) n) :
    ClassBelow (Accepting L) a b ↔ sumValue E.algebra a b = a := by
  have ho := FiniteContextualOrder.class_order (Accepting L) n
  have hm := FiniteOrderedAlgebra.sum_value_meet L E.algebra E.evaluates a b
  have hl := (hm _).mp (ho.1 _)
  constructor
  · intro hab
    exact ho.2.1 _ _ hl.1 ((hm a).mpr ⟨ho.1 a, hab⟩)
  · intro h
    rw [h] at hl
    exact hl.2

/--
---
conclusion: Lax369799.SetSystemAlgebras.syntactic_structure
---
The quotient substitution algebra is invariant under surjective covers
and reverses morphisms. The contextual meet gives its induced order.
-/
theorem syntactic_structure {A : RankedSet} (L : Algebras.Language A)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) :
    ∃ D : SetAlgebra (Carrier (Accepting L)), D.toAlgebra = E.algebra := by
  refine ⟨{ E.algebra with unfold_invariant := ?_, morphism := ?_ }, rfl⟩
  · rintro n S T ⟨U, f, g, hf, hg⟩
    exact (FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates f hf).symm.trans
      (FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates g hg)
  · rintro n S T ⟨f⟩
    exact (syntactic_order L E _ _).mp
      (FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates f)

end Lax369799Proofs.SetSystemAlgebras
