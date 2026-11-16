import Lax369799.GraphChoices
import Lax369799Proofs.ContextChoices

namespace Lax369799Proofs.GraphChoices
set_option backward.isDefEq.respectTransparency false
open Lax369799
open Lax369799.GraphChoices
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance
open FiniteDecomposition FiniteSyntacticAlgebra ExpandedSyntacticAlgebra

private noncomputable def drillAt {A : RankedSet} (P : FiniteSystem A 0)
    (v : P.Vertex) (hv : (P.graph.label v).1 = 1) : Context A 1 0 := by
  classical
  refine ⟨⟨P.size, {
    label := fun w => if w = v then ⟨1, Sum.inr ⟨rfl⟩⟩
      else ⟨(P.graph.label w).1, Sum.inl (P.graph.label w).2⟩
    initial := P.graph.initial
    root := P.graph.root
    edge := P.graph.edge
    direction_valid := ?_ }⟩, ?_⟩
  · intro w d t h
    by_cases hw : w = v
    · subst w
      simpa [hv] using P.graph.direction_valid v d t h
    · simpa only [if_neg hw] using P.graph.direction_valid w d t h
  · refine ⟨v, ?_, ?_⟩
    · change Flattening.IsHole (if v = v then _ else _)
      rw [if_pos rfl]
      exact ⟨⟨rfl⟩, rfl⟩
    · intro w h
      by_cases hw : w = v
      · exact hw
      · simp only [if_neg hw] at h
        obtain ⟨eq, he⟩ := h
        cases he

private theorem drill_hole {A : RankedSet} (P : FiniteSystem A 0)
    (v : P.Vertex) (hv : (P.graph.label v).1 = 1) : holeVertex (drillAt P v hv) = v := by
  classical
  apply Eq.symm
  apply (Classical.choose_spec (drillAt P v hv).one_hole).2
  change Flattening.IsHole (if v = v then _ else _)
  rw [if_pos rfl]
  exact ⟨⟨rfl⟩, rfl⟩

private theorem drill_label {A : RankedSet} (P : FiniteSystem A 0)
    (v : P.Vertex) (hv : (P.graph.label v).1 = 1) (w : P.Vertex) :
    (relabel (FiniteNormalForms.letterSubstitution (hv ▸ (P.graph.label v).2))
      (drillAt P v hv).system).graph.label w = P.graph.label w := by
  classical
  dsimp only [relabel, drillAt]
  by_cases hw : w = v
  · subst w
    rw [if_pos rfl]
    change (⟨1, hv ▸ (P.graph.label v).2⟩ : RankedSystems.Symbol A) = P.graph.label v
    generalize P.graph.label v = l at hv ⊢
    obtain ⟨r, a⟩ := l
    cases hv
    rfl
  · rw [if_neg hw]
    rfl

private theorem row_eval {A : RankedSet} (E : Algebra A) (P : FiniteSystem A 0)
    (v : P.Vertex) (hv : (P.graph.label v).1 = 1) (p : Set P.Vertex) :
    E.eval 0 (plug (ContextChoices.restrict (drillAt P v hv) p)
      (atomic (hv ▸ (P.graph.label v).2))) = E.eval 0 (restrictRow P v p) := by
  rw [E.isomorphic _ _ _ (FiniteNormalForms.plug_atomic_iso _ _)]
  apply E.isomorphic
  refine ⟨{ vertex := Equiv.refl P.Vertex
            label := ?_
            initial := fun _ => Iff.rfl
            root := fun _ => Iff.rfl
            edge := ?_ }⟩
  · intro w
    exact (drill_label P v hv w).symm
  · intro w d t
    change (P.graph.edge w d (Sum.map (Equiv.refl P.Vertex) id t) ∧ _) ↔
      (P.graph.edge w d t ∧ (w = holeVertex (drillAt P v hv) → _))
    rw [drill_hole]
    cases t <;> rfl

private theorem row_univ {A : RankedSet} (P : FiniteSystem A 0) (v : P.Vertex) :
    restrictRow P v Set.univ = P := by
  cases P
  dsimp only [restrictRow]
  congr 1
  congr 1
  funext w d t
  cases t with
  | inl u =>
    apply propext
    exact ⟨And.left, fun h => ⟨h, fun _ => True.intro⟩⟩
  | inr j => exact Fin.elim0 j

/--
---
conclusion: Lax369799.GraphChoices.row_choices
---
Drill the unary vertex, apply the cyclic context-choice theorem, and
identify atomic filling with the original labels.
-/
theorem row_choices {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (P : FiniteSystem (Carrier (Accepting L)) 0)
    (v : P.Vertex) (hv : (P.graph.label v).1 = 1)
    (hs : ExtremalUnaryTypes.Selected L E (hv ▸ (P.graph.label v).2)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 P) ↔
      ∀ w : P.Vertex, AcceptingClass (Accepting L)
        (E.algebra.eval 0 (restrictRow P v {w})) := by
  have hu := ContextChoices.accepting_finite L E _ hs (drillAt P v hv)
    Finset.univ ⟨v, Finset.mem_univ _⟩
  simp only [Finset.coe_univ, Finset.mem_univ, forall_true_left, row_eval, row_univ] at hu
  exact hu

private theorem choose_empty {A : RankedSet} (P : FiniteSystem A 0)
    (f : P.Vertex → P.Vertex) : chooseRows P ∅ f = P := by
  cases P
  dsimp only [chooseRows]
  congr 1
  congr 1
  funext v d t
  simp

private theorem choose_insert {A : RankedSet} (P : FiniteSystem A 0)
    (s : Finset P.Vertex) (v w : P.Vertex) (hv : v ∉ s) (f : P.Vertex → P.Vertex) :
    chooseRows (restrictRow P v {w}) s f = chooseRows P (insert v s) (Function.update f v w) := by
  classical
  dsimp only [chooseRows, restrictRow]
  congr 1
  congr 1
  funext u d t
  cases t with
  | inr j => exact Fin.elim0 j
  | inl z =>
    apply propext
    change ((P.graph.edge u d (.inl z) ∧ (u = v → z = w)) ∧ (u ∈ s → Sum.inl z = Sum.inl (f u))) ↔
      (P.graph.edge u d (.inl z) ∧ (u ∈ insert v s → Sum.inl z = Sum.inl (Function.update f v w u)))
    by_cases hu : u = v
    · subst u
      simp [hv]
    · simp [hu]

private theorem nullary_row {A : RankedSet} (P : FiniteSystem A 0)
    (v : P.Vertex) (hv : (P.graph.label v).1 = 0) (p : Set P.Vertex) :
    restrictRow P v p = P := by
  dsimp only [restrictRow]
  congr 1
  congr 1
  funext w d t
  apply propext
  refine ⟨And.left, fun he => ⟨he, ?_⟩⟩
  intro hw
  subst w
  have h := P.graph.direction_valid v d t he
  omega

private theorem row_choices_le_one {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (P : FiniteSystem (Carrier (Accepting L)) 0)
    (v : P.Vertex) (hv : (P.graph.label v).1 ≤ 1)
    (hs : ∀ h : (P.graph.label v).1 = 1,
      ExtremalUnaryTypes.Selected L E (h ▸ (P.graph.label v).2)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 P) ↔
      ∀ w : P.Vertex, AcceptingClass (Accepting L)
        (E.algebra.eval 0 (restrictRow P v {w})) := by
  by_cases h : (P.graph.label v).1 = 1
  · exact row_choices L E P v h (hs h)
  · have hz : (P.graph.label v).1 = 0 := by omega
    simp only [nullary_row P v hz]
    exact ⟨fun ha _ => ha, fun ha => ha v⟩

/--
---
conclusion: Lax369799.GraphChoices.finite_choices
---
Induct over the finite set of vertices. At each vertex use unary
extremality, or absence of outgoing edges for a nullary label.
-/
theorem finite_choices {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (P : FiniteSystem (Carrier (Accepting L)) 0)
    (hu : ∀ v, (P.graph.label v).1 ≤ 1)
    (hs : ∀ v (h : (P.graph.label v).1 = 1),
      ExtremalUnaryTypes.Selected L E (h ▸ (P.graph.label v).2))
    (s : Finset P.Vertex) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 P) ↔
      ∀ f : P.Vertex → P.Vertex, AcceptingClass (Accepting L) (E.algebra.eval 0 (chooseRows P s f)) := by
  classical
  suffices hall : ∀ N (s : Finset (Fin N))
      (P : FiniteSystem (Carrier (Accepting L)) 0) (hN : P.size = N)
      (hu : ∀ v, (P.graph.label v).1 ≤ 1)
      (hs : ∀ v (h : (P.graph.label v).1 = 1),
        ExtremalUnaryTypes.Selected L E (h ▸ (P.graph.label v).2)),
      AcceptingClass (Accepting L) (E.algebra.eval 0 P) ↔
        ∀ f : P.Vertex → P.Vertex, AcceptingClass (Accepting L)
          (E.algebra.eval 0 (chooseRows P (s.map (Fin.castOrderIso hN.symm).toEquiv.toEmbedding) f)) by
    simpa using hall P.size s P rfl hu hs
  intro N s
  induction s using Finset.induction_on with
  | empty =>
    intro Q hN hu hs
    simp only [Finset.map_empty, choose_empty]
    exact ⟨fun ha _ => ha, fun ha => ha id⟩
  | @insert v s hv ih =>
    intro Q hN hu hs
    subst N
    let s' : Finset Q.Vertex := s
    let v' : Q.Vertex := v
    have hmap (t : Finset Q.Vertex) : t.map (Fin.castOrderIso (rfl : Q.size = Q.size)).toEquiv.toEmbedding = t := by
      ext w; simp
    rw [hmap]
    change AcceptingClass (Accepting L) (E.algebra.eval 0 Q) ↔
      ∀ f : Q.Vertex → Q.Vertex, AcceptingClass (Accepting L)
        (E.algebra.eval 0 (chooseRows Q (insert v' s') f))
    rw [row_choices_le_one L E Q v' (hu v') (hs v')]
    constructor
    · intro ha f
      have hi := (ih (restrictRow Q v' {f v'}) rfl hu hs).mp (ha (f v')) f
      rw [hmap] at hi
      change AcceptingClass (Accepting L)
        (E.algebra.eval 0 (chooseRows (restrictRow Q v' {f v'}) s' f)) at hi
      rw [choose_insert Q s' v' (f v') hv f] at hi
      have he : Function.update f v' (f v') = f := Function.update_eq_self _ _
      rwa [he] at hi
    · intro ha w
      apply (ih (restrictRow Q v' {w}) rfl hu hs).mpr
      intro f
      rw [hmap]
      change AcceptingClass (Accepting L)
        (E.algebra.eval 0 (chooseRows (restrictRow Q v' {w}) s' f))
      rw [choose_insert Q s' v' w hv f]
      exact ha _

/--
---
conclusion: Lax369799.GraphChoices.chosen_functional
---
Every retained edge has the target specified by the choice function.
-/
theorem chosen_functional {A : RankedSet} (P : FiniteSystem A 0)
    (f : P.Vertex → P.Vertex) (v : P.Vertex) (d : ℕ) (t u : P.Vertex ⊕ Fin 0)
    (ht : (chooseRows P Finset.univ f).graph.edge v d t)
    (hu : (chooseRows P Finset.univ f).graph.edge v d u) : t = u :=
  (ht.2 (Finset.mem_univ v)).trans (hu.2 (Finset.mem_univ v)).symm

private theorem completion {A : RankedSet} (P : FiniteSystem A 0) (f : P.Vertex → P.Vertex) :
    ∃ g : P.Vertex → P.Vertex, Admissible P g ∧
      ∀ v d, P.graph.edge v d (.inl (f v)) → g v = f v := by
  classical
  have step (v : P.Vertex) : ∃ w : P.Vertex,
      ((∃ d u, P.graph.edge v d (.inl u)) → ∃ d, P.graph.edge v d (.inl w)) ∧
      (∀ d, P.graph.edge v d (.inl (f v)) → w = f v) := by
    by_cases hf : ∃ d, P.graph.edge v d (.inl (f v))
    · exact ⟨f v, fun _ => hf, fun _ _ => rfl⟩
    · by_cases h : ∃ d u, P.graph.edge v d (.inl u)
      · obtain ⟨d, w, hw⟩ := h
        exact ⟨w, fun _ => ⟨d, hw⟩, fun d hd => False.elim (hf ⟨d, hd⟩)⟩
      · exact ⟨f v, fun hn => False.elim (h hn), fun _ _ => rfl⟩
  choose g hg using step
  exact ⟨g, fun v => (hg v).1, fun v => (hg v).2⟩

private def restrictionMap {A : RankedSet} (P : FiniteSystem A 0)
    (f g : P.Vertex → P.Vertex) (h : ∀ v d, P.graph.edge v d (.inl (f v)) → g v = f v) :
    FiniteMorphisms.Morphism (chooseRows P Finset.univ f) (chooseRows P Finset.univ g) where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by
    intro v d t ht
    have ht' := ht.2 (Finset.mem_univ v)
    subst t
    change P.graph.edge v d (.inl (f v)) ∧ (v ∈ Finset.univ → Sum.inl (f v) = Sum.inl (g v))
    refine ⟨ht.1, fun _ => ?_⟩
    rw [h v d ht.1]

/--
---
conclusion: Lax369799.GraphChoices.admissible_test
---
Complete a choice to use an existing edge whenever possible. The original
restriction maps into its completion, so reverse morphism monotonicity
supplies acceptance for the restrictions that delete all outgoing edges.
-/
theorem admissible_test {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (P : FiniteSystem (Carrier (Accepting L)) 0)
    (hu : ∀ v, (P.graph.label v).1 ≤ 1)
    (hs : ∀ v (h : (P.graph.label v).1 = 1),
      ExtremalUnaryTypes.Selected L E (h ▸ (P.graph.label v).2)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 P) ↔
      ∀ f : P.Vertex → P.Vertex, Admissible P f →
        AcceptingClass (Accepting L) (E.algebra.eval 0 (chooseRows P Finset.univ f)) := by
  rw [GraphChoices.finite_choices L E P hu hs Finset.univ]
  refine ⟨fun h f _ => h f, ?_⟩
  intro h f
  obtain ⟨g, hg, hgf⟩ := completion P f
  exact (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)).2 _ _ (h g hg)
      (FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates (restrictionMap P f g hgf))


end Lax369799Proofs.GraphChoices
