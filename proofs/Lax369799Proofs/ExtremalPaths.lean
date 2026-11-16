import Lax369799.ExtremalPaths
import Lax369799Proofs.DirectionProjections
import Lax369799Proofs.FiniteCoverFamilies
import Lax369799Proofs.GraphChoices

namespace Lax369799Proofs.ExtremalPaths
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet Presentation System trim)
open FinitePresentations FiniteContextualOrder FiniteSyntacticAlgebra FiniteAcceptance
open Lax369799Proofs.Pullbacks

open Lax369799.ExtremalPaths (Unary)
abbrev Complete {A : RankedSet} (P : FiniteSystem A 0) :=
  ∀ v d, d < (P.graph.label v).1 → ∃! t, P.graph.edge v d t

def startAt {A : RankedSet} (P : FiniteSystem A 0) (v : P.Vertex) : FiniteSystem A 0 :=
  ⟨P.size, {P.graph with initial := {v}, root := ∅}⟩

def unmark {A : RankedSet} (P : FiniteSystem A 0) : FiniteSystem A 0 :=
  ⟨P.size, {P.graph with initial := ∅, root := ∅}⟩

noncomputable def fromVertex {A : RankedSet} (P : FiniteSystem A 0) (ht : Complete P)
    (v : P.Vertex) : System A 0 :=
  ⟨trim (startAt P v).graph, Yields.trim_deterministic _ v rfl rfl ht⟩

private noncomputable def first {A : RankedSet} (B : System A 0) : B.val.Vertex :=
  Classical.choose B.property.1

private theorem first_initial {A : RankedSet} (B : System A 0) :
    B.val.graph.initial (first B) := by
  rw [Classical.choose_spec B.property.1]
  rfl

private noncomputable def prependGraph {A : RankedSet} (a : RankedSystems.Symbol A)
    (ha : a.1 = 1) (B : System A 0) : Presentation A 0 (Option B.val.Vertex) where
  label := Option.elim' a B.val.graph.label
  initial := {none}
  root := ∅
  edge := fun v d t => match v with
    | none => d = 0 ∧ t = .inl (some (first B))
    | some w => ∃ s, B.val.graph.edge w d s ∧ t = Sum.map some id s
  direction_valid := by
    intro v d t h
    cases v with
    | none => rw [h.1]; change 0 < a.1; omega
    | some v => obtain ⟨s, hs, _⟩ := h; exact B.val.graph.direction_valid v d s hs

private noncomputable abbrev prepend {A : RankedSet} (a : RankedSystems.Symbol A)
    (ha : a.1 = 1) (B : System A 0) : System A 0 := by
  refine ⟨trim (prependGraph a ha B), Yields.trim_deterministic _ none rfl rfl ?_⟩
  intro v d hd
  cases v with
  | none =>
    change d < a.1 at hd
    rw [ha] at hd
    have hd : d = 0 := by omega
    subst d
    exact ⟨.inl (some (first B)), ⟨rfl, rfl⟩, fun _ h => h.2⟩
  | some v =>
    obtain ⟨t, ht, hu⟩ := B.property.2.2 v d hd
    refine ⟨Sum.map some id t, ⟨t, ht, rfl⟩, ?_⟩
    rintro s ⟨t', ht', rfl⟩
    rw [hu t' ht']

private theorem some_reachable {A : RankedSet} (a : RankedSystems.Symbol A)
    (ha : a.1 = 1) (B : System A 0) (v : B.val.Vertex) :
    (prependGraph a ha B).Reachable (some v) := by
  obtain ⟨r, hr, hp⟩ := B.val.reachable v
  have hr' : r = first B := by
    rcases hr with hr | hr
    · rw [Classical.choose_spec B.property.1] at hr
      exact hr
    · rw [B.property.2.1] at hr
      exact False.elim hr
  subst r
  have liftPath : ∀ {x y : B.val.Vertex}, Relation.ReflTransGen B.val.graph.Step x y →
      Relation.ReflTransGen (prependGraph a ha B).Step (some x) (some y) := by
    intro x y hp
    induction hp with
    | refl => exact .refl
    | @tail y z hp hyz ih =>
      obtain ⟨d, hd⟩ := hyz
      exact ih.tail ⟨d, ⟨.inl z, hd, rfl⟩⟩
  exact ⟨none, Or.inl rfl, (Relation.ReflTransGen.single ⟨0, rfl, rfl⟩).trans (liftPath hp)⟩

private noncomputable def prepend_tail {A : RankedSet} (a : RankedSystems.Symbol A)
    (ha : a.1 = 1) (B : System A 0) :
    FiniteMorphisms.Morphism (unmark (ofSetSystem B.val)) (ofSetSystem (prepend a ha B).val) where
  toFun := fun v => index (prependGraph a ha B) ⟨some v, some_reachable a ha B v⟩
  label := by intro v; change (prependGraph a ha B).label (vertex _ (index _ _)) = _; rw [vertex_index]; rfl
  initial := fun _ => False.elim
  root := fun _ => False.elim
  edge := by
    intro v d t h
    cases t with
    | inr i => exact Fin.elim0 i
    | inl w =>
      change (prependGraph a ha B).edge (vertex _ (index _ _)) d (.inl (vertex _ (index _ _)))
      rw [vertex_index, vertex_index]
      exact ⟨.inl w, h, rfl⟩

private noncomputable def prepend_map {A : RankedSet} (G : FiniteSystem A 0)
    (v w : G.Vertex) (hv : (G.graph.label v).1 = 1) (he : G.graph.edge v 0 (.inl w))
    (B : System A 0) (f : FiniteMorphisms.Morphism (ofSetSystem B.val) (startAt G w)) :
    FiniteMorphisms.Morphism (ofSetSystem (prepend (G.graph.label v) hv B).val) (startAt G v) := by
  change FiniteMorphisms.Morphism (ofSetSystem (trim (prependGraph (G.graph.label v) hv B))) (startAt G v)
  let raw : Map (prependGraph (G.graph.label v) hv B) (startAt G v).graph := {
    toFun := Option.elim' v f.toFun
    label := by intro x; cases x with | none => rfl | some x => exact f.label x
    initial := by rintro x rfl; rfl
    root := fun _ => False.elim
    edge := by
      intro x d t h
      cases x with
      | none =>
        rcases h with ⟨rfl, rfl⟩
        have hf : f.toFun (first B) = w := f.initial _ (first_initial B)
        simpa only [startAt, Option.elim'_none, Sum.map_inl, Option.elim'_some, hf] using he
      | some x =>
        obtain ⟨s, hs, rfl⟩ := h
        have hf := f.edge x d s hs
        cases s with
        | inl y => exact hf
        | inr i => exact Fin.elim0 i }
  exact {
    toFun := fun x => raw.toFun (vertex (prependGraph (G.graph.label v) hv B) (by exact x))
    initial := fun x h => raw.initial (vertex (prependGraph (G.graph.label v) hv B) (by exact x)) (by exact h)
    root := fun x h => raw.root (vertex (prependGraph (G.graph.label v) hv B) (by exact x)) (by exact h)
    label := fun x => raw.label _
    edge := by
      intro x d t h
      have hh := raw.edge (vertex (prependGraph (G.graph.label v) hv B) (by exact x)) d (Sum.map (vertex (prependGraph (G.graph.label v) hv B)) id (by exact t)) (by exact h)
      cases t <;> exact hh }

private theorem prepend_unary {A : RankedSet} (a : RankedSystems.Symbol A) (ha : a.1 = 1)
    (B : System A 0) (hB : Unary (ofSetSystem B.val)) : Unary (ofSetSystem (prepend a ha B).val) := by
  change Unary (ofSetSystem (trim (prependGraph a ha B)))
  intro v
  change ((prependGraph a ha B).label (vertex (prependGraph a ha B) (by exact v))).1 ≤ 1
  cases vertex (prependGraph a ha B) (by exact v) with
  | none => change a.1 ≤ 1; omega
  | some w => exact hB w

private def compose {A : RankedSet} {S T U : FiniteSystem A 0}
    (f : FiniteMorphisms.Morphism S T) (g : FiniteMorphisms.Morphism T U) :
    FiniteMorphisms.Morphism S U where
  toFun := g.toFun ∘ f.toFun
  label := fun v => (g.label _).trans (f.label v)
  initial := fun v h => g.initial _ (f.initial v h)
  root := fun v h => g.root _ (f.root v h)
  edge := by intro v d t h; have hh := g.edge _ d _ (f.edge v d t h); cases t <;> exact hh

private def unmarked_map {A : RankedSet} {S T : FiniteSystem A 0}
    (f : FiniteMorphisms.Morphism S T) : FiniteMorphisms.Morphism (unmark S) (unmark T) where
  toFun := f.toFun
  label := f.label
  initial := fun _ => False.elim
  root := fun _ => False.elim
  edge := f.edge

private theorem extend {A : RankedSet} (G : FiniteSystem A 0) (hG : Unary G)
    (B : System A 0) (hB : Unary (ofSetSystem B.val)) (v : G.Vertex)
    (f : FiniteMorphisms.Morphism (ofSetSystem B.val) (startAt G v))
    (u : G.Vertex) (hp : Relation.ReflTransGen G.graph.Step u v) :
    ∃ C : System A 0, Unary (ofSetSystem C.val) ∧
      Nonempty (FiniteMorphisms.Morphism (ofSetSystem C.val) (startAt G u)) ∧
      Nonempty (FiniteMorphisms.Morphism (unmark (ofSetSystem B.val)) (ofSetSystem C.val)) := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exact ⟨B, hB, ⟨f⟩, ⟨{
      toFun := id, label := fun _ => rfl, initial := fun _ => False.elim,
      root := fun _ => False.elim, edge := by intro v d t h; cases t <;> exact h }⟩⟩
  | @head u w huw hp ih =>
    obtain ⟨C, hC, ⟨g⟩, ⟨t⟩⟩ := ih
    obtain ⟨d, hd⟩ := huw
    have hvalid := G.graph.direction_valid u d _ hd
    have hrank : (G.graph.label u).1 = 1 := by have hu := hG u; omega
    have hd0 : d = 0 := by omega
    subst d
    exact ⟨prepend (G.graph.label u) hrank C, prepend_unary _ hrank C hC,
      ⟨prepend_map G u w hrank hd C g⟩,
      ⟨compose (unmarked_map (S := unmark (ofSetSystem B.val)) t) (prepend_tail (G.graph.label u) hrank C)⟩⟩


noncomputable def tail {A : RankedSet} (P : FiniteSystem A 0) (ht : Complete P)
    (v : P.Vertex) : FiniteSystem A 0 :=
  let B := fromVertex P ht v
  ⟨B.val.size, {B.val.graph with initial := fun w => P.graph.initial v ∧ B.val.graph.initial w}⟩

private noncomputable def fromVertex_map {A : RankedSet} (P : FiniteSystem A 0) (ht : Complete P)
    (v : P.Vertex) : FiniteMorphisms.Morphism (ofSetSystem (fromVertex P ht v).val) (startAt P v) :=
  let f := FiniteAcceptance.trimProjection (startAt P v).graph
  ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩

private noncomputable def tailMap {A : RankedSet} (P : FiniteSystem A 0) (ht : Complete P)
    (v : P.Vertex) : FiniteMorphisms.Morphism (tail P ht v) P where
  toFun := (fromVertex_map P ht v).toFun
  label := (fromVertex_map P ht v).label
  initial := by
    intro w hw
    have he : (fromVertex_map P ht v).toFun w = v := (fromVertex_map P ht v).initial w hw.2
    rw [he]
    exact hw.1
  root := by intro w hw; have hr := (fromVertex_map P ht v).root w hw; exact False.elim hr
  edge := (fromVertex_map P ht v).edge

private noncomputable def jointCover {A : RankedSet} (P : FiniteSystem A 0) (ht : Complete P)
    (hr : P.graph.root = ∅) : Lax369799.FiniteCoverFamilies.JointCover (tail P ht) P where
  map := tailMap P ht
  edges := fun v w d t h => (FiniteAcceptance.trimProjection (startAt P v).graph).edge_lift w d t h
  vertices := by
    intro v
    have hv : (startAt P v).graph.Reachable v := ⟨v, Or.inl rfl, .refl⟩
    refine ⟨v, index (startAt P v).graph ⟨v, hv⟩, ?_⟩
    exact vertex_index _ _ _
  initials := by
    intro v hv
    have hr : (startAt P v).graph.Reachable v := ⟨v, Or.inl rfl, .refl⟩
    refine ⟨v, index (startAt P v).graph ⟨v, hr⟩, ⟨hv, ?_⟩, vertex_index _ _ _⟩
    change (startAt P v).graph.initial (vertex _ (index _ _))
    rw [vertex_index]
    rfl
  roots := by intro v hv; rw [hr] at hv; exact False.elim hv

private def start_inclusion {A : RankedSet} (P : FiniteSystem A 0) (v : P.Vertex)
    (hv : P.graph.initial v) : FiniteMorphisms.Morphism (startAt P v) P where
  toFun := id
  label := fun _ => rfl
  initial := by intro w hw; change w = v at hw; change P.graph.initial w; rw [hw]; exact hv
  root := fun _ => False.elim
  edge := by intro w d t h; cases t <;> exact h

private def chosen_inclusion {A : RankedSet} (P : FiniteSystem A 0)
    (f : P.Vertex → P.Vertex) (v : P.Vertex) :
    FiniteMorphisms.Morphism (startAt (GraphChoices.chooseRows P Finset.univ f) v) (startAt P v) where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ => False.elim
  edge := by intro w d t h; cases t <;> exact h.1

private theorem chosen_complete {A : RankedSet} (P : FiniteSystem A 0) (hu : Unary P)
    (ht : ∀ v, (P.graph.label v).1 = 1 → ∃ w, P.graph.edge v 0 (.inl w))
    (f : P.Vertex → P.Vertex) (hf : GraphChoices.Admissible P f) :
    Complete (GraphChoices.chooseRows P Finset.univ f) := by
  intro v d hd
  have hv := hu v
  have hd' : d < (P.graph.label v).1 := hd
  have hv1 : (P.graph.label v).1 = 1 := by omega
  have hd0 : d = 0 := by omega
  subst d
  obtain ⟨w, hw⟩ := ht v hv1
  obtain ⟨e, he⟩ := hf v ⟨0, w, hw⟩
  have hevalid := P.graph.direction_valid v e _ he
  have he0 : e = 0 := by omega
  subst e
  refine ⟨.inl (f v), ⟨he, fun _ => rfl⟩, ?_⟩
  intro t h
  exact (GraphChoices.chosen_functional P f v 0 _ _ h ⟨he, fun _ => rfl⟩)

private theorem fromVertex_unary {A : RankedSet} (P : FiniteSystem A 0) (hu : Unary P)
    (ht : Complete P) (v : P.Vertex) : Unary (ofSetSystem (fromVertex P ht v).val) := by
  intro w
  exact hu (vertex (startAt P v).graph (by exact w))

private theorem tails_accepted {A : RankedSet} (L : Algebras.Language A)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) (G : FiniteSystem (Carrier (Accepting L)) 0)
    (hu : Unary G) (hr : G.graph.root = ∅) (hreach : FinitePresentations.Reachable G)
    (ht : ∀ v, (G.graph.label v).1 = 1 → ∃ w, G.graph.edge v 0 (.inl w))
    (hbranch : ∀ B : System (Carrier (Accepting L)) 0, Unary (ofSetSystem B.val) →
      Nonempty (FiniteMorphisms.Morphism (ofSetSystem B.val) G) →
      AcceptingClass (Accepting L) (E.algebra.eval 0 (ofSetSystem B.val)))
    (f : G.Vertex → G.Vertex) (hf : GraphChoices.Admissible G f) (v : G.Vertex) :
    AcceptingClass (Accepting L) (E.algebra.eval 0
      (tail (GraphChoices.chooseRows G Finset.univ f) (chosen_complete G hu ht f hf) v)) := by
  let H := GraphChoices.chooseRows G Finset.univ f
  let hc := chosen_complete G hu ht f hf
  let B := fromVertex H hc v
  let T := tail H hc v
  have hB : Unary (ofSetSystem B.val) := fromVertex_unary H hu hc v
  have base := compose (fromVertex_map H hc v) (chosen_inclusion G f v)
  have hup := (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)).2
  by_cases hv : G.graph.initial v
  · have hacc := hbranch B hB ⟨compose base (start_inclusion G v hv)⟩
    let m : FiniteMorphisms.Morphism T (ofSetSystem B.val) := {
      toFun := id, label := fun _ => rfl, initial := fun _ h => h.2,
      root := fun _ h => h, edge := by intro w d t h; cases t <;> exact h }
    exact hup _ _ hacc (FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates m)
  · obtain ⟨u, hinit, hp⟩ := hreach v
    have huinit : G.graph.initial u := hinit.elim id (fun h => by rw [hr] at h; exact False.elim h)
    obtain ⟨C, hC, ⟨g⟩, ⟨t⟩⟩ := extend G hu B hB v base u hp
    have hacc := hbranch C hC ⟨compose g (start_inclusion G u huinit)⟩
    let m : FiniteMorphisms.Morphism T (unmark (ofSetSystem B.val)) := {
      toFun := id, label := fun _ => rfl,
      initial := fun _ h => False.elim (hv h.1),
      root := by intro w h; change B.val.graph.root w at h; rw [B.property.2.1] at h; exact False.elim h,
      edge := by intro w d t h; cases t <;> exact h }
    exact hup _ _ hacc (FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates (compose m t))


/--
---
conclusion: Lax369799.ExtremalPaths.selected_path_criterion
---
Split outgoing choices until the presentation is functional. Cover each
restriction by its rooted branches and by unmarked tails from every
other vertex. Reachability in the original graph extends each such tail
to a regular branch, using a finite prefix. Surjectivity of the covering
family retains every vertex through substitution. The empty graph is
accepted by the empty-yield test.
-/
theorem selected_path_criterion {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) (G : FiniteSystem (Carrier (Accepting L)) 0)
    (hu : Unary G) (hr : G.graph.root = ∅) (hreach : FinitePresentations.Reachable G)
    (ht : ∀ v, (G.graph.label v).1 = 1 → ∃ w, G.graph.edge v 0 (.inl w))
    (hs : ∀ v (h : (G.graph.label v).1 = 1),
      ExtremalUnaryTypes.Selected L E (h ▸ (G.graph.label v).2)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 G) ↔
      ∀ B : System (Carrier (Accepting L)) 0, Unary (ofSetSystem B.val) →
        Nonempty (FiniteMorphisms.Morphism (ofSetSystem B.val) G) →
        AcceptingClass (Accepting L) (E.algebra.eval 0 (ofSetSystem B.val)) := by
  constructor
  · intro h B _ hm
    obtain ⟨m⟩ := hm
    exact (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
      (FiniteAcceptance.accepting_isomorphic L)).2 _ _ h
      (FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates m)
  · intro hbranch
    by_cases hsize : G.size = 0
    · let F := Accepting L
      let rep : RankedSystems.RankedMap (Carrier F) (FiniteSystem A) := fun _ a => a.out
      let Q := relabel rep G
      have hzero (v : Q.Vertex) : False := by have hv := v.isLt; change v.val < G.size at hv; omega
      let m : Map (flattenPresentation Q.graph) (empty A 0).graph := {
        toFun := fun v => False.elim (hzero v.1)
        initial := fun v _ => False.elim (hzero v.1)
        root := fun v _ => False.elim (hzero v.1)
        label := fun v => False.elim (hzero v.1)
        edge := fun v _ _ _ => False.elim (hzero v.1) }
      have ha := FiniteMorphisms.accepting_morphism L (FiniteMorphisms.fromEnumeration m)
        (FiniteAcceptance.accepting_empty L)
      have he := FiniteSyntacticAlgebra.evaluation_by_representatives F E.algebra E.evaluates G
      rw [he]
      exact (FiniteSyntacticAlgebra.accepting_classes F (FiniteAcceptance.accepting_isomorphic L)).1 _ |>.mpr ha
    · let : Finite (Carrier (Accepting L) 0) :=
        BoundedProfileRefinement.finite_carrier_recognizable L hL hrec 0
      apply (GraphChoices.admissible_test L E G hu hs).mpr
      intro f hf
      let H := GraphChoices.chooseRows G Finset.univ f
      let hc := chosen_complete G hu ht f hf
      exact FiniteCoverFamilies.acceptance L E (Nat.pos_of_ne_zero hsize) (tail H hc) H
        (jointCover H hc hr) (tails_accepted L E G hu hr hreach ht hbranch f hf)

/--
---
conclusion: Lax369799.ExtremalPaths.path_criterion
---
Every extremal unary value is selected by its own split witness. Apply
choice splitting and the regular-branch criterion for selected values.
-/
theorem path_criterion {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) (G : FiniteSystem (Carrier (Accepting L)) 0)
    (hu : Unary G) (hr : G.graph.root = ∅) (hreach : FinitePresentations.Reachable G)
    (ht : ∀ v, (G.graph.label v).1 = 1 → ∃ w, G.graph.edge v 0 (.inl w))
    (hs : ∀ v (h : (G.graph.label v).1 = 1),
      ExtendedContexts.ExtremalElement L E (h ▸ (G.graph.label v).2)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 G) ↔
      ∀ B : System (Carrier (Accepting L)) 0, Unary (ofSetSystem B.val) →
        Nonempty (FiniteMorphisms.Morphism (ofSetSystem B.val) G) →
        AcceptingClass (Accepting L) (E.algebra.eval 0 (ofSetSystem B.val)) :=
  selected_path_criterion L hL hrec E G hu hr hreach ht (fun v h =>
    ExtremalSituations.unary_selected L E _ ((ExtendedContexts.element_iff L E _).mp (hs v h)))

/--
---
conclusion: Lax369799.ExtremalPaths.syntactic_automaton_property
---
Combine canonical direction decomposition, extremality of each direction,
and the regular-branch path criterion.
-/
theorem syntactic_automaton_property {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) : Lax369799.ExtremalPaths.HasAutomatonProperty L E := by
  refine ⟨?_, ?_⟩
  · intro k hk a ha
    exact ⟨DirectionProjections.extremal_decomposition L E hk a ha,
      DirectionProjections.extremal_direction L hL hrec E a ha⟩
  · intro G hu hr hreach ht hs
    have h := path_criterion L hL hrec E G hu hr hreach ht hs
    exact h.trans ⟨fun hb B hB => hb B hB.1 hB.2, fun hb B hu hm => hb B ⟨hu, hm⟩⟩

end Lax369799Proofs.ExtremalPaths


