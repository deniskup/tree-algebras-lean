import Lax369799.RunAcceptance
import Lax369799Proofs.AlgebraicBranchCondition
import Lax369799Proofs.RunPresentations
import Lax369799Proofs.RunBranchObservations
import Lax369799Proofs.RegularBranchWords
import Lax369799Proofs.UnarySystemEvaluation
import Lax369799Proofs.ExtremalPaths

namespace Lax369799Proofs.RunAcceptance
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet System)
open FinitePresentations FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra
open ExpandedSyntacticAlgebra UnfoldAutomata ExpandedTransitions RunPresentations
open Lax369799.RunAcceptance

variable {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S)

private abbrev Raw := (v : S.val.Vertex) × (piece L E D r.toLabelling v).Vertex
private noncomputable abbrev rawGraph := flattenPresentation (withLabels (ofSetSystem S.val) (piece L E D r.toLabelling)).graph

private structure PieceData (v : S.val.Vertex) (P : FiniteSystem (Carrier (Accepting L)) (Rank S v)) where
  initial : ∀ u, P.graph.initial u
  root : ∀ u, ¬ P.graph.root u
  point : P.Vertex
  direction : ∀ u, (P.graph.label u).1 = 1 → Fin (Rank S v)
  label : ∀ u h, P.graph.label u = ⟨1,
    (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v (direction u h))⟩
  nullary_rank : ∀ u, (P.graph.label u).1 = 0 → Rank S v = 0
  nullary_label : ∀ u h, P.graph.label u = ⟨0,
    (Fintype.equivFin (Carrier (Accepting L) 0)).symm (r.leafType v (nullary_rank u h))⟩
  internal : ∀ u z d, ¬ P.graph.edge u d (.inl z)
  port_edge : ∀ u h d i, P.graph.edge u d (.inr i) ↔ d = 0 ∧ i = direction u h
  port : ∀ i, ∃ u h, direction u h = i

private theorem sigma_cast {Y : RankedSet} {n m : ℕ} (h : n = m) (a : Y m) :
    (⟨n, h.symm ▸ a⟩ : RankedSystems.Symbol Y) = ⟨m, a⟩ := by cases h; rfl

private theorem leaf_symbol (v : S.val.Vertex) (h : Rank S v = 0) :
    (⟨Rank S v, runLabel L E D r.toLabelling v⟩ : RankedSystems.Symbol (Carrier (Accepting L))) =
      ⟨0, (Fintype.equivFin (Carrier (Accepting L) 0)).symm (r.leafType v h)⟩ := by
  unfold runLabel
  rw [dif_pos h]
  exact sigma_cast h _

private noncomputable def pieceData (v : S.val.Vertex) : PieceData L E D r v (piece L E D r.toLabelling v) := by
  unfold piece
  split_ifs with hv
  · refine {
      initial := fun _ => True.intro
      root := fun _ => id
      point := (0 : Fin 1)
      direction := ?_
      label := ?_
      nullary_rank := fun _ _ => hv
      nullary_label := ?_
      internal := ?_
      port_edge := ?_
      port := ?_ }
    · intro u h
      change Rank S v = 1 at h
      omega
    · intro u h
      change Rank S v = 1 at h
      omega
    · intro u h
      exact leaf_symbol L E D r v hv
    · rintro u z d ⟨j, _, he⟩
      cases he
    · intro u h
      change Rank S v = 1 at h
      omega
    · intro i
      have := i.isLt
      omega
  · refine {
      initial := fun _ => True.intro
      root := fun _ => id
      point := (⟨0, Nat.pos_of_ne_zero hv⟩ : Fin (Rank S v))
      direction := fun u _ => u
      label := fun _ _ => rfl
      nullary_rank := ?_
      nullary_label := ?_
      internal := ?_
      port_edge := ?_
      port := fun i => ⟨i, rfl, rfl⟩ }
    · intro u h
      change 1 = 0 at h
      omega
    · intro u h
      change 1 = 0 at h
      omega
    · intro u z d h
      cases h.2
    · intro u h d i
      exact ⟨fun h => ⟨h.1, Sum.inr.inj h.2⟩,
        fun h => ⟨h.1, congrArg Sum.inr h.2⟩⟩

private theorem piece_initial (v : S.val.Vertex) : ∀ u : (piece L E D r.toLabelling v).Vertex, (piece L E D r.toLabelling v).graph.initial u := (pieceData L E D r v).initial
private theorem piece_root (v : S.val.Vertex) : ∀ u : (piece L E D r.toLabelling v).Vertex, ¬ (piece L E D r.toLabelling v).graph.root u := (pieceData L E D r v).root
private noncomputable def piecePoint (v : S.val.Vertex) := (pieceData L E D r v).point
private noncomputable def pieceDirection (v : S.val.Vertex) := (pieceData L E D r v).direction
private theorem direction_label (v : S.val.Vertex) : ∀ (u : (piece L E D r.toLabelling v).Vertex) h, (piece L E D r.toLabelling v).graph.label u = ⟨1, (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v (pieceDirection L E D r v u h))⟩ := (pieceData L E D r v).label
private theorem piece_internal (v : S.val.Vertex) : ∀ (u z : (piece L E D r.toLabelling v).Vertex) d, ¬ (piece L E D r.toLabelling v).graph.edge u d (.inl z) := (pieceData L E D r v).internal
private theorem piece_variable (v : S.val.Vertex) : ∀ (u : (piece L E D r.toLabelling v).Vertex) h d i, (piece L E D r.toLabelling v).graph.edge u d (.inr i) ↔ d = 0 ∧ i = pieceDirection L E D r v u h := (pieceData L E D r v).port_edge

private theorem raw_edge (v w : Raw L E D r)
    (h : ((rawGraph L E D r).label v).1 = 1) (d : ℕ) :
    (rawGraph L E D r).edge v d (.inl w) ↔ d = 0 ∧
      S.val.graph.edge v.1 (pieceDirection L E D r v.1 v.2 h).val (.inl w.1) := by
  change ((∃ z, (piece L E D r.toLabelling v.1).graph.edge v.2 d (.inl z) ∧ _) ∨
    ∃ i, (piece L E D r.toLabelling v.1).graph.edge v.2 d (.inr i) ∧
      ((∃ q : Raw L E D r, S.val.graph.edge v.1 i.val (.inl q.1) ∧
        (piece L E D r.toLabelling q.1).graph.initial q.2 ∧ (.inl w : Raw L E D r ⊕ Fin 0) = .inl q) ∨
       (∃ j, S.val.graph.edge v.1 i.val (.inr j) ∧ (.inl w : Raw L E D r ⊕ Fin 0) = .inr j))) ↔ _
  simp only [piece_internal, false_and, exists_false, false_or, piece_variable L E D r v.1 v.2 h,
    piece_initial, and_true, Sum.inl.injEq, Sum.inl_ne_inr, and_false, or_false]
  constructor
  · rintro ⟨i, ⟨hd, rfl⟩, q, he, hq⟩
    rcases hq with ⟨_, rfl⟩
    exact ⟨hd, he⟩
  · rintro ⟨rfl, he⟩
    exact ⟨pieceDirection L E D r v.1 v.2 h, ⟨rfl, rfl⟩, w, he, True.intro, rfl⟩


private theorem raw_initial (v : Raw L E D r) :
    (rawGraph L E D r).initial v ↔ S.val.graph.initial v.1 :=
  and_iff_left (piece_initial L E D r v.1 v.2)

private theorem raw_root (v : Raw L E D r) : ¬ (rawGraph L E D r).root v := by
  rintro (h | h)
  · exact piece_root L E D r v.1 v.2 h
  · have hs := h.1
    change S.val.graph.root v.1 at hs
    rw [S.property.2.1] at hs
    exact hs.elim

private theorem raw_nonblocked (v : Raw L E D r) (h : ((rawGraph L E D r).label v).1 = 1) :
    ∃ w, (rawGraph L E D r).edge v 0 (.inl w) := by
  let i := pieceDirection L E D r v.1 v.2 h
  obtain ⟨t, ht, _⟩ := S.property.2.2 v.1 i.val i.isLt
  cases t with
  | inr j => exact Fin.elim0 j
  | inl w =>
    exact ⟨⟨w, piecePoint L E D r w⟩, (raw_edge L E D r v _ h 0).mpr ⟨rfl, ht⟩⟩

private theorem raw_reachable : ∀ v : Raw L E D r, (rawGraph L E D r).Reachable v := by
  rintro ⟨v, u⟩
  obtain ⟨a, ha, hp⟩ := S.val.reachable v
  have hainit : S.val.graph.initial a := ha.elim id (fun h => by rw [S.property.2.1] at h; exact h.elim)
  have hfor : ∀ z : (piece L E D r.toLabelling v).Vertex, (rawGraph L E D r).Reachable ⟨v, z⟩ := by
    clear u
    induction hp with
    | refl => intro z; exact ⟨⟨a, z⟩, Or.inl ((raw_initial L E D r _).mpr hainit), .refl⟩
    | @tail y z hp hyz ih =>
      intro zcopy
      obtain ⟨d, hd⟩ := hyz
      let i : Fin (Rank S y) := ⟨d, S.val.graph.direction_valid _ _ _ hd⟩
      obtain ⟨ucopy, hu, hdir⟩ := (pieceData L E D r y).port i
      obtain ⟨a', ha', hp'⟩ := ih ucopy
      refine ⟨a', ha', hp'.tail ⟨0, ?_⟩⟩
      apply (raw_edge L E D r ⟨y, ucopy⟩ ⟨z, zcopy⟩ hu 0).mpr
      rw [show pieceDirection L E D r y ucopy hu = i from hdir]
      exact ⟨rfl, hd⟩
  exact hfor u

/--
---
conclusion: Lax369799.RunAcceptance.shape
---
Every inserted vertex is initial in its piece. Lift input paths to the
flattening; all input directions have corresponding unary copies.
-/
theorem shape :
    (presentation L E D r.toLabelling).graph.root = ∅ ∧ Reachable (presentation L E D r.toLabelling) ∧
      ∀ v, ((presentation L E D r.toLabelling).graph.label v).1 = 1 →
        ∃ w, (presentation L E D r.toLabelling).graph.edge v 0 (.inl w) := by
  let e := Fintype.equivFin (Raw L E D r)
  let iso := UntrimmedFlattening.reindexIso (rawGraph L E D r) e
  refine ⟨?_, ?_, ?_⟩
  · ext v
    change (rawGraph L E D r).root (e.symm v) ↔ False
    exact ⟨fun h => raw_root L E D r _ h, False.elim⟩
  · intro v
    let f : Pullbacks.Map (rawGraph L E D r) (presentation L E D r.toLabelling).graph := {
      toFun := e
      label := iso.label
      initial := fun u h => (iso.initial u).mpr h
      root := fun u h => (iso.root u).mpr h
      edge := fun u d t h => (iso.edge u d t).mpr h }
    have h := Pullbacks.reachable_map f (raw_reachable L E D r (e.symm v))
    simpa only [f, e.apply_symm_apply] using h
  · intro v h
    obtain ⟨w, hw⟩ := raw_nonblocked L E D r (e.symm v) h
    refine ⟨e w, ?_⟩
    change (rawGraph L E D r).edge (e.symm v) 0 (.inl (e.symm (e w)))
    simpa only [e.symm_apply_apply] using hw

private structure Projection where
  vertex : (presentation L E D r.toLabelling).Vertex → S.val.Vertex
  direction : ∀ v, ((presentation L E D r.toLabelling).graph.label v).1 = 1 → Fin (Rank S (vertex v))
  leaf : ∀ v, ((presentation L E D r.toLabelling).graph.label v).1 = 0 → Rank S (vertex v) = 0
  initial : ∀ v, (presentation L E D r.toLabelling).graph.initial v → S.val.graph.initial (vertex v)
  edge : ∀ v w h, (presentation L E D r.toLabelling).graph.edge v 0 (.inl w) →
    S.val.graph.edge (vertex v) (direction v h).val (.inl (vertex w))
  unary_label : ∀ v h, (presentation L E D r.toLabelling).graph.label v =
    ⟨1, (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType (vertex v) (direction v h))⟩
  nullary_label : ∀ v h, (presentation L E D r.toLabelling).graph.label v =
    ⟨0, (Fintype.equivFin (Carrier (Accepting L) 0)).symm (r.leafType (vertex v) (leaf v h))⟩

private noncomputable def projection : Projection L E D r where
  vertex := fun v => ((Fintype.equivFin (Raw L E D r)).symm v).1
  direction := fun v h => pieceDirection L E D r _ _ h
  leaf := fun v h => (pieceData L E D r _).nullary_rank _ h
  initial := fun v h => (raw_initial L E D r _).mp h
  edge := fun v w h he => ((raw_edge L E D r _ _ h 0).mp he).2
  unary_label := fun v h => direction_label L E D r _ _ h
  nullary_label := fun v h => (pieceData L E D r _).nullary_label _ h


section Branches
variable {B : System (Carrier (Accepting L)) 0}
    (hu : UnarySystemEvaluation.Unary B)
    (f : FiniteMorphisms.Morphism (ofSetSystem B.val) (presentation L E D r.toLabelling))
    (p : Projection L E D r)

private theorem one {Y : RankedSet} {T : System Y 0} (hu : UnarySystemEvaluation.Unary T)
    (v : T.val.Vertex) (d : Fin (Rank T v)) : Rank T v = 1 := by
  have := hu v
  have := d.isLt
  omega

private theorem mapped_rank (v : B.val.Vertex) :
    ((presentation L E D r.toLabelling).graph.label (f.toFun v)).1 = Rank B v :=
  congrArg Sigma.fst (f.label v)

private theorem edgeMap (v w : B.val.Vertex) (d : Fin (Rank B v))
    (h : B.val.graph.edge v d.val (.inl w)) :
    S.val.graph.edge (p.vertex (f.toFun v))
      (p.direction (f.toFun v) ((mapped_rank L E D r f v).trans (one hu v d))).val
      (.inl (p.vertex (f.toFun w))) := by
  have hd : d.val = 0 := by have := d.isLt; have := hu v; omega
  apply p.edge
  simpa only [hd, Sum.map_inl] using f.edge v d.val (.inl w) h

private def finiteBranch (hu : UnarySystemEvaluation.Unary B)
    (f : FiniteMorphisms.Morphism (ofSetSystem B.val) (presentation L E D r.toLabelling))
    (p : Projection L E D r) {k : ℕ} (b : FiniteBranch B k) : FiniteBranch S k where
  vertex := fun i => p.vertex (f.toFun (b.vertex i))
  direction := fun i => p.direction (f.toFun (b.vertex i.castSucc))
    ((mapped_rank L E D r f _).trans (one hu _ (b.direction i)))
  starts := p.initial _ (f.initial _ b.starts)
  follows := fun i => edgeMap L E D r hu f p _ _ (b.direction i) (b.follows i)
  ends := p.leaf _ ((mapped_rank L E D r f _).trans b.ends)

private def infiniteBranch (hu : UnarySystemEvaluation.Unary B)
    (f : FiniteMorphisms.Morphism (ofSetSystem B.val) (presentation L E D r.toLabelling))
    (p : Projection L E D r) (b : InfiniteBranch B) : InfiniteBranch S where
  vertex := fun n => p.vertex (f.toFun (b.vertex n))
  direction := fun n => p.direction (f.toFun (b.vertex n))
    ((mapped_rank L E D r f _).trans (one hu _ (b.direction n)))
  starts := p.initial _ (f.initial _ b.starts)
  follows := fun n => edgeMap L E D r hu f p _ _ (b.direction n) (b.follows n)

private theorem cast_label {Y : RankedSet} (s : RankedSystems.Symbol Y) {n : ℕ} (h : s.1 = n) :
    (⟨n, h ▸ s.2⟩ : RankedSystems.Symbol Y) = s := by cases s; cases h; rfl

private theorem unary_mapped (v : B.val.Vertex) (d : Fin (Rank B v)) :
    UnarySystemEvaluation.unaryLabel hu v d =
      (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType (p.vertex (f.toFun v))
        (p.direction (f.toFun v) ((mapped_rank L E D r f v).trans (one hu v d)))) := by
  have hs : (⟨1, UnarySystemEvaluation.unaryLabel hu v d⟩ : RankedSystems.Symbol (Carrier (Accepting L))) =
      ⟨1, (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType (p.vertex (f.toFun v))
        (p.direction (f.toFun v) ((mapped_rank L E D r f v).trans (one hu v d))))⟩ :=
    (cast_label _ (one hu v d)).trans ((f.label v).symm.trans
      (p.unary_label (f.toFun v) ((mapped_rank L E D r f v).trans (one hu v d))))
  exact eq_of_heq (Sigma.mk.inj hs).2

private theorem leaf_mapped (v : B.val.Vertex) (h : Rank B v = 0) :
    (h ▸ (B.val.graph.label v).2) =
      (Fintype.equivFin (Carrier (Accepting L) 0)).symm (r.leafType (p.vertex (f.toFun v))
        (p.leaf (f.toFun v) ((mapped_rank L E D r f v).trans h))) := by
  have hs : (⟨0, h ▸ (B.val.graph.label v).2⟩ : RankedSystems.Symbol (Carrier (Accepting L))) =
      ⟨0, (Fintype.equivFin (Carrier (Accepting L) 0)).symm (r.leafType (p.vertex (f.toFun v))
        (p.leaf (f.toFun v) ((mapped_rank L E D r f v).trans h)))⟩ :=
    (cast_label _ h).trans ((f.label v).symm.trans
      (p.nullary_label (f.toFun v) ((mapped_rank L E D r f v).trans h)))
  exact eq_of_heq (Sigma.mk.inj hs).2

private theorem finite_word {k : ℕ} (b : FiniteBranch B k) :
    UnarySystemEvaluation.finiteWord hu b =
      (List.ofFn (fun i => r.edgeType ((finiteBranch L E D r hu f p b).vertex i.castSucc)
        ((finiteBranch L E D r hu f p b).direction i))).map
          (Fintype.equivFin (Carrier (Accepting L) 1)).symm := by
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact unary_mapped L E D r hu f p _ (b.direction i)

private theorem finite_leaf {k : ℕ} (b : FiniteBranch B k) :
    UnarySystemEvaluation.leafValue b =
      (Fintype.equivFin (Carrier (Accepting L) 0)).symm
        (r.leafType ((finiteBranch L E D r hu f p b).vertex (Fin.last k))
          (finiteBranch L E D r hu f p b).ends) :=
  leaf_mapped L E D r f p _ b.ends

private theorem infinite_word (b : InfiniteBranch B) :
    UnarySystemEvaluation.infiniteWord hu b =
      fun n => (Fintype.equivFin (Carrier (Accepting L) 1)).symm
        (r.edgeType ((infiniteBranch L E D r hu f p b).vertex n)
          ((infiniteBranch L E D r hu f p b).direction n)) := by
  funext n
  exact unary_mapped L E D r hu f p _ (b.direction n)

end Branches

/--
---
conclusion: Lax369799.RunAcceptance.accepting_run_value
---
Project each regular branch of the unary run presentation into the
input run. Word correctness and branch evaluation give acceptance of
every regular branch; choice splitting gives acceptance of the graph.
-/
theorem accepting_run_value (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (hD : WordCorrect L E D) (hr : r.Accepting) :
    AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling))) := by
  rw [← RunPresentations.evaluation L E D r.toLabelling]
  obtain ⟨hroot, hreach, htotal⟩ := shape L E D r
  apply (ExtremalPaths.selected_path_criterion L hL hrec E (presentation L E D r.toLabelling)
    (RunPresentations.unary L E D r.toLabelling) hroot hreach htotal (RunPresentations.selected L E D r)).mpr
  intro B hu hm
  obtain ⟨f⟩ := hm
  obtain ⟨ES, hES⟩ := SetSystemAlgebras.syntactic_structure L E
  have ht := UnarySystemEvaluation.agreement ES {a | AcceptingClass (Accepting L) a} B hu
  change AcceptingClass (Accepting L) (ES.toAlgebra.eval 0 (ofSetSystem B.val)) ↔ _ at ht
  rw [hES] at ht
  apply ht.mpr
  constructor
  · intro k b
    let p := projection L E D r
    have hh := (hD.1 _ _).mp (hr.1 k (finiteBranch L E D r hu f p b))
    rw [← finite_word L E D r hu f p b, ← finite_leaf L E D r hu f p b] at hh
    exact hh
  · intro b
    let p := projection L E D r
    have hh := (hD.2 _).mp (hr.2 (infiniteBranch L E D r hu f p b))
    rw [← infinite_word L E D r hu f p b] at hh
    exact hh


section
variable (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)

private theorem regular_word (hD : WordCorrect L E D)
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r))))
    (b : RunBranchObservations.RegularBranch S) :
    D.AcceptsInfinite (fun n => r.edgeType ((RegularBranchWords.trace b).vertex n)
      ((RegularBranchWords.trace b).direction n)) := by
  classical
  let V := {v : Fin b.size // ∃ n, RegularBranchWords.position b n = v}
  let nxt : V → V := fun v => ⟨b.next v.val, by
    obtain ⟨n, hn⟩ := v.property
    exact ⟨n + 1, by change b.next (RegularBranchWords.position b n) = b.next v.val; rw [hn]⟩⟩
  let start : V := ⟨b.start, 0, rfl⟩
  let lab := fun v : Fin b.size => (Fintype.equivFin (Carrier (Accepting L) 1)).symm
    (r.edgeType (b.vertex v) (b.direction v))
  let H := UnaryGraphEvaluation.graph nxt start (fun v => lab v.val)
  let G := RunBranchObservations.regularPath L E D r b
  let g : Pullbacks.Map H G.graph := {
    toFun := Subtype.val
    initial := by intro v hv; change v = start at hv; subst v; rfl
    root := by intro _ h; exact h.elim
    label := fun _ => rfl
    edge := by rintro v d t ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩ }
  have haccG := RunBranchObservations.regularPath_accepting L E D r hr b
  have haccH := (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)).2 _ _ haccG
      (FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates (FiniteMorphisms.fromEnumeration g))
  have htrace (n : ℕ) : (UnaryGraphEvaluation.trace nxt start n).val = RegularBranchWords.position b n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg b.next ih
  have hreach (v : V) : ∃ n, UnaryGraphEvaluation.trace nxt start n = v := by
    obtain ⟨n, hn⟩ := v.property
    exact ⟨n, Subtype.ext ((htrace n).trans hn)⟩
  obtain ⟨ES, hES⟩ := SetSystemAlgebras.syntactic_structure L E
  have ht := UnaryGraphEvaluation.agreement ES {a | AcceptingClass (Accepting L) a} nxt start
    (fun v => lab v.val) hreach
  change AcceptingClass (Accepting L) (ES.toAlgebra.eval 0 (enumerate H)) ↔ _ at ht
  rw [hES] at ht
  have homega := ht.mp haccH
  apply (hD.2 _).mpr
  have hw : (fun v => lab v.val) ∘ UnaryGraphEvaluation.trace nxt start =
      fun n => (Fintype.equivFin (Carrier (Accepting L) 1)).symm
        (r.edgeType ((RegularBranchWords.trace b).vertex n) ((RegularBranchWords.trace b).direction n)) := by
    funext n
    exact congrArg lab (htrace n)
  simpa only [hw] using homega

/--
---
conclusion: Lax369799.RunAcceptance.labelling_accepting
---
Finite branch observations have accepted values. For a regular infinite
branch restrict to its reachable orbit, apply graph evaluation, and use
the periodic branch test to obtain acceptance on all infinite branches.
-/
theorem labelling_accepting (hD : WordCorrect L E D)
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r)))) : r.Accepting D := by
  constructor
  · intro k b
    have h := RunBranchObservations.path_accepting L E D r hr b
    rw [RunBranchObservations.path_evaluation L E D r b] at h
    apply (hD.1 _ _).mpr
    simpa only [List.map_ofFn, Function.comp_def, Labelling.asRun] using h
  · apply (RegularBranchWords.regular_test (unrestricted D) S (r.asRun D)).mp
    intro b
    exact regular_word L E D r hD hr b

end

/--
---
conclusion: Lax369799.RunAcceptance.evaluated_run_accepting
---
Apply the acceptance implication for arbitrary type assignments.
-/
theorem evaluated_run_accepting (hD : WordCorrect L E D)
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling)))) : r.Accepting :=
  labelling_accepting L E D r.toLabelling hD hr

/--
---
conclusion: Lax369799.RunAcceptance.evaluated_run_iff
---
Combine the two directions of the run evaluation criterion.
-/
theorem evaluated_run_iff (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (hD : WordCorrect L E D) : r.Accepting ↔
    AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling))) :=
  ⟨accepting_run_value L E D r hL hrec hD, evaluated_run_accepting L E D r hD⟩

/--
---
conclusion: Lax369799.RunAcceptance.exists_condition
---
Specialize the common finite/infinite algebraic condition to the unary
and nullary sorts of the yield-syntactic algebra.
-/
theorem exists_condition {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L) :
    ∃ D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)), WordCorrect L E D := by
  exact AlgebraicBranchCondition.exists_condition E.algebra {a | AcceptingClass (Accepting L) a}

end Lax369799Proofs.RunAcceptance
