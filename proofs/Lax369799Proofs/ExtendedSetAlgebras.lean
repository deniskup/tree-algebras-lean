import Lax369799.ExtendedSetAlgebras
import Lax369799Proofs.SetSystemAlgebras
import Lax369799Proofs.ExtendedContexts
import Lax369799Proofs.ExtendedContextDecomposition

namespace Lax369799Proofs.ExtendedSetAlgebras
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet RankedMap)
open FinitePresentations FiniteContexts
open Lax369799.SetSystemAlgebras (SetAlgebra Below)
open Lax369799.ExtendedSetAlgebras
open ExtendedContexts (Piece Pieces Marker)

private def fill {A : RankedSet} {k : ℕ} (a : A k) : RankedMap (Flattening.WithHole A k) A :=
  FiniteNormalForms.letterSubstitution a

private theorem eval_atomic {A : RankedSet} (E : SetAlgebra A) {k n : ℕ}
    (C : Context A k n) (a : A k) :
    E.eval n (plug C (atomic a)) = E.eval n (relabel (fill a) C.system) :=
  E.isomorphic n _ _ (FiniteNormalForms.plug_atomic_iso C a)

/--
---
conclusion: Lax369799.ExtendedSetAlgebras.pieces_evaluation
---
Associativity evaluates each ordinary piece first. Its marker set is
unchanged, and the atomic unit evaluates the hole label.
-/
theorem pieces_evaluation {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (p : Pieces (FiniteSystem A) k) (a : A k) :
    E.eval 0 (expansion p a) = value E (evaluatePieces E p) a := by
  let Q := relabel (fun r u => match u with
    | .inl s => s
    | .inr ⟨h⟩ => h ▸ atomic a) (ExtendedContexts.context p).system
  have he : relabel E.eval Q =
      relabel (fill a) (ExtendedContexts.context (evaluatePieces E p)).system := by
    dsimp only [Q, relabel, ExtendedContexts.context, evaluatePieces,
      ExtremalContexts.normalPresentation]
    congr 1
    congr 1
    funext v
    cases v using Fin.cases with
    | zero => change Sigma.mk k (E.eval k (atomic a)) = Sigma.mk k a; rw [E.unit]
    | succ i => rfl
  change E.eval 0 (flatten Q) = _
  rw [← E.associative, he]
  exact (eval_atomic E _ a).symm

private def markerMap {A : RankedSet} {k : ℕ} (p q : Pieces A k)
    (h : ∀ i, (q i).2 ⊆ (p i).2) (a : A k) :
    FiniteMorphisms.Morphism (relabel (fill a) (ExtendedContexts.context q).system)
      (relabel (fill a) (ExtendedContexts.context
        (fun i => ((q i).1, (p i).2))).system) where
  toFun := id
  label := fun _ => rfl
  initial := fun v hv => hv.elim Or.inl (fun hv => Or.inr ⟨hv.1, h 0 hv.2⟩)
  root := fun v hv => ⟨hv.1, by obtain ⟨i, hi⟩ := hv.2; exact ⟨i, h i hi⟩⟩
  edge := by
    intro v d t ht
    cases t with
    | inr i => exact Fin.elim0 i
    | inl w =>
      cases v using Fin.cases with
      | zero =>
        rcases ht with h' | ⟨i, hi, hd, hw⟩
        · exact Or.inl h'
        · exact Or.inr ⟨i, h i.succ hi, hd, hw⟩
      | succ i => exact ht

private theorem labels_monotone {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (p q : Pieces A k) (h : ∀ i, Below E (p i).1 (q i).1)
    (a b : A k) (hab : Below E a b) :
    Below E (E.eval 0 (relabel (fill a) (ExtendedContexts.context p).system))
      (E.eval 0 (relabel (fill b) (ExtendedContexts.context
        (fun i => ((q i).1, (p i).2))).system)) := by
  let R : RankedSet := fun n => {x : A n × A n // Below E x.1 x.2}
  let p' : Pieces R k := fun i => ⟨⟨((p i).1, (q i).1), h i⟩, (p i).2⟩
  let a' : R k := ⟨(a, b), hab⟩
  let P := relabel (fill a') (ExtendedContexts.context p').system
  have hm := SetSystemAlgebras.evaluation_monotone E P
    (fun v => (P.graph.label v).2.val.1) (fun v => (P.graph.label v).2.val.2)
    (fun v => (P.graph.label v).2.property)
  have hfirst : withLabels P (fun v => (P.graph.label v).2.val.1) =
      relabel (fill a) (ExtendedContexts.context p).system := by
    dsimp only [P, p', a', withLabels, relabel, ExtendedContexts.context,
      ExtremalContexts.normalPresentation, fill, FiniteNormalForms.letterSubstitution]
    congr 1
    congr 1
    funext v
    exact Fin.cases rfl (fun _ => rfl) v
  have hsecond : withLabels P (fun v => (P.graph.label v).2.val.2) =
      relabel (fill b) (ExtendedContexts.context
        (fun i => ((q i).1, (p i).2))).system := by
    dsimp only [P, p', a', withLabels, relabel, ExtendedContexts.context,
      ExtremalContexts.normalPresentation, fill, FiniteNormalForms.letterSubstitution]
    congr 1
    congr 1
    funext v
    exact Fin.cases rfl (fun _ => rfl) v
  rwa [hfirst, hsecond] at hm

/--
---
conclusion: Lax369799.ExtendedSetAlgebras.context_monotone
---
Increase ordinary labels first. Then delete the marker contributions
using the reverse morphism order, and compose the two comparisons.
-/
theorem context_monotone {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (p q : Pieces A k) (hpq : ∀ i, PieceBelow E (p i) (q i))
    (a b : A k) (hab : Below E a b) : Below E (value E p a) (value E q b) := by
  unfold value
  rw [eval_atomic, eval_atomic]
  have hlabels := labels_monotone E p q (fun i => (hpq i).1) a b hab
  have hmarks := E.morphism 0 _ _ ⟨markerMap p q (fun i => (hpq i).2) b⟩
  exact (SetSystemAlgebras.order_laws E 0).2.2.1 _ _ _ hlabels hmarks

private abbrev pieceOrder {A : RankedSet} (E : SetAlgebra A) : PartialOrder (Piece A) where
  le := PieceBelow E
  le_refl := fun p => ⟨(SetSystemAlgebras.order_laws E 1).1 p.1, Set.Subset.rfl⟩
  le_trans := fun _ _ _ h h' => ⟨(SetSystemAlgebras.order_laws E 1).2.2.1 _ _ _ h.1 h'.1,
    h'.2.trans h.2⟩
  le_antisymm := fun _ _ h h' => Prod.ext
    ((SetSystemAlgebras.order_laws E 1).2.1 _ _ h.1 h'.1) (Set.Subset.antisymm h'.2 h.2)

/--
---
conclusion: Lax369799.ExtendedSetAlgebras.extremal_choice
---
The finite product order includes every unary piece, both markers, and
the hole element. Choose a minimal accepted tuple below the supplied one.
-/
theorem extremal_choice {A : RankedSet} (E : SetAlgebra A) (hA : RankedSystems.RankwiseFinite A)
    (F : Set (A 0)) {k : ℕ} (p : Pieces A k) (a : A k) (ha : Accepted E F p a) :
    ∃ q b, IsExtremal E F q b ∧ (∀ i, PieceBelow E (q i) (p i)) ∧ Below E b a := by
  classical
  let : ∀ n, Finite (A n) := hA
  let := pieceOrder E
  have ho := SetSystemAlgebras.order_laws E k
  let : PartialOrder (A k) := {
    le := Below E, le_refl := ho.1, le_trans := ho.2.2.1, le_antisymm := ho.2.1 }
  let pred : Pieces A k × A k → Prop := fun x => Accepted E F x.1 x.2
  obtain ⟨⟨q, b⟩, hbelow, hacc, hmin⟩ :=
    Finite.exists_le_minimal (p := pred) (a := (p, a)) ha
  refine ⟨q, b, ⟨hacc, ?_⟩, hbelow.1, hbelow.2⟩
  intro r c hpieces hc haccepted
  have hle : (r, c) ≤ (q, b) := ⟨hpieces, hc⟩
  have he : (r, c) = (q, b) := le_antisymm hle (hmin haccepted hle)
  exact Prod.mk.inj he

/--
---
conclusion: Lax369799.ExtendedSetAlgebras.replacement
---
Decompose the given context without planting it. Minimize the whole
accepted situation, then restore its context pieces by monotonicity and
upward closure of the accepting set.
-/
theorem replacement {A : RankedSet} (E : SetAlgebra A) (hA : RankedSystems.RankwiseFinite A)
    (F : Set (A 0)) (hF : UpwardClosed E F) {k : ℕ}
    (C : Context A k 0) (a : A k) (ha : E.eval 0 (plug C (atomic a)) ∈ F) :
    ∃ b, ExtremalElement E F b ∧ Below E b a ∧ E.eval 0 (plug C (atomic b)) ∈ F := by
  obtain ⟨p, hp⟩ := ExtendedContextDecomposition.context_decomposition E C
  have hacc : Accepted E F p a := by change E.eval 0 (plug _ _) ∈ F; rw [hp]; exact ha
  obtain ⟨q, b, hb, hqp, hba⟩ := extremal_choice E hA F p a hacc
  refine ⟨b, ⟨q, hb⟩, hba, ?_⟩
  have hr := hF _ _ hb.1 (context_monotone E q p hqp b b ((SetSystemAlgebras.order_laws E k).1 b))
  change E.eval 0 (plug (ExtendedContexts.context p) (atomic b)) ∈ F at hr
  rwa [hp] at hr

/--
---
conclusion: Lax369799.ExtendedSetAlgebras.simultaneous
---
Iterate extremal replacement through every vertex. The reverse direction
uses monotonicity to restore the original labels.
-/
theorem simultaneous {A B : RankedSet} (E : SetAlgebra A) (hA : RankedSystems.RankwiseFinite A)
    (F : Set (A 0)) (hF : UpwardClosed E F) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, A (P.graph.label v).1) :
    E.eval 0 (withLabels P q) ∈ F ↔
      ∃ r : ∀ v : P.Vertex, A (P.graph.label v).1,
        (∀ v, ExtremalElement E F (r v) ∧ Below E (r v) (q v)) ∧
        E.eval 0 (withLabels P r) ∈ F := by
  constructor
  · intro hq
    exact FiniteLocalReplacement.simultaneous E.toAlgebra F
      (fun _ a b => ExtremalElement E F b ∧ Below E b a)
      (fun _ C a ha => by
        obtain ⟨b, hb, hba, hacc⟩ := replacement E hA F hF C a ha
        exact ⟨b, ⟨hb, hba⟩, hacc⟩) P q hq
  · rintro ⟨r, hr, hacc⟩
    exact hF _ _ hacc (SetSystemAlgebras.evaluation_monotone E P r q (fun v => (hr v).2))

end Lax369799Proofs.ExtendedSetAlgebras
