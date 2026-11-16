import Lax369799.ExtendedContexts
import Lax369799Proofs.ExtremalSituations

namespace Lax369799Proofs.ExtendedContexts
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra
open FiniteAcceptance ExpandedSyntacticAlgebra
open ExtremalContexts (Data)
open Lax369799.ExtendedContexts

/--
---
conclusion: Lax369799.ExtendedContexts.normalize_canonical
---
The saturated markers recover the hole's root flag and each loop.
-/
theorem normalize_canonical {A : RankedSet} {k : ℕ} (x : Data A k) :
    normalize (canonical x) = x := by
  rcases x with ⟨⟨r, s⟩, m⟩
  have hr : (r ∨ ∃ _ : Fin (k + 1), r) = r := propext ⟨fun h => h.elim id (fun h => h.choose_spec), Or.inl⟩
  change ((⟨r ∨ ∃ _ : Fin (k + 1), r, s⟩, m) : Data A k) = _
  rw [hr]

/--
---
conclusion: Lax369799.ExtendedContexts.canonical_order
---
The reversed inclusion of markers records the reversed boundary order.
-/
theorem canonical_order {A : RankedSet} (F : ClosedProperty A) {k : ℕ}
    (x : Data (Carrier F) k) (p : Pieces (Carrier F) k) :
    (∀ i, PieceBelow F (canonical x i) (p i)) ↔
      FiniteExtremal.DataBelow F x (normalize p) := by
  constructor
  · intro h
    refine ⟨?_, ?_, fun i => (h i).1⟩
    · rintro (hr | ⟨i, hr⟩)
      · exact (h 0).2 hr
      · exact (h i).2 hr
    · intro i hi
      exact (h i.succ).2 hi
  · rintro ⟨hr, hs, hm⟩ i
    refine ⟨hm i, ?_⟩
    intro marker hmarker
    cases marker with
    | root => exact hr (Or.inr ⟨i, hmarker⟩)
    | initial =>
      cases i using Fin.cases with
      | zero => exact hr (Or.inl hmarker)
      | succ j => exact hs hmarker

private def normalIso {A : RankedSet} {k : ℕ} (p : Pieces A k) :
    PresentationIso (plant (context p).system).graph
      (FiniteNormalForms.normalContext (normalize p).1 (normalize p).2).system.graph where
  vertex := Equiv.refl _
  label := fun _ => rfl
  initial := fun _ => Iff.rfl
  root := by
    intro v
    change (v = (0 : Fin (k + 1)).succ ∨
      (v = (0 : Fin (k + 2)) ∧ (Marker.initial ∈ (p 0).2 ∨ ∃ i, Marker.root ∈ (p i).2))) ↔
      ((v = (0 : Fin (k + 2)) ∧ ∃ i, Marker.root ∈ (p i).2) ∨
        (v = (0 : Fin (k + 1)).succ ∨ (v = (0 : Fin (k + 2)) ∧ Marker.initial ∈ (p 0).2)))
    tauto
  edge := by intro v d t; cases t <;> rfl

/--
---
conclusion: Lax369799.ExtendedContexts.acceptance_normalize
---
Plant the context before substitution. Its marks and edges are exactly
those of the normalized context, and planting preserves acceptance.
-/
theorem acceptance_normalize {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (p : Pieces (Carrier (Accepting L)) k)
    (a : Carrier (Accepting L) k) :
    Accepted L E p a ↔ FiniteExtremal.Accepts (Accepting L) E.algebra a (normalize p) := by
  let C := context p
  let N := FiniteNormalForms.normalContext (normalize p).1 (normalize p).2
  let S := relabel (substitution (atomic a)) C.system
  have hf : Isomorphic (flatten (plant S)) (plug N (atomic a)) :=
    UntrimmedFlattening.flatten_iso _ _
      ⟨UntrimmedFlattening.relabelIso (substitution (atomic a)) (normalIso p)⟩
  have he := E.algebra.isomorphic 0 _ _ hf
  rw [E.algebra.isomorphic 0 _ _ (FinitePlant.flatten_plant S)] at he
  change AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a))) ↔
    AcceptingClass (Accepting L) (E.algebra.eval 0 (plug N (atomic a)))
  rw [← he]
  exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).symm

private theorem data_refl {A : RankedSet} (F : ClosedProperty A) {k : ℕ}
    (x : Data (Carrier F) k) : FiniteExtremal.DataBelow F x x :=
  ⟨id, Set.Subset.rfl, fun i => (FiniteContextualOrder.class_order F 1).1 (x.2 i)⟩

private theorem normalize_monotone {A : RankedSet} (F : ClosedProperty A) {k : ℕ}
    (p q : Pieces (Carrier F) k) (h : ∀ i, PieceBelow F (p i) (q i)) :
    FiniteExtremal.DataBelow F (normalize p) (normalize q) := by
  refine ⟨?_, ?_, fun i => (h i).1⟩
  · rintro (hr | ⟨i, hr⟩)
    · exact Or.inl ((h 0).2 hr)
    · exact Or.inr ⟨i, (h i).2 hr⟩
  · intro i hi
    exact (h i.succ).2 hi

private theorem piece_antisymm {A : RankedSet} (F : ClosedProperty A)
    (p q : Piece (Carrier F)) (h : PieceBelow F p q) (h' : PieceBelow F q p) : p = q :=
  Prod.ext ((FiniteContextualOrder.class_order F 1).2.1 _ _ h.1 h'.1)
    (Set.Subset.antisymm h'.2 h.2)

/--
---
conclusion: Lax369799.ExtendedContexts.extremal_iff
---
Minimal formal data are saturated. Saturation and normalization preserve
acceptance, and their order comparison transports minimality both ways.
-/
theorem extremal_iff {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (p : Pieces (Carrier (Accepting L)) k)
    (a : Carrier (Accepting L) k) :
    IsExtremal L E p a ↔ canonical (normalize p) = p ∧
      ExtremalSituations.IsExtremal (Accepting L) E.algebra (normalize p, a) := by
  let F := Accepting L
  have hrefl := (FiniteContextualOrder.class_order F k).1 a
  constructor
  · intro hx
    have hacc := (acceptance_normalize L E p a).mp hx.1
    have hcanonical : Accepted L E (canonical (normalize p)) a := by
      rw [acceptance_normalize, normalize_canonical]
      exact hacc
    have hs := (hx.2 _ a ((canonical_order F (normalize p) p).mpr (data_refl F _))
      hrefl hcanonical).1
    refine ⟨hs, hacc, ?_⟩
    rintro ⟨y, b⟩ hy hb
    have hq : Accepted L E (canonical y) b := by
      rw [acceptance_normalize, normalize_canonical]
      exact hb
    obtain ⟨he, hba⟩ := hx.2 (canonical y) b ((canonical_order F y p).mpr hy.1) hy.2 hq
    have hdata : y = normalize p := by
      have h := congrArg normalize he
      rwa [normalize_canonical] at h
    exact Prod.ext hdata hba
  · rintro ⟨hs, hx⟩
    refine ⟨(acceptance_normalize L E p a).mpr hx.1, ?_⟩
    intro q b hq hb hacc
    have hbelow : ExtremalSituations.Below F (normalize q, b) (normalize p, a) :=
      ⟨normalize_monotone F q p hq, hb⟩
    have he := hx.2 _ hbelow ((acceptance_normalize L E q b).mp hacc)
    have hn : normalize q = normalize p := congrArg Prod.fst he
    have hsat := (canonical_order F (normalize q) q).mpr (data_refl F _)
    rw [hn, hs] at hsat
    exact ⟨funext (fun i => piece_antisymm F _ _ (hq i) (hsat i)), congrArg Prod.snd he⟩

/--
---
conclusion: Lax369799.ExtendedContexts.element_iff
---
Normalize an extremal formal situation, or represent an extremal planted
situation by its saturated formal pieces.
-/
theorem element_iff {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (a : Carrier (Accepting L) k) :
    ExtremalElement L E a ↔ ExtremalSituations.ExtremalElement (Accepting L) E.algebra a := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨normalize p, ((extremal_iff L E p a).mp hp).2⟩
  · rintro ⟨x, hx⟩
    refine ⟨canonical x, (extremal_iff L E (canonical x) a).mpr ?_⟩
    rw [normalize_canonical]
    exact ⟨rfl, hx⟩

/--
---
conclusion: Lax369799.ExtendedContexts.extremal_choice
---
Choose a minimal normalized situation and saturate its formal pieces.
The adjunction between canonical pieces and normalization gives all bounds.
-/
theorem extremal_choice {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ} (p : Pieces (Carrier (Accepting L)) k)
    (a : Carrier (Accepting L) k) (ha : Accepted L E p a) :
    ∃ q b, IsExtremal L E q b ∧
      (∀ i, PieceBelow (Accepting L) (q i) (p i)) ∧ ClassBelow (Accepting L) b a := by
  obtain ⟨⟨y, b⟩, hy, hb⟩ := ExtremalSituations.choice (Accepting L) E.algebra
    (BoundedProfileRefinement.finite_carrier_recognizable L hL hrec) (normalize p, a)
    ((acceptance_normalize L E p a).mp ha)
  refine ⟨canonical y, b, ?_, (canonical_order (Accepting L) y p).mpr hy.1, hy.2⟩
  apply (extremal_iff L E _ _).mpr
  rw [normalize_canonical]
  exact ⟨rfl, hb⟩

/--
---
conclusion: Lax369799.ExtendedContexts.replacement
---
Transport the whole-situation replacement through the formal-marker
characterization of extremal elements. This includes ranks zero and one.
-/
theorem replacement {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ}
    (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b, ExtremalElement L E b ∧ ClassBelow (Accepting L) b a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic b))) := by
  obtain ⟨b, hb, hba, hacc⟩ := ExtremalSituations.replacement L hL hrec E C a ha
  exact ⟨b, (element_iff L E b).mpr hb, hba, hacc⟩

/--
---
conclusion: Lax369799.ExtendedContexts.simultaneous
---
The marker characterization transports simultaneous replacement at
every vertex, including the case of an empty presentation.
-/
theorem simultaneous {A B : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P q)) ↔
      ∃ r : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1,
        (∀ v, ExtremalElement L E (r v) ∧ ClassBelow (Accepting L) (r v) (q v)) ∧
        AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P r)) := by
  rw [ExtremalSituations.simultaneous L hL hrec E P q]
  simp only [element_iff]

/--
---
conclusion: Lax369799.ExtendedContexts.normal_test
---
In every rank, the exact planted test and the canonical-marker
comparison identify acceptance with the componentwise order test.
-/
theorem normal_test {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ}
    (p q : Pieces (Carrier (Accepting L)) k) (a : Carrier (Accepting L) k)
    (ha : IsExtremal L E p a) :
    Accepted L E q a ↔ ∀ i, PieceBelow (Accepting L) (p i) (q i) := by
  obtain ⟨hs, hx⟩ := (extremal_iff L E p a).mp ha
  rw [acceptance_normalize, ExtremalSituations.normal_test L E _ _ hx]
  have h := canonical_order (Accepting L) (normalize p) q
  rw [hs] at h
  exact h.symm

end Lax369799Proofs.ExtendedContexts
