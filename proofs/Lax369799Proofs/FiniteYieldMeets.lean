import Lax369799.FiniteYieldMeets
import Lax369799Proofs.FiniteContinuityOrder

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteYieldMeets
open Lax369799.RankedSystems (RankedSet SetSystem Presentation trim)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance
open Lax369799.PresentationCovers
open Lax369799Proofs.Pullbacks

private def graph {A : RankedSet} {n m : ℕ} (F : Fin m → FiniteSystem A n) :
    Presentation A n ((i : Fin m) × (F i).Vertex) where
  label := fun v => (F v.1).graph.label v.2
  initial := fun v => (F v.1).graph.initial v.2
  root := fun v => (F v.1).graph.root v.2
  edge := fun v d t => ∃ s, (F v.1).graph.edge v.2 d s ∧ t = Sum.map (Sigma.mk v.1) id s
  direction_valid := by rintro v d t ⟨s, hs, _⟩; exact (F v.1).graph.direction_valid v.2 d s hs

private def fan {A : RankedSet} {n m : ℕ} (F : Fin m → FiniteSystem A n) :
    FiniteSystem (FiniteSystem A) n where
  size := m
  graph := {
    label := fun i => ⟨n, F i⟩
    initial := Set.univ
    root := ∅
    edge := fun _ d t => ∃ i : Fin n, d = i.val ∧ t = .inr i
    direction_valid := by rintro v d t ⟨i, rfl, _⟩; exact i.isLt }

private theorem fan_edge {A : RankedSet} {n m : ℕ} (F : Fin m → FiniteSystem A n)
    (v : (i : Fin m) × (F i).Vertex) (d : ℕ) (t : ((i : Fin m) × (F i).Vertex) ⊕ Fin n) :
    (flattenPresentation (fan F).graph).edge v d t ↔ (graph F).edge v d t := by
  constructor
  · rintro (⟨w, hw, rfl⟩ | ⟨i, hi, he⟩)
    · exact ⟨.inl w, hw, rfl⟩
    · rcases he with ⟨w, ⟨j, _, hj⟩, _⟩ | ⟨j, ⟨l, hl, he⟩, rfl⟩
      · cases hj
      · have hlj : j = l := Sum.inr.inj he
        have hil : i = l := Fin.ext hl
        subst j
        subst i
        exact ⟨.inr l, hi, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    cases s with
    | inl w => exact Or.inl ⟨w, hs, rfl⟩
    | inr i => exact Or.inr ⟨i, hs, Or.inr ⟨i, ⟨i, rfl, rfl⟩, rfl⟩⟩

private def fanCover {A : RankedSet} {n m : ℕ} (F : Fin m → FiniteSystem A n) :
    Cover (flattenPresentation (fan F).graph) (graph F) where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h.2
  root := fun _ h => h.elim id (fun h => False.elim h.1)
  edge := by
    intro v d t h
    have hh := (fan_edge F v d t).mp h
    cases t <;> exact hh
  initial_lift := fun v h => ⟨v, ⟨trivial, h⟩, rfl⟩
  root_lift := fun v h => ⟨v, Or.inl h, rfl⟩
  edge_lift := fun v d t h => ⟨t, (fan_edge F v d t).mpr h, by cases t <;> rfl⟩

private def foldCover {A : RankedSet} {n m : ℕ} (hm : 0 < m) (R : FiniteSystem A n) :
    Cover (graph (fun _ : Fin m => R)) R.graph where
  toFun := Sigma.snd
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by rintro v d t ⟨s, hs, rfl⟩; cases s <;> exact hs
  initial_lift := fun v h => ⟨⟨⟨0, hm⟩, v⟩, h, rfl⟩
  root_lift := fun v h => ⟨⟨⟨0, hm⟩, v⟩, h, rfl⟩
  edge_lift := fun v d t h => ⟨Sum.map (Sigma.mk v.1) id t, ⟨t, h, rfl⟩, by cases t <;> rfl⟩

private theorem graph_meet {A : RankedSet} (L : Lax369799.Algebras.Language A) {n m : ℕ}
    (R : FiniteSystem A n) (F : Fin m → FiniteSystem A n) :
    Below (Accepting L) R (enumerate (graph F)) ↔ ∀ i, Below (Accepting L) R (F i) := by
  classical
  constructor
  · intro h i
    let raw : Map (F i).graph (graph F) := {
      toFun := fun v => ⟨i, v⟩
      initial := fun _ h => h
      root := fun _ h => h
      label := fun _ => rfl
      edge := fun _ _ t h => ⟨t, h, rfl⟩ }
    let f := FiniteMorphisms.toEnumeration (S := F i) raw
    exact fun C hc => FiniteMorphisms.contextual_morphism L f C (h C hc)
  · intro h
    cases m with
    | zero =>
      let f := FiniteMorphisms.fromEnumeration (G := graph F) (T := R) {
        toFun := fun v => Fin.elim0 v.1
        initial := fun v => Fin.elim0 v.1
        root := fun v => Fin.elim0 v.1
        label := fun v => Fin.elim0 v.1
        edge := fun v => Fin.elim0 v.1 }
      exact FiniteMorphisms.contextual_morphism L f
    | succ m =>
      let K := fun _ : Fin (m + 1) => R
      have hm := FiniteContextualOrder.flatten_monotone (Accepting L)
        (FiniteAcceptance.accepting_isomorphic L) (fan K) (fun _ => R) F h
      have he : withLabels (fan K) (fun _ => R) = fan K := rfl
      have hf : withLabels (fan K) F = fan F := rfl
      rw [he, hf] at hm
      have ha := FiniteCovers.contextual_cover L (S := flatten (fan K)) (T := R)
        (FiniteCovers.compose (FiniteCovers.isoCover (UntrimmedFlattening.isoSymm
          (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _))))
          (FiniteCovers.compose (fanCover K) (foldCover (Nat.succ_pos m) R)))
      have hb := FiniteCovers.contextual_cover L (FiniteCovers.enumerateCover (fanCover F))
      exact fun C hc => hb.1 C (hm C (ha.2 C hc))

/--
---
conclusion: Lax369799.FiniteYieldMeets.finite_meet
---
The finite parallel substitution is monotone in every label. Repeating
a single presentation gives a cover of that presentation, so a common
lower bound lies below the sum. Inclusion morphisms give the converse;
the empty family has a morphism into every presentation.
-/
theorem finite_meet {A : RankedSet} (L : Lax369799.Algebras.Language A) {n m : ℕ}
    (R : FiniteSystem A n) (F : Fin m → SetSystem A n) :
    Below (Accepting L) R (ofSetSystem (Lax369799.YieldContinuity.finiteSum F)) ↔
      ∀ i, Below (Accepting L) R (ofSetSystem (F i)) := by
  classical
  let G := graph (fun i => ofSetSystem (F i))
  have he := FiniteCovers.contextual_cover L
    (S := ofSetSystem (trim G)) (T := enumerate G)
    (FiniteCovers.compose (FiniteAcceptance.trimProjection G)
      (FiniteCovers.isoCover (UntrimmedFlattening.reindexIso G (Fintype.equivFin _))))
  constructor
  · intro h
    exact (graph_meet L R _).mp (fun C hc => he.1 C (h C hc))
  · intro h
    have hh := (graph_meet L R _).mpr h
    exact fun C hc => he.2 C (hh C hc)

/--
---
conclusion: Lax369799.FiniteYieldMeets.yield_lower_bound
---
Finite approximation reduces the order comparison to finite sums of
yields. The finite meet law reduces each such comparison to its
summands. Singleton families give the reverse implication.
-/
theorem yield_lower_bound {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    (R S : FiniteSystem A n) :
    Below (Accepting L) R S ↔
      ∀ T : SetSystem A n, Lax369799.Morphisms.Yield (trim S.graph) T →
        Below (Accepting L) R (ofSetSystem T) := by
  rw [FiniteContinuityOrder.order_approximation L R S]
  constructor
  · intro h T hT
    exact (finite_meet L R (fun _ : Fin 1 => T)).mp (h 1 (fun _ => T) (fun _ => hT)) 0
  · intro h m F hF
    exact (finite_meet L R F).mpr (fun i => h (F i) (hF i))

end Lax369799Proofs.FiniteYieldMeets
