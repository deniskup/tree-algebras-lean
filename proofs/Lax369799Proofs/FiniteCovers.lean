import Lax369799Proofs.FiniteMorphisms

namespace Lax369799Proofs.FiniteCovers
open Lax369799.RankedSystems (RankedSet Presentation)
open Lax369799.PresentationCovers
open Lax369799Proofs.UntrimmedFlattening

private def asMap {A : RankedSet} {n : ℕ} {V W : Type}
    {P : Presentation A n V} {Q : Presentation A n W} (f : Cover P Q) : Pullbacks.Map P Q :=
  ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩

def substituteCover {A B : RankedSet} {n : ℕ} {V : Type} {W X : V → Type}
    (P : Presentation B n V) (Q : ∀ v, Presentation A (P.label v).1 (W v))
    (R : ∀ v, Presentation A (P.label v).1 (X v))
    (f : ∀ v, Cover (Q v) (R v)) : Cover (substitute P Q) (substitute P R) where
  toFun := (substituteMap P Q R (fun v => asMap (f v))).toFun
  label := (substituteMap P Q R (fun v => asMap (f v))).label
  initial := (substituteMap P Q R (fun v => asMap (f v))).initial
  root := (substituteMap P Q R (fun v => asMap (f v))).root
  edge := (substituteMap P Q R (fun v => asMap (f v))).edge
  initial_lift := by
    rintro ⟨v, w⟩ ⟨hv, hw⟩
    obtain ⟨u, hu, rfl⟩ := (f v).initial_lift w hw
    exact ⟨⟨v, u⟩, ⟨hv, hu⟩, rfl⟩
  root_lift := by
    rintro ⟨v, w⟩ (hw | ⟨hv, hw⟩)
    · obtain ⟨u, hu, rfl⟩ := (f v).root_lift w hw
      exact ⟨⟨v, u⟩, Or.inl hu, rfl⟩
    · obtain ⟨u, hu, rfl⟩ := (f v).initial_lift w hw
      exact ⟨⟨v, u⟩, Or.inr ⟨hv, hu⟩, rfl⟩
  edge_lift := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · obtain ⟨s, hs, he⟩ := (f v.1).edge_lift v.2 d (.inl w) hw
      cases s with
      | inl u =>
        cases Sum.inl.inj he
        exact ⟨.inl ⟨v.1, u⟩, Or.inl ⟨u, hs, rfl⟩, rfl⟩
      | inr j => cases he
    · obtain ⟨s, hs, he⟩ := (f v.1).edge_lift v.2 d (.inr i) hi
      cases s with
      | inl u => cases he
      | inr j =>
        cases Sum.inr.inj he
        rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨k, hk, rfl⟩
        · obtain ⟨u, hu, he⟩ := (f w.1).initial_lift w.2 hw'
          refine ⟨.inl ⟨w.1, u⟩, Or.inr ⟨j, hs, Or.inl ⟨⟨w.1, u⟩, hw, hu, rfl⟩⟩, ?_⟩
          exact congrArg (fun x => Sum.inl (Sigma.mk w.1 x)) he
        · exact ⟨.inr k, Or.inr ⟨j, hs, Or.inr ⟨k, hk, rfl⟩⟩, rfl⟩

open Lax369799.FinitePresentations Lax369799.FiniteContexts
open Lax369799.FiniteAcceptance Lax369799.FiniteContextualOrder

def isoCover {A : RankedSet} {n : ℕ} {V W : Type}
    {G : Presentation A n V} {H : Presentation A n W} (f : PresentationIso G H) : Cover G H where
  toFun := f.vertex
  label := f.label
  initial := fun v => (f.initial v).mpr
  root := fun v => (f.root v).mpr
  edge := fun v d t => (f.edge v d t).mpr
  initial_lift := by
    intro w hw
    obtain ⟨v, rfl⟩ := f.vertex.surjective w
    exact ⟨v, (f.initial v).mp hw, rfl⟩
  root_lift := by
    intro w hw
    obtain ⟨v, rfl⟩ := f.vertex.surjective w
    exact ⟨v, (f.root v).mp hw, rfl⟩
  edge_lift := by
    intro v d t ht
    let s := Sum.map f.vertex.symm id t
    have he : Sum.map f.vertex id s = t := by cases t <;> simp [s]
    refine ⟨s, (f.edge v d s).mp ?_, he⟩
    rw [he]
    exact ht

def compose {A : RankedSet} {n : ℕ} {V W X : Type}
    {G : Presentation A n V} {H : Presentation A n W} {K : Presentation A n X}
    (f : Cover G H) (g : Cover H K) : Cover G K where
  toFun := g.toFun ∘ f.toFun
  label := fun v => (g.label _).trans (f.label v)
  initial := fun v h => g.initial _ (f.initial v h)
  root := fun v h => g.root _ (f.root v h)
  edge := by
    intro v d t h
    have hh := g.edge _ d _ (f.edge v d t h)
    cases t <;> exact hh
  initial_lift := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := g.initial_lift x hx
    obtain ⟨v, hv, rfl⟩ := f.initial_lift w hw
    exact ⟨v, hv, rfl⟩
  root_lift := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := g.root_lift x hx
    obtain ⟨v, hv, rfl⟩ := f.root_lift w hw
    exact ⟨v, hv, rfl⟩
  edge_lift := by
    intro v d t ht
    obtain ⟨s, hs, rfl⟩ := g.edge_lift (f.toFun v) d t ht
    obtain ⟨r, hr, rfl⟩ := f.edge_lift v d s hs
    exact ⟨r, hr, by cases r <;> rfl⟩

noncomputable def enumerateCover {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : Cover G H) :
    Cover (enumerate G).graph (enumerate H).graph :=
  compose (isoCover (isoSymm (reindexIso G (Fintype.equivFin V))))
    (compose f (isoCover (reindexIso H (Fintype.equivFin W))))

noncomputable def plugCover {A : RankedSet} {k n : ℕ} (C : Context A k n)
    {S T : FiniteSystem A k} (f : Cover S.graph T.graph) : Cover (plug C S).graph (plug C T).graph := by
  have maps : ∀ r a, Cover (substitution S r a).graph (substitution T r a).graph := by
    intro r a
    cases a with
    | inl a => exact isoCover (isoRefl _)
    | inr h => obtain ⟨he⟩ := h; subst r; exact f
  exact enumerateCover (substituteCover C.system.graph
    (fun v => (substitution S (C.system.graph.label v).1 (C.system.graph.label v).2).graph)
    (fun v => (substitution T (C.system.graph.label v).1 (C.system.graph.label v).2).graph)
    (fun v => maps (C.system.graph.label v).1 (C.system.graph.label v).2))

theorem accepting_cover {A : RankedSet} (L : Lax369799.Algebras.Language A)
    {S T : FiniteSystem A 0} (f : Cover S.graph T.graph) : Accepting L S ↔ Accepting L T := by
  have hf := Pullbacks.trimMap_surjective (asMap f) f.initial_lift f.root_lift f.edge_lift
  exact Acceptance.accepting_unfold L _ _
    ⟨_, ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
      ⟨Pullbacks.trimMap (asMap f), hf⟩⟩

/--
---
conclusion: Lax369799.FiniteMorphisms.contextual_cover
---
Local surjectivity lifts through substitution in a fixed context and
preserves the yields of the final reachable restriction.
-/
theorem contextual_cover {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    {S T : FiniteSystem A n} (f : Cover S.graph T.graph) : Equivalent (Accepting L) S T :=
  ⟨fun C => (accepting_cover L (plugCover C f)).mp,
   fun C => (accepting_cover L (plugCover C f)).mpr⟩

private def foldCover {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    Cover (sumPresentation S.graph S.graph) S.graph where
  toFun := Sum.elim id id
  label := by intro v; cases v <;> rfl
  initial := by intro v; cases v <;> exact id
  root := by intro v; cases v <;> exact id
  edge := by
    intro v d t ht
    cases v <;> obtain ⟨s, hs, rfl⟩ := ht <;> cases s <;> exact hs
  initial_lift := fun v h => ⟨.inl v, h, rfl⟩
  root_lift := fun v h => ⟨.inl v, h, rfl⟩
  edge_lift := by
    intro v d t ht
    cases v with
    | inl v => exact ⟨Sum.map Sum.inl id t, ⟨t, ht, rfl⟩, by cases t <;> rfl⟩
    | inr v => exact ⟨Sum.map Sum.inr id t, ⟨t, ht, rfl⟩, by cases t <;> rfl⟩

/--
---
conclusion: Lax369799.FiniteMorphisms.sum_idempotent
---
Folding two copies onto one is locally surjective, also at unreachable
vertices. Contextual invariance under covers therefore identifies them.
-/
theorem sum_idempotent {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    (S : FiniteSystem A n) : Equivalent (Accepting L) (sum S S) S := by
  classical
  exact contextual_cover L (compose (isoCover (isoSymm
    (reindexIso (sumPresentation S.graph S.graph) (Fintype.equivFin _)))) (foldCover S))

private def binaryLabels {A : RankedSet} {n : ℕ}
    (P Q S T : FiniteSystem A n) :
    ∀ v : (binary P Q).Vertex, FiniteSystem A ((binary P Q).graph.label v).1 :=
  Fin.cases S (fun _ => T)

private theorem withLabels_binary {A : RankedSet} {n : ℕ} (P Q S T : FiniteSystem A n) :
    withLabels (binary P Q) (binaryLabels P Q S T) = binary S T := by
  dsimp only [withLabels, binary]
  congr 1
  congr 1
  funext v
  fin_cases v <;> rfl

private theorem sum_monotone {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    {P Q S T : FiniteSystem A n} (h : Below (Accepting L) P S) (h' : Below (Accepting L) Q T) :
    Below (Accepting L) (sum P Q) (sum S T) := by
  have hm := FiniteContextualOrder.flatten_monotone (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) (binary P Q)
    (binaryLabels P Q P Q) (binaryLabels P Q S T) (by
      intro v
      fin_cases v
      · exact h
      · exact h')
  rw [withLabels_binary, withLabels_binary] at hm
  have hi := FiniteContextualOrder.contextual_iso (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) _ _ (FiniteSums.flatten_binary P Q)
  have hj := FiniteContextualOrder.contextual_iso (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) _ _ (FiniteSums.flatten_binary S T)
  exact fun C hc => hj.1 C (hm C (hi.2 C hc))

/--
---
conclusion: Lax369799.FiniteMorphisms.sum_meet
---
Monotonicity of substitution gives monotonicity of the binary sum. Its
idempotence and the two inclusion morphisms characterize the greatest
lower bound in the contextual preorder.
-/
theorem sum_meet {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    (R S T : FiniteSystem A n) :
    Below (Accepting L) R (sum S T) ↔
      Below (Accepting L) R S ∧ Below (Accepting L) R T := by
  constructor
  · intro h
    have hs := FiniteMorphisms.sum_lower L S T
    exact ⟨fun C hc => hs.1 C (h C hc), fun C hc => hs.2 C (h C hc)⟩
  · rintro ⟨hs, ht⟩
    have h := sum_monotone L hs ht
    exact fun C hc => h C ((sum_idempotent L R).2 C hc)

end Lax369799Proofs.FiniteCovers
