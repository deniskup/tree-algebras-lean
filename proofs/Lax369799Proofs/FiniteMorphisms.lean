import Lax369799.FiniteMorphisms
import Lax369799Proofs.FiniteAcceptance

namespace Lax369799Proofs.FiniteMorphisms
open Lax369799.RankedSystems (RankedSet RankedMap Presentation)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteAcceptance Lax369799.FiniteMorphisms
open Lax369799Proofs.Pullbacks

noncomputable def toEnumeration {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    {S : FiniteSystem A n} {G : Presentation A n V} (f : Map S.graph G) : Morphism S (enumerate G) where
  toFun := fun v => Fintype.equivFin V (f.toFun v)
  label := by
    intro v
    change G.label ((Fintype.equivFin V).symm (Fintype.equivFin V (f.toFun v))) = _
    rw [Equiv.symm_apply_apply]
    exact f.label v
  initial := by
    intro v hv
    change G.initial ((Fintype.equivFin V).symm (Fintype.equivFin V (f.toFun v)))
    rw [Equiv.symm_apply_apply]
    exact f.initial v hv
  root := by
    intro v hv
    change G.root ((Fintype.equivFin V).symm (Fintype.equivFin V (f.toFun v)))
    rw [Equiv.symm_apply_apply]
    exact f.root v hv
  edge := by
    intro v d t ht
    change G.edge ((Fintype.equivFin V).symm (Fintype.equivFin V (f.toFun v))) d
      (Sum.map (Fintype.equivFin V).symm id (Sum.map (fun v => Fintype.equivFin V (f.toFun v)) id t))
    have h := f.edge v d t ht
    cases t <;> simpa using h

noncomputable def fromEnumeration {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    {G : Presentation A n V} {T : FiniteSystem A n} (f : Map G T.graph) :
    Morphism (enumerate G) T where
  toFun := fun v => f.toFun ((Fintype.equivFin V).symm v)
  initial := fun _ h => f.initial _ h
  root := fun _ h => f.root _ h
  label := fun _ => f.label _
  edge := by
    intro v d t ht
    have h := f.edge _ d (Sum.map (Fintype.equivFin V).symm id t) ht
    cases t <;> exact h

noncomputable def enumerateMap {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : Map G H) :
    Morphism (enumerate G) (enumerate H) := toEnumeration {
  toFun := fun v => f.toFun ((Fintype.equivFin V).symm v)
  initial := fun v h => f.initial _ h
  root := fun v h => f.root _ h
  label := fun v => f.label _
  edge := by
    intro v d t ht
    have h := f.edge _ d (Sum.map (Fintype.equivFin V).symm id t) ht
    cases t <;> exact h }

def asMap {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n} (f : Morphism S T) :
    Map S.graph T.graph := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩

noncomputable def plugMorphism {A : RankedSet} {k n : ℕ} (C : Context A k n)
    {S T : FiniteSystem A k} (f : Morphism S T) : Morphism (plug C S) (plug C T) := by
  have maps : ∀ r a, Map (substitution S r a).graph (substitution T r a).graph := by
    intro r a
    cases a with
    | inl a => exact UntrimmedFlattening.isoMap (UntrimmedFlattening.isoRefl _)
    | inr h => obtain ⟨he⟩ := h; subst r; exact asMap f
  exact enumerateMap (UntrimmedFlattening.substituteMap C.system.graph
    (fun v => (substitution S (C.system.graph.label v).1 (C.system.graph.label v).2).graph)
    (fun v => (substitution T (C.system.graph.label v).1 (C.system.graph.label v).2).graph)
    (fun v => maps (C.system.graph.label v).1 (C.system.graph.label v).2))

/--
---
conclusion: Lax369799.FiniteMorphisms.accepting_morphism
---
The induced morphism on reachable restrictions preserves yields, so
universal yield acceptance reverses the morphism.
-/
theorem accepting_morphism {A : RankedSet} (L : Lax369799.Algebras.Language A)
    {S T : FiniteSystem A 0} (f : Morphism S T) : Accepting L T → Accepting L S := by
  intro ht U hu
  exact ht U ((Yields.morphism_yields (trimMap (asMap f))).1 U hu)

/--
---
conclusion: Lax369799.FiniteMorphisms.contextual_morphism
---
Lift the morphism through each testing context, then use reversal of
universal acceptance.
-/
theorem contextual_morphism {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    {S T : FiniteSystem A n} (f : Morphism S T) : Below (Accepting L) T S :=
  fun C => accepting_morphism L (plugMorphism C f)

noncomputable def sumLeft {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) :
    Morphism S (sum S T) := toEnumeration {
  toFun := Sum.inl
  initial := fun _ h => h
  root := fun _ h => h
  label := fun _ => rfl
  edge := fun _ _ t h => ⟨t, h, rfl⟩ }

noncomputable def sumRight {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) :
    Morphism T (sum S T) := toEnumeration {
  toFun := Sum.inr
  initial := fun _ h => h
  root := fun _ h => h
  label := fun _ => rfl
  edge := fun _ _ t h => ⟨t, h, rfl⟩ }

/--
---
conclusion: Lax369799.FiniteMorphisms.sum_lower
---
The inclusions into the disjoint union give the contextual comparisons
by reversal of morphisms.
-/
theorem sum_lower {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    (S T : FiniteSystem A n) :
    Below (Accepting L) (sum S T) S ∧ Below (Accepting L) (sum S T) T :=
  ⟨contextual_morphism L (sumLeft S T), contextual_morphism L (sumRight S T)⟩

end Lax369799Proofs.FiniteMorphisms
