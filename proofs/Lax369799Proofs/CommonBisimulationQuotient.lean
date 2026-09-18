import Lax369799Proofs.BisimulationQuotient
import Mathlib.Data.Quot

namespace Lax369799Proofs.BisimulationQuotient
open Lax369799.BisimulationQuotient Lax369799.TransitionSystems

private def union {P : Type} (S T : TransitionSystem P) : Graph P (S.Vertex ⊕ T.Vertex) where
  valuation := Sum.elim S.valuation T.valuation
  edge := fun v w => match v, w with
    | .inl v, .inl w => S.edge v w
    | .inr v, .inr w => T.edge v w
    | _, _ => False

private def left {P : Type} (S T : TransitionSystem P) : BisimulationMap (ofSystem S) (union S T) where
  toFun := Sum.inl
  valuation := fun _ => rfl
  forward := fun _ _ h => h
  backward := by
    intro v w h
    cases w with
    | inl w => exact ⟨w, h, rfl⟩
    | inr w => exact False.elim h

private def right {P : Type} (S T : TransitionSystem P) : BisimulationMap (ofSystem T) (union S T) where
  toFun := Sum.inr
  valuation := fun _ => rfl
  forward := fun _ _ h => h
  backward := by
    intro v w h
    cases w with
    | inl w => exact False.elim h
    | inr w => exact ⟨w, h, rfl⟩

def compose {P V W U : Type} {G : Graph P V} {H : Graph P W} {K : Graph P U}
    (f : BisimulationMap G H) (g : BisimulationMap H K) : BisimulationMap G K where
  toFun := g.toFun ∘ f.toFun
  valuation := fun v => (f.valuation v).trans (g.valuation _)
  forward := fun v w h => g.forward _ _ (f.forward v w h)
  backward := by
    intro v u h
    obtain ⟨w, hw, hwu⟩ := g.backward _ u h
    obtain ⟨v', hv', hvw⟩ := f.backward v w hw
    exact ⟨v', hv', (congrArg g.toFun hvw).trans hwu⟩

private theorem roots_related {P : Type} (S T : TransitionSystem P) (h : Bisimilar S T) :
    Related (union S T) (union S T) (.inl S.initial) (.inr T.initial) := by
  obtain ⟨R, hr, hR⟩ := h
  let Q : (S.Vertex ⊕ T.Vertex) → (S.Vertex ⊕ T.Vertex) → Prop := fun v w => match v, w with
    | .inl v, .inr w => R v w
    | _, _ => False
  refine ⟨Q, ?_, hr⟩
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inr w =>
      have hh := hR v w h
      refine ⟨hh.1, ?_, ?_⟩
      · intro v' hv'
        cases v' with
        | inl v' =>
          obtain ⟨w', hw', hR'⟩ := hh.2.1 v' hv'
          exact ⟨.inr w', hw', hR'⟩
        | inr v' => exact False.elim hv'
      · intro w' hw'
        cases w' with
        | inr w' =>
          obtain ⟨v', hv', hR'⟩ := hh.2.2 w' hw'
          exact ⟨.inl v', hv', hR'⟩
        | inl w' => exact False.elim hw'
    | inl w => exact False.elim h
  | inr v => cases w <;> exact False.elim h

private theorem map_path {P V W : Type} {G : Graph P V} {H : Graph P W}
    (f : BisimulationMap G H) {v w : V} (h : Relation.ReflTransGen G.edge v w) :
    Relation.ReflTransGen H.edge (f.toFun v) (f.toFun w) := by
  induction h with
  | refl => exact .refl
  | tail h h' ih => exact ih.tail (f.forward _ _ h')

/--
---
conclusion: Lax369799.BisimulationQuotient.common_quotient
---
Take the disjoint union and quotient by vertex bisimilarity. The two
initial vertices have the same class. Every quotient class is reachable
from that class, and both projections lift successors.
-/
theorem common_quotient {P : Type} (S T : TransitionSystem P) (h : Bisimilar S T) :
    ∃ U : TransitionSystem P, Nonempty (SystemMap S U) ∧ Nonempty (SystemMap T U) := by
  classical
  let G := union S T
  let : Finite (Carrier G) := Finite.of_surjective (Quot.mk (Related G G)) Quot.mk_surjective
  let : Fintype (Carrier G) := Fintype.ofFinite _
  let e := Fintype.equivFin (Carrier G)
  obtain ⟨p, hp⟩ := quotient_projection G
  let l := compose (left S T) p
  let r := compose (right S T) p
  have hroot : l.toFun S.initial = r.toFun T.initial := by
    change p.toFun (.inl S.initial) = p.toFun (.inr T.initial)
    rw [hp]
    exact Quot.sound (roots_related S T h)
  have reachable (q : Carrier G) : Relation.ReflTransGen (quotient G).edge (l.toFun S.initial) q := by
    obtain ⟨v, hv⟩ := Quot.exists_rep q
    have hv : p.toFun v = q := by rw [hp]; exact hv
    cases v with
    | inl v => exact hv ▸ map_path l (S.reachable v)
    | inr v =>
      rw [hroot]
      exact hv ▸ map_path r (T.reachable v)
  let U : TransitionSystem P := {
    size := Fintype.card (Carrier G)
    initial := e (l.toFun S.initial)
    valuation := fun v => (quotient G).valuation (e.symm v)
    edge := fun v w => (quotient G).edge (e.symm v) (e.symm w)
    reachable := by
      intro v
      have hh := reachable (e.symm v)
      have hm : ∀ {q q'}, Relation.ReflTransGen (quotient G).edge q q' →
          Relation.ReflTransGen (fun v w => (quotient G).edge (e.symm v) (e.symm w)) (e q) (e q') := by
        intro q q' hh
        induction hh with
        | refl => exact .refl
        | tail hh h' ih => exact ih.tail (by simpa only [Equiv.symm_apply_apply] using h')
      simpa only [Equiv.apply_symm_apply] using hm hh }
  let g : BisimulationMap (quotient G) (ofSystem U) := {
    toFun := e
    valuation := fun v => by change _ = (quotient G).valuation (e.symm (e v)); rw [e.symm_apply_apply]
    forward := by
      intro v w h
      change (quotient G).edge (e.symm (e v)) (e.symm (e w))
      simpa only [Equiv.symm_apply_apply] using h
    backward := by
      intro v w h
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      change (quotient G).edge (e.symm (e v)) (e.symm w) at h
      simpa only [Equiv.symm_apply_apply] using h }
  refine ⟨U, ⟨{ compose l g with initial := rfl }⟩, ⟨{ compose r g with initial := ?_ }⟩⟩
  exact congrArg e hroot.symm

end Lax369799Proofs.BisimulationQuotient
