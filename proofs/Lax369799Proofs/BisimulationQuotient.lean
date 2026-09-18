import Lax369799.BisimulationQuotient

namespace Lax369799Proofs.BisimulationQuotient
open Lax369799.BisimulationQuotient

theorem related_refl {P V : Type} (G : Graph P V) (v : V) : Related G G v v := by
  refine ⟨Eq, ?_, rfl⟩
  rintro x y rfl
  exact ⟨rfl, fun z h => ⟨z, h, rfl⟩, fun z h => ⟨z, h, rfl⟩⟩

theorem related_symm {P V W : Type} {G : Graph P V} {H : Graph P W} {v : V} {w : W}
    (h : Related G H v w) : Related H G w v := by
  obtain ⟨R, hR, hr⟩ := h
  refine ⟨fun y x => R x y, ?_, hr⟩
  intro y x h
  have hh := hR x y h
  exact ⟨hh.1.symm, hh.2.2, hh.2.1⟩

theorem related_trans {P V W U : Type} {G : Graph P V} {H : Graph P W} {K : Graph P U}
    {v : V} {w : W} {u : U} (h : Related G H v w) (h' : Related H K w u) : Related G K v u := by
  obtain ⟨R, hR, hr⟩ := h
  obtain ⟨Q, hQ, hq⟩ := h'
  refine ⟨fun x z => ∃ y, R x y ∧ Q y z, ?_, ⟨w, hr, hq⟩⟩
  rintro x z ⟨y, hxy, hyz⟩
  have hxy := hR x y hxy
  have hyz := hQ y z hyz
  refine ⟨hxy.1.trans hyz.1, ?_, ?_⟩
  · intro x' hx
    obtain ⟨y', hy, hr⟩ := hxy.2.1 x' hx
    obtain ⟨z', hz, hq⟩ := hyz.2.1 y' hy
    exact ⟨z', hz, y', hr, hq⟩
  · intro z' hz
    obtain ⟨y', hy, hq⟩ := hyz.2.2 z' hz
    obtain ⟨x', hx, hr⟩ := hxy.2.2 y' hy
    exact ⟨x', hx, y', hr, hq⟩

/--
---
conclusion: Lax369799.BisimulationQuotient.related_equivalence
---
Identity, converse, and relational composition preserve the valuation
and the two successor-matching conditions.
-/
theorem related_equivalence {P V : Type} (G : Graph P V) : Equivalence (Related G G) :=
  ⟨related_refl G, related_symm, related_trans⟩

private theorem exact_related {P V : Type} (G : Graph P V) {v w : V}
    (h : Quot.mk (Related G G) v = Quot.mk (Related G G) w) : Related G G v w := by
  have hh : Relation.EqvGen (Related G G) v w := Quot.eqvGen_exact h
  clear h
  induction hh with
  | rel v w h => exact h
  | refl v => exact related_refl G v
  | symm v w h ih => exact related_symm ih
  | trans v w u h h' ih ih' => exact related_trans ih ih'

/--
---
conclusion: Lax369799.BisimulationQuotient.quotient_projection
---
Project an edge to the classes of its endpoints. Conversely, an edge of
the quotient has representatives related to the given source vertex;
its bisimulation matches that edge from the given source.
-/
theorem quotient_projection {P V : Type} (G : Graph P V) :
    ∃ f : BisimulationMap G (quotient G), f.toFun = Quot.mk (Related G G) := by
  refine ⟨{
    toFun := Quot.mk (Related G G)
    valuation := fun _ => rfl
    forward := fun v w h => ⟨v, w, rfl, rfl, h⟩
    backward := ?_ }, rfl⟩
  rintro v q ⟨x, y, hx, hy, hxy⟩
  obtain ⟨R, hR, hrvx⟩ := exact_related G hx.symm
  obtain ⟨v', hv', hrv'y⟩ := (hR v x hrvx).2.2 y hxy
  exact ⟨v', hv', (Quot.sound ⟨R, hR, hrv'y⟩).trans hy⟩

end Lax369799Proofs.BisimulationQuotient
