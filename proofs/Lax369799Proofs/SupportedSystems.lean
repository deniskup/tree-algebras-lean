import Lax369799.SupportedSystems
import Lax369799Proofs.Flattening

namespace Lax369799Proofs.SupportedSystems
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations
open Lax369799.SupportedSystems
open Lax369799Proofs.Pullbacks

private noncomputable def innerFirst {A : RankedSet} {n : ℕ}
    (S : System (System A) n) (v : S.val.val.Vertex) :
    ((S.val.val.graph.label v).2.val.val).Vertex :=
  Classical.choose (S.val.val.graph.label v).2.val.property.1

private theorem inner_path {A : RankedSet} {n : ℕ} (S : System (System A) n)
    (v : S.val.val.Vertex) {a b : ((S.val.val.graph.label v).2.val.val).Vertex}
    (h : Relation.ReflTransGen (S.val.val.graph.label v).2.val.val.graph.Step a b) :
    Relation.ReflTransGen (flattenPresentation (pattern S).graph).Step ⟨v, a⟩ ⟨v, b⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b c h hbc ih =>
    obtain ⟨d, hd⟩ := hbc
    exact ih.tail ⟨d, Or.inl ⟨c, hd, rfl⟩⟩

private theorem reach_inside {A : RankedSet} {n : ℕ} (S : System (System A) n)
    (v : S.val.val.Vertex) (a : ((S.val.val.graph.label v).2.val.val).Vertex)
    (hv : (flattenPresentation (pattern S).graph).Reachable ⟨v, innerFirst S v⟩) :
    (flattenPresentation (pattern S).graph).Reachable ⟨v, a⟩ := by
  let U := (S.val.val.graph.label v).2.val
  obtain ⟨r, hr, hp⟩ := U.val.reachable a
  have hr' : r = innerFirst S v := by
    rcases hr with hr | hr
    · rw [Classical.choose_spec U.property.1] at hr
      exact hr
    · rw [U.property.2.1] at hr
      exact False.elim hr
  subst r
  obtain ⟨z, hz, hzp⟩ := hv
  exact ⟨z, hz, hzp.trans (inner_path S v hp)⟩

private theorem reach_entry {A : RankedSet} {n : ℕ} (S : System (System A) n)
    (v : S.val.val.Vertex) :
    (flattenPresentation (pattern S).graph).Reachable ⟨v, innerFirst S v⟩ := by
  obtain ⟨r, hr, hp⟩ := S.val.val.reachable v
  have hrinit : S.val.val.graph.initial r := hr.elim id (fun h => by
    rw [S.val.property.2.1] at h
    exact False.elim h)
  have hstart : (flattenPresentation (pattern S).graph).Reachable ⟨r, innerFirst S r⟩ := by
    have hi : (S.val.val.graph.label r).2.val.val.graph.initial (innerFirst S r) := by
      rw [Classical.choose_spec (S.val.val.graph.label r).2.val.property.1]
      rfl
    exact ⟨⟨r, innerFirst S r⟩, Or.inl ⟨hrinit, hi⟩, .refl⟩
  induction hp with
  | refl => exact hstart
  | @tail v w hp hvw ih =>
    obtain ⟨d, hd⟩ := hvw
    let i : Fin (S.val.val.graph.label v).1 :=
      ⟨d, S.val.val.graph.direction_valid v d (.inl w) hd⟩
    obtain ⟨u, e, he⟩ := (S.val.val.graph.label v).2.property i
    obtain ⟨z, hz, hzu⟩ := reach_inside S v u ih
    have hwinit : (S.val.val.graph.label w).2.val.val.graph.initial (innerFirst S w) := by
      rw [Classical.choose_spec (S.val.val.graph.label w).2.val.property.1]
      rfl
    exact ⟨z, hz, hzu.tail ⟨e, Or.inr ⟨i, he,
      Or.inl ⟨⟨w, innerFirst S w⟩, hd, hwinit, rfl⟩⟩⟩⟩

/--
---
conclusion: Lax369799.SupportedSystems.flatten_reachable
---
Every outer edge can be traversed through a reachable variable of its
inner system. Induct on an outer path, then follow an inner path to the
desired vertex. No flattened vertex is removed.
-/
theorem flatten_reachable {A : RankedSet} {n : ℕ} (S : System (System A) n) :
    ∀ v, (flattenPresentation (pattern S).graph).Reachable v :=
  fun v => reach_inside S v.1 v.2 (reach_entry S v.1)

/--
---
conclusion: Lax369799.SupportedSystems.flatten_system
---
The existing deterministic flattening supplies the unique successors.
Every outer variable edge is reached through its supported inner port,
and the reachable-part enumeration retains that edge.
-/
theorem flatten_system {A : RankedSet} {n : ℕ} (S : System (System A) n) :
    ∃ T : System A n, Lax369799.Flattening.SystemFlattening (forgetPattern S) T.val := by
  obtain ⟨T, hT⟩ := Flattening.flatten_system (forgetPattern S)
  have hs : FullySupported T := by
    intro j
    obtain ⟨v, d, hd⟩ := S.property j
    let i : Fin (S.val.val.graph.label v).1 :=
      ⟨d, S.val.val.graph.direction_valid v d (.inr j) hd⟩
    obtain ⟨u, e, he⟩ := (S.val.val.graph.label v).2.property i
    have hu := flatten_reachable S ⟨v, u⟩
    have hval : T.val = RankedSystems.trim (flattenPresentation (pattern S).graph) := hT
    rw [hval]
    refine ⟨index _ ⟨⟨v, u⟩, hu⟩, e, ?_⟩
    change (flattenPresentation (pattern S).graph).edge (vertex _ (index _ _)) e (.inr j)
    rw [vertex_index]
    exact Or.inr ⟨i, he, Or.inr ⟨j, hd, rfl⟩⟩
  exact ⟨⟨T, hs⟩, hT⟩

end Lax369799Proofs.SupportedSystems
