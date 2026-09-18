import Lax369799.InitialAlgebra
import Lax369799Proofs.Flattening

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.InitialAlgebra
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.Flattening
open Lax369799.InitialAlgebra
open Lax369799Proofs.Pullbacks

private theorem initial_spec {A : RankedSet} {n : ℕ} (S : System A n) :
    S.val.graph.initial = {initial S} := Classical.choose_spec S.property.1

private theorem initial_mem {A : RankedSet} {n : ℕ} (S : System A n) :
    initial S ∈ S.val.graph.initial := by rw [initial_spec]; rfl

private theorem initial_unique {A : RankedSet} {n : ℕ} (S : System A n) {v : S.val.Vertex}
    (h : v ∈ S.val.graph.initial) : v = initial S := by
  rwa [initial_spec] at h

/--
---
conclusion: Lax369799.InitialAlgebra.algebra
---
The initial vertex of a flattening pairs the initial outer vertex with the
initial vertex of its inner system.
-/
theorem algebra (C : Type) : ∃ E : Algebra (fun _ => C), E.eval = evaluate := by
  classical
  refine ⟨{
    eval := evaluate
    isomorphic := ?_
    unit := ?_
    associative := ?_ }, rfl⟩
  · intro n S T h
    obtain ⟨f, _, _⟩ := h
    have hi := initial_unique T (f.initial _ (initial_mem S))
    have hl := f.label (initial S)
    rw [hi] at hl
    exact (congrArg Sigma.snd hl).symm
  · intro n c
    rfl
  · intro n S T ht
    let R := relabel (fun _ (U : System (fun _ => C) _) => U.val) S.val
    let G := Flattening.graph R
    have htv : T.val = trim G := ht
    have hd : (trim G).Deterministic := htv ▸ T.property
    have hte : T = ⟨trim G, hd⟩ := Subtype.ext htv
    subst T
    let v := initial (⟨trim G, hd⟩ : System (fun _ => C) n)
    have hv : vertex G v ∈ G.initial := by
      exact initial_mem (⟨trim G, hd⟩ : System (fun _ => C) n)
    have ho : (vertex G v).1 = initial S := initial_unique S hv.1
    have hi : (vertex G v).2 = initial (S.val.graph.label (vertex G v).1).2 :=
      initial_unique _ hv.2
    have hl : evaluate n (⟨trim G, hd⟩ : System (fun _ => C) n) = (G.label (vertex G v)).2 := by
      rfl
    rw [hl]
    change _ = ((S.val.graph.label (vertex G v).1).2.val.graph.label (vertex G v).2).2
    rw [hi]
    rw [ho]
    rfl

/--
---
conclusion: Lax369799.InitialAlgebra.recognizes
---
Interpret each letter by the truth value of its initial-vertex predicate.
-/
theorem recognizes {A : RankedSet} (p : ∀ n, A n → Prop) :
    Recognizable {S : System A 0 | p _ (S.val.graph.label (initial S)).2} := by
  classical
  obtain ⟨E, he⟩ := algebra Bool
  refine ⟨fun _ => Bool, E, fun n a => decide (p n a), {true}, fun _ => inferInstance, ?_⟩
  intro S
  rw [he]
  change p _ (S.val.graph.label (initial S)).2 ↔ decide (p _ (S.val.graph.label (initial S)).2) = true
  exact (decide_eq_true_iff).symm

end Lax369799Proofs.InitialAlgebra
