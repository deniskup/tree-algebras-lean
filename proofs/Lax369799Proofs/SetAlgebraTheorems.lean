import Lax369799.SetAlgebraTheorems
import Lax369799Proofs.Yields
import Lax369799Proofs.SumEvaluation

namespace Lax369799Proofs.SetAlgebraTheorems
open Lax369799.RankedSystems Lax369799.SetAlgebras Lax369799.AutomatonProperty

/--
---
conclusion: Lax369799.SetAlgebraTheorems.low_rank_deterministic
---
The atomic system of a letter of rank at most one is a witnessing system.
-/
theorem low_rank_deterministic {A : RankedSet} (E : SetAlgebra A)
    {n : ℕ} (hn : n ≤ 1) (a : A n) : Deterministic E a :=
  ⟨atomic a, fun _ => hn, E.unit n a⟩

/--
---
conclusion: Lax369799.SetAlgebraTheorems.order_laws
---
The associative, commutative, idempotent operation defines its usual
semilattice order.
-/
theorem order_laws {A : RankedSet} (E : SetAlgebra A) (n : ℕ) :
    (∀ a : A n, Below E a a) ∧
    (∀ a b : A n, Below E a b → Below E b a → a = b) ∧
    (∀ a b c : A n, Below E a b → Below E b c → Below E a c) ∧
    (∀ a b c : A n, Below E c (meet E a b) ↔ Below E c a ∧ Below E c b) := by
  obtain ⟨assoc, comm, idem⟩ := Lax369799Proofs.SumEvaluation.meet_laws E n
  change (∀ a, meet E a a = a) ∧
    (∀ a b, meet E a b = a → meet E b a = b → a = b) ∧
    (∀ a b c, meet E a b = a → meet E b c = b → meet E a c = a) ∧
    (∀ a b c, meet E c (meet E a b) = c ↔ meet E c a = c ∧ meet E c b = c)
  have trans : ∀ a b c : A n, meet E a b = a → meet E b c = b → meet E a c = a := by
    intro a b c hab hbc
    calc
      meet E a c = meet E (meet E a b) c := by rw [hab]
      _ = meet E a (meet E b c) := assoc a b c
      _ = a := by rw [hbc, hab]
  refine ⟨idem, ?_, trans, ?_⟩
  · intro a b hab hba
    exact hab.symm.trans ((comm a b).trans hba)
  · intro a b c
    constructor
    · intro h
      constructor
      · apply trans c (meet E a b) a h
        rw [comm a b, assoc b a a, idem, comm]
      · apply trans c (meet E a b) b h
        rw [assoc, idem]
    · rintro ⟨ha, hb⟩
      rw [← assoc, ha, hb]

open Lax369799.Morphisms Lax369799Proofs.MorphismTheorems

def plantMap {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) : Morphism (plant S) (plant T) where
  toFun := f.toFun
  initial := fun _ h => False.elim h
  root := fun v h => h.elim (fun h => Or.inl (f.root v h)) (fun h => Or.inr (f.initial v h))
  label := f.label
  edge := f.edge

theorem plant_surjective {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) (hf : f.LocallySurjective) : (plantMap f).LocallySurjective := by
  refine ⟨fun _ h => False.elim h, ?_, hf.2.2⟩
  intro w hw
  rcases hw with hw | hw
  · obtain ⟨v, hv, he⟩ := hf.2.1 w hw
    exact ⟨v, Or.inl hv, he⟩
  · obtain ⟨v, hv, he⟩ := hf.1 w hw
    exact ⟨v, Or.inr hv, he⟩

private theorem eval_cover {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) (hf : f.LocallySurjective) :
    E.eval n S = E.eval n T :=
  E.unfold_invariant n S T ⟨S, ⟨identity S, identity_surjective S⟩, ⟨f, hf⟩⟩

private theorem yield_evaluation {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (S T : SetSystem A n) (h : Yield S T) : Below E (E.eval n S) (E.eval n T) := by
  rcases h with ⟨U, ⟨D, ⟨d⟩, ⟨u, hu⟩⟩, rfl⟩ | ⟨U, ⟨D, ⟨d⟩, ⟨u, hu⟩⟩, rfl⟩
  · rw [← eval_cover E u hu]
    exact E.morphism n D.val S ⟨d⟩
  · let G : Presentation A n S.Vertex := {S.graph with initial := S.graph.root, root := ∅}
    let vmap := fun v => Lax369799Proofs.Pullbacks.vertex G (d.toFun v)
    let m : Morphism (plant D.val) S := {
      toFun := vmap
      initial := fun _ h => False.elim h
      root := by
        intro v hv
        rcases hv with hv | hv
        · rw [D.property.2.1] at hv
          exact False.elim hv
        · exact d.initial v hv
      label := fun v => d.label v
      edge := by
        intro v dir t ht
        have hh := d.edge v dir t ht
        cases t <;> exact hh }
    rw [← eval_cover E (plantMap u) (plant_surjective u hu)]
    exact E.morphism n (plant D.val) S ⟨m⟩

/--
---
conclusion: Lax369799.SetAlgebraTheorems.yield_order
---
Every yield has evaluation above the original system, by the morphism
and unfolding axioms. Apply continuity to the included family of yields.
-/
theorem yield_order {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (S T : SetSystem A n) (h : YieldBelow S T) : Below E (E.eval n T) (E.eval n S) := by
  apply E.continuity
  intro U hU
  exact yield_evaluation E T U (h U hU)

end Lax369799Proofs.SetAlgebraTheorems
