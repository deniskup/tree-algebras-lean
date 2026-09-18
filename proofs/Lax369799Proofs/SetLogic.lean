import Lax369799.SetLogic

namespace Lax369799Proofs.SetLogic
open Lax369799.TransitionSystems Lax369799.SetLogic

@[simp] theorem eval_conj {P X : Type} (S : TransitionSystem P) (σ : X → Set S.Vertex)
    (φ ψ : Formula P X) : (φ.conj ψ).eval S σ ↔ φ.eval S σ ∧ ψ.eval S σ := by
  simp [Formula.conj, Formula.eval]

/--
---
conclusion: Lax369799.SetLogic.empty_iff
---
A set included in every set is included in the empty set.
-/
theorem empty_iff {P X : Type} (S : TransitionSystem P) (σ : X → Set S.Vertex) (x : X) :
    (Formula.empty x).eval S σ ↔ σ x = ∅ := by
  simp only [Formula.empty, Formula.eval, Option.elim_some, Option.elim_none,
    not_exists, not_not]
  constructor
  · intro h
    exact Set.Subset.antisymm (h ∅) (Set.empty_subset _)
  · intro h U
    rw [h]
    exact Set.empty_subset U

/--
---
conclusion: Lax369799.SetLogic.singleton_iff
---
A nonempty set with no proper nonempty subset consists of one vertex.
-/
theorem singleton_iff {P X : Type} (S : TransitionSystem P) (σ : X → Set S.Vertex) (x : X) :
    (Formula.singleton x).eval S σ ↔ ∃ v, σ x = {v} := by
  classical
  simp only [Formula.singleton, eval_conj, Formula.eval, empty_iff,
    Option.elim_none, Option.elim_some]
  constructor
  · rintro ⟨hn, h⟩
    obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hn
    refine ⟨v, Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr hv)⟩
    by_contra he
    exact h ⟨{v}, Set.singleton_subset_iff.mpr hv, Set.singleton_ne_empty v, he⟩
  · rintro ⟨v, hv⟩
    refine ⟨hv ▸ Set.singleton_ne_empty v, ?_⟩
    rintro ⟨U, hU, hn, hbad⟩
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hn
    have hwv : w = v := by simpa only [hv, Set.mem_singleton_iff] using hU hw
    subst w
    apply hbad
    rw [hv]
    exact Set.singleton_subset_iff.mpr hw

end Lax369799Proofs.SetLogic
