import Lax369799.ModalTransitions

namespace Lax369799Proofs.ModalTransitions
set_option backward.isDefEq.respectTransparency false
open Lax369799
open TransitionEncoding TransitionSystems UnfoldAutomata ModalMuCalculus ModalTransitions

theorem eval_conjunction {P : Type} {n : ℕ} (l : List (Formula P n))
    (S : TransitionSystem P) (ρ : Fin n → Set S.Vertex) (v : S.Vertex) :
    v ∈ (conjunction l).eval S ρ ↔ ∀ φ ∈ l, v ∈ φ.eval S ρ := by
  induction l with
  | nil => simp [conjunction, Formula.eval]
  | cons φ l ih => simpa [conjunction, Formula.eval] using and_congr Iff.rfl ih

theorem eval_disjunction {P : Type} {n : ℕ} (l : List (Formula P n))
    (S : TransitionSystem P) (ρ : Fin n → Set S.Vertex) (v : S.Vertex) :
    v ∈ (disjunction l).eval S ρ ↔ ∃ φ ∈ l, v ∈ φ.eval S ρ := by
  induction l with
  | nil => simp [disjunction, Formula.eval]
  | cons φ l ih => simpa [disjunction, Formula.eval] using or_congr Iff.rfl ih

private theorem valuation_iff {P : Type} [Fintype P] {n : ℕ}
    (ν : Set P) (S : TransitionSystem P) (ρ : Fin n → Set S.Vertex) (v : S.Vertex) :
    v ∈ (valuationFormula ν).eval S ρ ↔ S.valuation v = ν := by
  classical
  have he : v ∈ (valuationFormula ν).eval S ρ ↔
      ∀ p, if p ∈ ν then p ∈ S.valuation v else p ∉ S.valuation v := by
    simp only [valuationFormula, eval_conjunction, List.forall_mem_map, Finset.mem_toList,
      Finset.mem_univ, forall_true_left]
    apply forall_congr'
    intro p
    by_cases hp : p ∈ ν <;> simp [hp, Formula.eval]
  rw [he]
  constructor
  · intro h
    ext p
    specialize h p
    split_ifs at h with hp <;> simp_all
  · intro h p
    rw [h]
    split_ifs <;> assumption

private theorem support_iff {P : Type}
    (M : UnfoldAutomaton (TransitionAlphabet P)) (q : Fin M.condition.states)
    (B : Set (Fin M.unary)) (S : TransitionSystem P)
    (ρ : Fin M.condition.states → Set S.Vertex) (v : S.Vertex) :
    v ∈ (supportFormula M q B).eval S ρ ↔
      (∀ b ∈ B, ∃ w, S.edge v w ∧ w ∈ ρ (M.condition.step q (.inl b))) ∧
      (∀ w, S.edge v w → ∃ b ∈ B, w ∈ ρ (M.condition.step q (.inl b))) := by
  classical
  simp [supportFormula, Formula.eval, eval_conjunction, eval_disjunction]

theorem leaf_iff {P : Type} {n : ℕ} (C : Prop) [Decidable C]
    (S : TransitionSystem P) (ρ : Fin n → Set S.Vertex) (v : S.Vertex) :
    v ∈ (if C then (Formula.box Formula.bot : Formula P n) else Formula.bot).eval S ρ ↔
      C ∧ ∀ w, ¬ S.edge v w := by
  by_cases h : C <;> simp [h, Formula.eval]

/--
---
conclusion: Lax369799.ModalTransitions.eval_transition
---
The valuation guard selects precisely the input valuation. Diamonds
witness each supported type, the box covers all successors, and the
leaf disjunct checks the final-state condition at a vertex with no edge.
-/
theorem eval_transition {P : Type} [Fintype P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (q : Fin M.condition.states)
    (S : TransitionSystem P) (ρ : Fin M.condition.states → Set S.Vertex) (v : S.Vertex) :
    v ∈ (transitionFormula M q).eval S ρ ↔ OneStep M q S v ρ := by
  classical
  simp [transitionFormula, eval_disjunction, Formula.eval, valuation_iff, support_iff,
    leaf_iff, OneStep]

/--
---
conclusion: Lax369799.ModalTransitions.realized_nonempty
---
A realized support contains the first component of its positive-arity
transition tuple.
-/
theorem realized_nonempty {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (ν : Set P) (B : Set (Fin M.unary)) (h : Realized M ν B) : B.Nonempty := by
  obtain ⟨n, b, _, rfl⟩ := h
  exact ⟨b 0, ⟨0, rfl⟩⟩

private theorem valuation_cast {P : Type} {n m : ℕ} (h : n = m)
    (ν : TransitionAlphabet P n) : (h ▸ ν : TransitionAlphabet P m) = ν := by
  cases h
  rfl

/--
---
conclusion: Lax369799.ModalTransitions.run_marking
---
Mark every successor by the word state reached through a direction of
the run. Determinism supplies a successor for each supported type, and
every decoded edge is covered by its direction's type. At a leaf the
assumed final-state test supplies the nullary disjunct.
-/
theorem run_marking {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    {S : RankedSystems.System (TransitionAlphabet P) 0} (r : Run M S)
    (q : Fin M.condition.states) (v : S.val.Vertex)
    (hfinal : ∀ h : Rank S v = 0,
      M.condition.step q (.inr (r.leafType v h)) ∈ M.condition.final) :
    OneStep M q (decode S) v (marking M r q v) := by
  classical
  by_cases hv : Rank S v = 0
  · apply Or.inl
    refine ⟨⟨r.leafType v hv, ?_, hfinal hv⟩, ?_⟩
    · have h := r.leaves v hv
      simpa only [valuation_cast, decode] using h
    · rintro w ⟨d, hd⟩
      have hlt := S.val.graph.direction_valid _ _ _ hd
      change d < Rank S v at hlt
      omega
  · apply Or.inr
    refine ⟨Set.range (r.edgeType v), ?_, ?_, ?_⟩
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hv
      refine ⟨n, (fun i => r.edgeType v (Fin.cast hn.symm i)), ?_, ?_⟩
      · have h := r.transitions v n hn
        simpa only [valuation_cast, decode] using h
      · ext b
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨Fin.cast hn.symm i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨Fin.cast hn i, rfl⟩
    · rintro b ⟨i, rfl⟩
      obtain ⟨t, ht, _⟩ := S.property.2.2 v i.val i.isLt
      cases t with
      | inr j => exact Fin.elim0 j
      | inl w => exact ⟨w, ⟨i.val, ht⟩, ⟨i, ht, rfl⟩⟩
    · rintro w ⟨d, hd⟩
      let i : Fin (Rank S v) := ⟨d, S.val.graph.direction_valid _ _ _ hd⟩
      exact ⟨r.edgeType v i, ⟨i, rfl⟩, ⟨i, hd, rfl⟩⟩

end Lax369799Proofs.ModalTransitions
