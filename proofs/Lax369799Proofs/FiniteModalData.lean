import Lax369799.FiniteModalData
import Lax369799Proofs.PriorityCompilation
import Lax369799Proofs.ModalTransitions
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Finset.Sort

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteModalData
open Lax369799
open ModalMuCalculus TransitionSystems TransitionEncoding UnfoldAutomata
open Lax369799.FiniteModalData

theorem mem_elements (α : Type) [Fintype α] [Encodable α] (a : α) : a ∈ elements α := by
  simp only [elements,Finset.mem_sort,Finset.mem_univ]

private theorem valuation_iff {P : Type} [Fintype P] [Encodable P] {n : ℕ} (ν : P → Bool)
    (S : TransitionSystem P) (ρ : Fin n → Set S.Vertex) (v : S.Vertex) :
    v ∈ (valuationFormula ν).eval S ρ ↔ S.valuation v = {p | ν p = true} := by
  have he : v ∈ (valuationFormula ν).eval S ρ ↔
      ∀ p,if ν p then p ∈ S.valuation v else p ∉ S.valuation v := by
    simp only [valuationFormula,ModalTransitions.eval_conjunction,List.forall_mem_map,
      mem_elements,forall_true_left]
    apply forall_congr'
    intro p
    cases hp : ν p <;> simp [Formula.eval]
  rw [he]
  constructor
  · intro h
    ext p
    specialize h p
    cases hp : ν p <;> simp_all
  · intro h p
    rw [h]
    cases hp : ν p <;> simp [hp]

private theorem support_iff {P : Type} {u z d p : ℕ} (t : Data P u z d p) (q : Fin d)
    (B : Fin u → Bool) (S : TransitionSystem P) (ρ : Fin d → Set S.Vertex) (v : S.Vertex) :
    v ∈ (supportFormula t q B).eval S ρ ↔
      (∀ b,B b = true → ∃ w,S.edge v w ∧ w ∈ ρ (t.2.1 q (.inl b))) ∧
      (∀ w,S.edge v w → ∃ b,B b = true ∧ w ∈ ρ (t.2.1 q (.inl b))) := by
  simp [supportFormula,Formula.eval,ModalTransitions.eval_conjunction,ModalTransitions.eval_disjunction,mem_elements]

private theorem encode_set {V : Type} (X : Set V) : ∃ b : V → Bool,{v | b v = true} = X := by
  classical
  exact ⟨fun v => decide (v ∈ X),by ext v;exact decide_eq_true_iff⟩

private theorem table_correct {P : Type} [Fintype P] [Encodable P] [DecidableEq P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) {p : ℕ}
    (t : Data P M.unary M.nullary M.condition.states p)
    (hstep : t.2.1 = M.condition.step)
    (hfinal : ∀ r,t.2.2.2.1 r = true ↔ r ∈ M.condition.final)
    (hl : ∀ ν a,t.2.2.2.2.1 ν a = true ↔ a ∈ M.leafTransition {p | ν p = true})
    (hs : ∀ ν B,t.2.2.2.2.2 ν B = true ↔ ModalTransitions.Realized M {p | ν p = true} {b | B b = true})
    (q : Fin M.condition.states) (S : TransitionSystem P)
    (ρ : Fin M.condition.states → Set S.Vertex) (v : S.Vertex) :
    v ∈ (transition t q).eval S ρ ↔ ModalTransitions.OneStep M q S v ρ := by
  classical
  simp [transition,ModalTransitions.eval_disjunction,Formula.eval,valuation_iff,
    ModalTransitions.leaf_iff,support_iff,mem_elements]
  simp only [hl,hs,hfinal,hstep]
  unfold ModalTransitions.OneStep
  constructor
  · rintro ⟨ν,hν,h⟩
    rw [hν]
    rcases h with hleaf | ⟨B,hB,hreq,hcover⟩
    · exact Or.inl hleaf
    · exact Or.inr ⟨_,hB,hreq,hcover⟩
  · intro h
    obtain ⟨ν,hν⟩ := encode_set (S.valuation v)
    refine ⟨ν,hν.symm,?_⟩
    rw [hν]
    rcases h with hleaf | ⟨B,hB,hreq,hcover⟩
    · exact Or.inl hleaf
    · obtain ⟨b,hb⟩ := encode_set B
      apply Or.inr
      refine ⟨b,?_,?_,?_⟩
      · rw [hb];exact hB
      · intro a ha
        exact hreq a (by change a ∈ {v | b v = true} at ha;rw [hb] at ha;exact ha)
      · intro w hw
        obtain ⟨a,ha,hh⟩ := hcover w hw
        exact ⟨a,by change a ∈ {v | b v = true};rw [hb];exact ha,hh⟩

/--
---
conclusion: Lax369799.FiniteModalData.exists_table
---
Encode the word condition, leaf tests and realized supports as finite
Boolean tables. The executable modal compiler has the same one-step
semantics as the original automaton, so priority compilation proves
correctness on every finite transition system.
-/
theorem exists_table {P : Type} [Fintype P] [Encodable P] [DecidableEq P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (p : ℕ)
    (hp : ∀ q,M.condition.priority q ≤ p) :
    ∃ t : Data P M.unary M.nullary M.condition.states p,
      ∀ S,Models S (compile t) ↔ ParityWinningRegions.Winning (ModalAcceptanceGame.game M S) true
        (ModalAcceptanceGame.position M.condition.initial S.initial) := by
  classical
  let t : Data P M.unary M.nullary M.condition.states p :=
    ⟨M.condition.initial,M.condition.step,(fun q => ⟨M.condition.priority q,Nat.lt_succ_of_le (hp q)⟩),
      (fun q => decide (q ∈ M.condition.final)),
      (fun ν a => decide (a ∈ M.leafTransition {p | ν p = true})),
      (fun ν B => decide (ModalTransitions.Realized M {p | ν p = true} {b | B b = true}))⟩
  refine ⟨t,?_⟩
  intro S
  have ht (q ρ v) : v ∈ (transition t q).eval S ρ ↔ ModalTransitions.OneStep M q S v ρ :=
    table_correct M t rfl (fun _ => decide_eq_true_iff)
      (fun _ _ => decide_eq_true_iff) (fun _ _ => decide_eq_true_iff) q S ρ v
  exact PriorityCompilation.sentence_correct M (transition t) S ht

end Lax369799Proofs.FiniteModalData
