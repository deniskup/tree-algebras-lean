import Lax369799Proofs.SupportedCompletion
import Lax369799.BisimAutomatonTheorem
import Lax369799Proofs.BoundedProfileRefinement
import Lax369799Proofs.UnfoldEquivalence
import Lax369799Proofs.ParallelCompression
import Lax369799Proofs.CloneRunRefinement
import Lax369799Proofs.RunAcceptance

namespace Lax369799Proofs.CloneCompression
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet System)
open FinitePresentations SetSystemAlgebras TransitionEncoding UnfoldAutomata
open FiniteContextualOrder (Carrier)
open FiniteAcceptance ExpandedSyntacticAlgebra ExpandedTransitions RunPresentations
open Lax369799.DirectionReindexing

private noncomputable def localValue {Y : RankedSet} (E : FiniteSyntacticAlgebra.Algebra Y)
    (n : ℕ) (b : Fin n → Y 1) (z : n = 0 → Y 0) : Y n :=
  if h : n = 0 then h.symm ▸ z h else E.eval n (ofSetSystem (DeterministicElements.parallel b))

private noncomputable def localPiece {Y : RankedSet} (E : FiniteSyntacticAlgebra.Algebra Y)
    (n : ℕ) (b : Fin n → Y 1) (z : n = 0 → Y 0) : FiniteSystem Y n :=
  if n = 0 then atomic (localValue E n b z) else ofSetSystem (DeterministicElements.parallel b)

private theorem rename_nullary {Y : RankedSet} (a : Y 0) (σ : Fin 0 → Fin 0) :
    PortReindexing.rename (atomic a) σ = atomic a := by
  unfold PortReindexing.rename atomic ofSetSystem RankedSystems.atomic
  congr 1
  congr 1
  funext v d t
  apply propext
  cases t with
  | inl w => exact Iff.rfl
  | inr i => exact Fin.elim0 i

private theorem rename_cast_nullary {Y : RankedSet} (E : SetAlgebra Y)
    {m n : ℕ} (hm : m = 0) (hn : n = 0) (a : Y 0) (σ : Fin m → Fin n) :
    E.eval n (PortReindexing.rename (atomic (hm.symm ▸ a)) σ) = hn.symm ▸ a := by
  cases hm
  cases hn
  rw [rename_nullary, E.unit]

private theorem local_compression {Y : RankedSet} (E : SetAlgebra Y) (n k : ℕ) (hk : 0 < k)
    (b : Fin (n * k) → Y 1) (z : n * k = 0 → Y 0) :
    E.eval n (PortReindexing.rename (localPiece E.toAlgebra (n * k) b z) (fun i => i.divNat)) =
      localValue E.toAlgebra n (CloneTransitions.compress E b)
        (fun h => z (by rw [h]; exact Nat.zero_mul k)) := by
  cases n with
  | zero =>
    simp only [localPiece, if_pos (Nat.zero_mul k), localValue,
      dif_pos (Nat.zero_mul k)]
    exact rename_cast_nullary E (Nat.zero_mul k) rfl _ _
  | succ n =>
    have hn : n + 1 ≠ 0 := Nat.succ_ne_zero _
    have hnk : (n + 1) * k ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos _) hk)
    simp only [localPiece, if_neg hnk, localValue, dif_neg hn]
    exact (ParallelCompression.evaluation b E).symm

def duplication {P : Type} (S : System (TransitionAlphabet P) 0) (k : ℕ) (hk : 0 < k) : Reindexing S where
  arity := fun v => Rank S v * k
  map := fun _ i => i.divNat
  surjective := by
    intro v i
    refine ⟨finProdFinEquiv (i, ⟨0, hk⟩), ?_⟩
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, (⟨0, hk⟩ : Fin k)))

variable {P : Type} (L : Algebras.Language (TransitionAlphabet P))
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (ES : SetAlgebra (Carrier (Accepting L))) (hES : ES.toAlgebra = E.algebra)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    (S : System (TransitionAlphabet P) 0) (k : ℕ) (hk : 0 < k)
    (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) (DirectionReindexing.system S (duplication S k hk)))

noncomputable def compressed : Labelling (Fintype.card (Carrier (Accepting L) 1))
    (Fintype.card (Carrier (Accepting L) 0)) S where
  edgeType := fun v i => (Fintype.equivFin (Carrier (Accepting L) 1))
    (CloneTransitions.compress ES
      (fun j => (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v j)) i)
  leafType := fun v h => r.leafType v (by change Rank S v * k = 0; rw [h]; exact Nat.zero_mul k)

include hES in
theorem evaluation :
    E.algebra.eval 0 (withLabels (ofSetSystem S.val)
      (runLabel L E D (compressed L ES S k hk r))) =
    E.algebra.eval 0 (withLabels (ofSetSystem (DirectionReindexing.system S (duplication S k hk)).val)
      (runLabel L E D r)) := by
  have h := PortReindexing.evaluation S (duplication S k hk) (piece L E D r) ES
  have hleft (v : S.val.Vertex) :
      ES.eval _ (PortReindexing.rename (piece L E D r v) ((duplication S k hk).map v)) =
        runLabel L E D (compressed L ES S k hk r) v := by
    have hh := local_compression ES (Rank S v) k hk
      (fun i => (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v i))
      (fun h => (Fintype.equivFin (Carrier (Accepting L) 0)).symm (r.leafType v h))
    rw [hES] at hh
    change ES.toAlgebra.eval _ _ = _
    rw [hES]
    simpa only [localPiece, localValue, piece, runLabel, compressed, Equiv.symm_apply_apply, Rank, DirectionReindexing.system, DirectionReindexing.graph, duplication] using hh
  have hright (v : S.val.Vertex) : ES.eval _ (piece L E D r v) = runLabel L E D r v := by
    change ES.toAlgebra.eval _ _ = _
    rw [hES]
    unfold piece
    split_ifs with hv
    · exact E.algebra.unit _ _
    · unfold runLabel
      rw [dif_neg hv]
  have hl : (fun v => ES.eval _ (PortReindexing.rename (piece L E D r v) ((duplication S k hk).map v))) =
      runLabel L E D (compressed L ES S k hk r) := funext hleft
  have hr : (fun v => ES.eval _ (piece L E D r v)) = runLabel L E D r := funext hright
  have hl' := congrArg (fun q => ES.eval 0 (withLabels (ofSetSystem S.val) q)) hl
  have hr' := congrArg (fun q => ES.eval 0
    (withLabels (ofSetSystem (DirectionReindexing.system S (duplication S k hk)).val) q)) hr
  have hf := hl'.symm.trans (h.trans hr')
  change ES.toAlgebra.eval _ _ = ES.toAlgebra.eval _ _ at hf
  rwa [hES] at hf

end Lax369799Proofs.CloneCompression

namespace Lax369799Proofs.CloneNormalization
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet System)
open FinitePresentations SetSystemAlgebras TransitionEncoding UnfoldAutomata
open FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra ExpandedSyntacticAlgebra
open Lax369799.DirectionReindexing
open CloneCompression

variable {P : Type} (L : Algebras.Language (TransitionAlphabet P))
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (ES : SetAlgebra (Carrier (Accepting L))) (hES : ES.toAlgebra = E.algebra)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))

private def table (ν : Set P) (n : ℕ) : Set (Fin (n + 1) → Carrier (Accepting L) 1) :=
  {b | (∀ i, ExtremalUnaryTypes.Selected L E (b i)) ∧
    ClassBelow (Accepting L) (E.algebra.eval (n + 1) (ofSetSystem (DeterministicElements.parallel b)))
      (quotientMap (Accepting L) _ (atomic ν))}

private noncomputable def leaves (ν : Set P) : Set (Fin (Fintype.card (Carrier (Accepting L) 0))) :=
  {(Fintype.equivFin (Carrier (Accepting L) 0)) (quotientMap (Accepting L) 0 (atomic ν))}

noncomputable def machine :=
  CloneTransitions.automaton (CloneTransitions.beta ES (table L E)) (leaves L) D

private theorem valuation_cast {P : Type} {n m : ℕ} (h : n = m)
    (ν : TransitionAlphabet P n) : (h ▸ ν : TransitionAlphabet P m) = ν := by cases h; rfl

private theorem cast_membership {H : Type} (B : ∀ n, Set (Fin n → H)) {n m : ℕ}
    (h : n = m) (b : Fin n → H) (hb : b ∈ B n) :
    (fun i => b (Fin.cast h.symm i)) ∈ B m := by cases h; exact hb

private theorem closure_of_mem {H : Type} (B : ∀ n, Set (Fin n → H)) {n : ℕ}
    (hn : 0 < n) (b : Fin n → H) (hb : b ∈ B n) : b ∈ CloneTransitions.Closure B n := by
  refine ⟨n, 1, hn, by decide, Nat.mul_one n, b, hb, ?_⟩
  funext i
  apply congrArg b
  apply Fin.ext
  simp [Fin.divNat]

private theorem compressed_mem
    (S : System (TransitionAlphabet P) 0) (k : ℕ) (hk : 0 < k)
    (r : Run (ExpandedTransitions.automaton L E D) (system S (duplication S k hk)))
    (ht : ∀ v, CloneTransitions.alpha ES (table L E) (S.val.graph.label v).2 (Rank S v) k ⊆
      CloneTransitions.beta ES (table L E) (S.val.graph.label v).2 (Rank S v))
    (v : S.val.Vertex) (hv : Rank S v ≠ 0) :
    CloneTransitions.compress ES (fun i => (Fintype.equivFin (Carrier (Accepting L) 1)).symm
      (r.edgeType v i)) ∈ CloneTransitions.beta ES (table L E) (S.val.graph.label v).2 (Rank S v) := by
  apply ht v
  have hpos : 0 < Rank S v * k := Nat.mul_pos (Nat.pos_of_ne_zero hv) hk
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  let b : Fin (l + 1) → Carrier (Accepting L) 1 := fun i =>
    (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v (Fin.cast hl.symm i))
  refine ⟨l, hl, b, ?_, ?_⟩
  · have h := r.transitions v l hl
    simp only [ExpandedTransitions.automaton, valuation_cast] at h
    exact h
  · rfl

private noncomputable def compressedRun
    (S : System (TransitionAlphabet P) 0) (k : ℕ) (hk : 0 < k)
    (r : Run (ExpandedTransitions.automaton L E D) (system S (duplication S k hk)))
    (ht : ∀ v, CloneTransitions.alpha ES (table L E) (S.val.graph.label v).2 (Rank S v) k ⊆
      CloneTransitions.beta ES (table L E) (S.val.graph.label v).2 (Rank S v)) : Run (machine L E ES D) S where
  edgeType := (compressed L ES S k hk r.toLabelling).edgeType
  leafType := (compressed L ES S k hk r.toLabelling).leafType
  transitions := by
    intro v n hn
    have hb := compressed_mem L E ES D S k hk r ht v (by omega)
    have hc := closure_of_mem (CloneTransitions.beta ES (table L E) (S.val.graph.label v).2)
      (by omega : 0 < Rank S v) _ hb
    have hc' := cast_membership
      (CloneTransitions.Closure (CloneTransitions.beta ES (table L E) (S.val.graph.label v).2)) hn _ hc
    simp only [machine, CloneTransitions.automaton, valuation_cast]
    simpa only [compressed, Equiv.symm_apply_apply, Set.mem_ofPred_eq] using hc'
  leaves := by
    intro v hv
    have h := r.leaves v (by change Rank S v * k = 0; rw [hv]; exact Nat.zero_mul k)
    simp only [machine, CloneTransitions.automaton, ExpandedTransitions.automaton, valuation_cast] at h ⊢
    exact h

include hES in
private theorem word_monotone (hD : RunAcceptance.WordCorrect L E D) :
    Lax369799.BranchMonotonicity.ConditionMonotone ES D := by
  apply BranchMonotonicity.condition ES {a | AcceptingClass (Accepting L) a} ?_ D ?_
  · intro a b ha hab
    apply (FiniteSyntacticAlgebra.accepting_classes (Accepting L) (FiniteAcceptance.accepting_isomorphic L)).2 _ _ ha
    apply (SetSystemAlgebras.syntactic_order L E a b).mpr
    change sumValue ES.toAlgebra a b = a at hab
    rwa [hES] at hab
  · simpa only [hES, RunAcceptance.WordCorrect, Set.mem_ofPred_eq] using hD

include hES in
theorem sound
    (hL : ∀ S T, RankedBisimilar S T → (S ∈ L ↔ T ∈ L)) (hrec : Algebras.Recognizable L)
    (hD : RunAcceptance.WordCorrect L E D) (S : System (TransitionAlphabet P) 0)
    (r : Run (machine L E ES D) S) (hr : r.Accepting) : S ∈ L := by
  obtain ⟨U, hU, s, hs⟩ := CloneRunRefinement.run_refinement ES (table L E) (leaves L) D S r
    (word_monotone L E ES hES D hD) hr
  have hinv : Algebras.UnfoldInvariantLanguage L := fun A B h => hL A B (.rel _ _ (.inl h))
  have hu := ExpandedTransitions.evaluated_run_sound L hinv E D s
    (RunAcceptance.accepting_run_value L E D s hinv hrec hD hs)
  exact (hL U S (.rel _ _ (.inr hU))).mp hu

include hES in
theorem complete
    (hL : ∀ S T, RankedBisimilar S T → (S ∈ L ↔ T ∈ L)) (hrec : Algebras.Recognizable L)
    (hD : RunAcceptance.WordCorrect L E D) (S : System (TransitionAlphabet P) 0) (hS : S ∈ L) :
    ∃ r : Run (machine L E ES D) S, r.Accepting := by
  classical
  obtain ⟨N, hN⟩ := CloneTransitions.uniform_stabilization ES (table L E)
    (fun v : S.val.Vertex => (S.val.graph.label v).2) (Rank S)
  let k := N + 1
  have hk : 0 < k := Nat.succ_pos _
  let U := system S (duplication S k hk)
  have hU : U ∈ L := (hL U S (.rel _ _ (.inr
    (DirectionReindexing.decode_isomorphic _ (realizes S (duplication S k hk)))))).mpr hS
  have hinv : Algebras.UnfoldInvariantLanguage L := fun A B h => hL A B (.rel _ _ (.inl h))
  obtain ⟨r, hr⟩ := ExpandedTransitions.evaluated_run_exists L hinv hrec E D U hU
  let s := compressedRun L E ES D S k hk r (fun v => hN v k (Nat.le_succ _))
  refine ⟨s, ?_⟩
  have hv := CloneCompression.evaluation L E ES hES D S k hk r.toLabelling
  have hs : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (ExpandedTransitions.runLabel L E D
        (compressed L ES S k hk r.toLabelling)))) := by
    rw [hv]
    exact hr
  exact RunAcceptance.labelling_accepting L E D _ hD hs

/--
---
conclusion: Lax369799.BisimAutomatonTheorem.bisim_automaton_runs
---
Choose the finite syntactic unary and nullary sorts and their algebraic
branch condition. Stabilization compresses an accepted duplicated run
into the recurrent clone table. Conversely, rerouting lifts a clone run
to an original run with larger labels and isomorphic decoding.
-/
theorem bisim_automaton_runs {P : Type} [Finite P]
    (L : Algebras.Language (TransitionAlphabet P))
    (hL : ∀ S T, RankedBisimilar S T → (S ∈ L ↔ T ∈ L))
    (hA : SupportedAlgebras.Recognizable L) :
    ∃ M : UnfoldAutomaton (TransitionAlphabet P),
      BisimAutomata.IsBisimAutomaton M ∧ UnfoldAutomata.Recognizes M L ∧
        ∀ S ∈ L, ∃ r : Run M S, r.Accepting := by
  classical
  have hA : Algebras.Recognizable L := SupportedCompletion.legacy_recognizable L hA
  have hinv : Algebras.UnfoldInvariantLanguage L := fun A B h => hL A B (.rel _ _ (.inl h))
  letI : Finite (Carrier (Accepting L) 1) := BoundedProfileRefinement.finite_carrier_recognizable L hinv hA 1
  letI : Finite (Carrier (Accepting L) 0) := BoundedProfileRefinement.finite_carrier_recognizable L hinv hA 0
  letI : Fintype (Carrier (Accepting L) 1) := Fintype.ofFinite _
  letI : Fintype (Carrier (Accepting L) 0) := Fintype.ofFinite _
  obtain ⟨E⟩ := ExpandedSyntacticAlgebra.syntactic_algebra_exists L
  obtain ⟨ES, hES⟩ := SetSystemAlgebras.syntactic_structure L E
  obtain ⟨D, hD⟩ := RunAcceptance.exists_condition L E
  refine ⟨machine L E ES D, CloneTransitions.clone_automaton _ _ _, ?_,
    fun S hS => complete L E ES hES D hL hA hD S hS⟩
  intro S
  constructor
  · intro hS
    obtain ⟨r, hr⟩ := complete L E ES hES D hL hA hD S hS
    exact ⟨S, (MorphismTheorems.unfold_equivalence _ _).refl S.val, r, hr⟩
  · rintro ⟨U, hU, r, hr⟩
    exact (hinv S U hU).mpr (sound L E ES hES D hL hA hD U r hr)

/--
---
conclusion: Lax369799.BisimAutomatonTheorem.bisim_automaton_exists
---
Forget the additional accepting-run guarantee.
-/
theorem bisim_automaton_exists {P : Type} [Finite P]
    (L : Algebras.Language (TransitionAlphabet P))
    (hL : ∀ S T, RankedBisimilar S T → (S ∈ L ↔ T ∈ L))
    (hA : SupportedAlgebras.Recognizable L) :
    ∃ M : UnfoldAutomaton (TransitionAlphabet P),
      BisimAutomata.IsBisimAutomaton M ∧ UnfoldAutomata.Recognizes M L := by
  obtain ⟨M, hM, hML, _⟩ := bisim_automaton_runs L hL hA
  exact ⟨M, hM, hML⟩

end Lax369799Proofs.CloneNormalization
