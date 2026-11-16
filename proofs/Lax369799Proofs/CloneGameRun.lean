import Lax369799.CloneGameRun
import Lax369799Proofs.ModalAcceptanceGame
import Lax369799Proofs.ParityWinningRegions
import Lax369799Proofs.Yields
import Lax369799Proofs.AutomatonRunGame
import Mathlib.Logic.Equiv.Fin.Basic

namespace Lax369799Proofs.CloneGameRun
set_option backward.isDefEq.respectTransparency false
open Lax369799
open TransitionEncoding TransitionSystems UnfoldAutomata ModalTransitions BisimAutomata
open ModalAcceptanceGame FiniteParityGames ParityWinningRegions
open RankedSystems

abbrev Good {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P)
    (f : Vertex M S → Vertex M S) :=
  {s : Fin M.condition.states × S.Vertex // (game M S).WinsFrom true f (position s.1 s.2)}

private theorem chosen_marking {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (f : Vertex M S → Vertex M S) (hf : (game M S).Legal true f)
    (s : Good M S f) : ∃ ρ : Marking M S,
      f (position s.val.1 s.val.2) = selection s.val.2 ρ ∧ OneStep M s.val.1 S s.val.2 ρ ∧
        ∀ q w, S.edge s.val.2 w → w ∈ ρ q →
          (game M S).WinsFrom true f (position q w) := by
  have he := hf (position s.val.1 s.val.2) (by simp [game, eve, position])
  have hw := ParityWinningRegions.move (game M S) true f _ _ s.property he (fun _ => rfl)
  cases h : f (position s.val.1 s.val.2) with
  | inl t => rw [h] at he; exact he.elim
  | inr t =>
    cases t with
    | inl t =>
      rw [h] at he hw
      have hst : s.val.2 = t.1 ∧ OneStep M s.val.1 S s.val.2 t.2 := he
      obtain ⟨v, ρ⟩ := t
      dsimp at hst
      obtain ⟨hv, hstep⟩ := hst
      subst v
      refine ⟨ρ, rfl, hstep, ?_⟩
      intro q w hew hρ
      exact ParityWinningRegions.move (game M S) true f _ _ hw ⟨hew, hρ⟩
        (fun heve => (heve.mpr rfl).elim)
    | inr b =>
      cases b with
      | false =>
        rw [h] at hw
        exact (Bool.false_ne_true ((ModalAcceptanceGame.terminal_winning M S false).mp
          ⟨f, hf, hw⟩)).elim
      | true => rw [h] at he; exact he.elim

private theorem finite_onto {W : Type} [Fintype W] [Nonempty W] (n : ℕ)
    (hn : Fintype.card W ≤ n) : ∃ f : Fin n → W, Function.Surjective f := by
  let e := Fintype.equivFin W
  let f : Fin n → W := fun i => e.symm ⟨i.val % Fintype.card W, Nat.mod_lt _ Fintype.card_pos⟩
  refine ⟨f, ?_⟩
  intro w
  let i : Fin n := ⟨(e w).val, (e w).isLt.trans_le hn⟩
  refine ⟨i, ?_⟩
  change e.symm ⟨(e w).val % Fintype.card W, _⟩ = w
  have he : (⟨(e w).val % Fintype.card W, Nat.mod_lt _ Fintype.card_pos⟩ : Fin (Fintype.card W)) = e w :=
    Fin.ext (Nat.mod_eq_of_lt (e w).isLt)
  rw [he, e.symm_apply_apply]

structure Row {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (f : Vertex M S → Vertex M S) (s : Good M S f) where
  arity : ℕ
  types : Fin arity → Fin M.unary
  next : Fin arity → Good M S f
  marking : Marking M S
  chosen : f (position s.val.1 s.val.2) = selection s.val.2 marking
  transitions : ∀ k (h : arity = k+1),
    (fun i => types (Fin.cast h.symm i)) ∈ M.transition k (S.valuation s.val.2)
  leaf : arity = 0 → Fin M.nullary
  leaves : ∀ h, leaf h ∈ M.leafTransition (S.valuation s.val.2)
  final : ∀ h, M.condition.step s.val.1 (.inr (leaf h)) ∈ M.condition.final
  edge : ∀ i, S.edge s.val.2 (next i).val.2
  response : ∀ i, (next i).val.2 ∈ marking (next i).val.1
  state : ∀ i, (next i).val.1 = M.condition.step s.val.1 (.inl (types i))
  cover : ∀ w, S.edge s.val.2 w → ∃ i, (next i).val.2 = w

theorem row_exists {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (hM : IsBisimAutomaton M) (S : TransitionSystem P) (f : Vertex M S → Vertex M S)
    (hf : (game M S).Legal true f) (s : Good M S f) : Nonempty (Row M S f s) := by
  classical
  obtain ⟨ρ, hchosen, hρ, hgood⟩ := chosen_marking M S f hf s
  rcases hρ with ⟨⟨a, ha, hfinal⟩, hno⟩ | ⟨B, ⟨n, b, hb, hB⟩, hl, hr⟩
  · exact ⟨{
      arity := 0
      types := Fin.elim0
      next := Fin.elim0
      marking := ρ
      chosen := hchosen
      transitions := fun k h => by omega
      leaf := fun _ => a
      leaves := fun _ => ha
      final := fun _ => hfinal
      edge := fun i => Fin.elim0 i
      response := fun i => Fin.elim0 i
      state := fun i => Fin.elim0 i
      cover := fun w hw => (hno w hw).elim }⟩
  · have hsize : 0 < S.size := Nat.zero_le S.initial.val |>.trans_lt S.initial.isLt
    let W := fun i : Fin (n+1) =>
      {w : S.Vertex // S.edge s.val.2 w ∧ w ∈ ρ (M.condition.step s.val.1 (.inl (b i)))}
    have hex : ∀ i, ∃ g : Fin S.size → W i, Function.Surjective g := by
      intro i
      have hbi : b i ∈ B := hB ▸ Set.mem_range_self i
      obtain ⟨w, hw, hwρ⟩ := hl (b i) hbi
      let : Nonempty (W i) := ⟨w, hw, hwρ⟩
      exact finite_onto S.size ((Fintype.card_subtype_le _).trans_eq (Fintype.card_fin S.size))
    choose g hg using hex
    obtain ⟨k, hk, hclone⟩ := hM (S.valuation s.val.2) n b hb S.size hsize
    let nxt : Fin ((n+1)*S.size) → Good M S f := fun i =>
      ⟨(M.condition.step s.val.1 (.inl (b i.divNat)), (g i.divNat i.modNat).val),
        hgood _ _ (g i.divNat i.modNat).property.1 (g i.divNat i.modNat).property.2⟩
    refine ⟨{
      arity := (n+1)*S.size
      types := Duplicate b
      next := nxt
      marking := ρ
      chosen := hchosen
      transitions := ?_
      leaf := fun h => (by omega : False).elim
      leaves := fun h => (by omega : False).elim
      final := fun h => (by omega : False).elim
      edge := fun i => (g i.divNat i.modNat).property.1
      response := fun i => (g i.divNat i.modNat).property.2
      state := fun _ => rfl
      cover := ?_ }⟩
    · intro j hj
      have hkj : j = k := by omega
      subst j
      exact hclone
    · intro w hw
      obtain ⟨a, ha, hwρ⟩ := hr w hw
      obtain ⟨i, rfl⟩ := hB.symm ▸ ha
      obtain ⟨j, hj⟩ := hg i ⟨w, hw, hwρ⟩
      let d := finProdFinEquiv (i, j)
      have hd : (d.divNat, d.modNat) = (i, j) := finProdFinEquiv.symm_apply_apply (i, j)
      refine ⟨d, ?_⟩
      change (g d.divNat d.modNat).val = w
      have hd₁ : d.divNat = i := congrArg Prod.fst hd
      have hd₂ : d.modNat = j := congrArg Prod.snd hd
      rw [hd₁, hd₂]
      exact congrArg Subtype.val hj

private theorem valuation_cast {P : Type} {n m : ℕ} (h : n = m)
    (ν : TransitionAlphabet P n) : (h ▸ ν : TransitionAlphabet P m) = ν := by
  cases h
  rfl

private theorem fold_states {α β : Type} (f : α → β → α) (N : ℕ)
    (s : Fin (N+1) → α) (w : Fin N → β)
    (hs : ∀ i : Fin N, s i.succ = f (s i.castSucc) (w i)) :
    (List.ofFn w).foldl f (s 0) = s (Fin.last N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.ofFn_succ_last, List.foldl_append]
    have h := ih (fun i => s i.castSucc) (fun i => w i.castSucc) (fun i => hs i.castSucc)
    change (List.ofFn (fun i => w i.castSucc)).foldl f (s 0) = s (Fin.last N).castSucc at h
    simp only [List.foldl_cons, List.foldl_nil]
    rw [h]
    exact (hs (Fin.last N)).symm

/--
---
conclusion: Lax369799.CloneGameRun.winning_run
---
The finite strategy graph records the word state and input vertex.
Uniform duplication realizes each marking while covering all input
successors. Trimming preserves the run and the bisimulation projection.
Finite branches use final states; infinite branches follow the winning
strategy and therefore satisfy the word parity condition.
-/
theorem winning_run {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (hM : IsBisimAutomaton M) (S : TransitionSystem P)
    (hwin : Winning (game M S) true (position M.condition.initial S.initial)) :
    ∃ U : RankedSystems.System (TransitionAlphabet P) 0,
      Bisimilar (decode U) S ∧ ∃ r : Run M U, r.Accepting := by
  classical
  obtain ⟨f, hf, hstart⟩ := hwin
  let s₀ : Good M S f := ⟨(M.condition.initial, S.initial), hstart⟩
  let row : ∀ s : Good M S f, Row M S f s := fun s => Classical.choice (row_exists M hM S f hf s)
  let G : Presentation (TransitionAlphabet P) 0 (Good M S f) := {
    label := fun s => ⟨(row s).arity, S.valuation s.val.2⟩
    initial := {s₀}
    root := ∅
    edge := fun s d t => ∃ i : Fin (row s).arity, d = i.val ∧ t = .inl ((row s).next i)
    direction_valid := by rintro s d t ⟨i, rfl, _⟩; exact i.isLt }
  have hdet := Yields.trim_deterministic G s₀ rfl rfl (by
    intro s d hd
    refine ⟨.inl ((row s).next ⟨d, hd⟩), ⟨⟨d, hd⟩, rfl, rfl⟩, ?_⟩
    rintro t ⟨i, hi, rfl⟩
    have he : i = (⟨d, hd⟩ : Fin (row s).arity) := Fin.ext hi.symm
    rw [he])
  let U : RankedSystems.System (TransitionAlphabet P) 0 := ⟨trim G, hdet⟩
  let π : U.val.Vertex → Good M S f := Pullbacks.vertex G
  have hinit : ∀ v, v ∈ U.val.graph.initial → π v = s₀ := fun _ h => h
  have hroot : π (decode U).initial = s₀ := by
    apply hinit
    have hi := congrArg (fun I : Set U.val.Vertex => (decode U).initial ∈ I)
      (Classical.choose_spec U.property.1)
    exact hi.mpr rfl
  have hnext : ∀ v (i : Fin (Rank U v)) w,
      U.val.graph.edge v i.val (.inl w) → π w = (row (π v)).next i := by
    intro v i w he
    change ∃ j : Fin (row (π v)).arity, i.val = j.val ∧
      Sum.inl (π w) = Sum.inl ((row (π v)).next j) at he
    obtain ⟨j, hij, ht⟩ := he
    have hij' : i = j := Fin.ext hij
    subst j
    exact Sum.inl.inj ht
  have hsucc : ∀ v (i : Fin (Rank U v)), ∃ w, U.val.graph.edge v i.val (.inl w) := by
    intro v i
    obtain ⟨t, ht, _⟩ := U.property.2.2 v i.val i.isLt
    cases t with
    | inr j => exact Fin.elim0 j
    | inl w => exact ⟨w, ht⟩
  have hbisim : Bisimilar (decode U) S := by
    refine ⟨fun u v => (π u).val.2 = v, ?_, ?_⟩
    · exact congrArg (fun s => s.val.2) hroot
    · intro u v huv
      subst v
      refine ⟨rfl, ?_, ?_⟩
      · rintro w ⟨d, hd⟩
        let i : Fin (Rank U u) := ⟨d, U.val.graph.direction_valid _ _ _ hd⟩
        refine ⟨(π w).val.2, ?_, rfl⟩
        rw [hnext u i w hd]
        exact (row (π u)).edge i
      · intro w hw
        obtain ⟨i, hi⟩ := (row (π u)).cover w hw
        obtain ⟨u', hu'⟩ := hsucc u i
        exact ⟨u', ⟨i.val, hu'⟩, (congrArg (fun s => s.val.2) (hnext u i u' hu')).trans hi⟩
  let r : Run M U := {
    edgeType := fun v i => (row (π v)).types i
    leafType := fun v h => (row (π v)).leaf h
    transitions := by
      intro v k h
      change _ ∈ M.transition k (h ▸ S.valuation (π v).val.2)
      rw [valuation_cast]
      exact (row (π v)).transitions k h
    leaves := by
      intro v h
      change _ ∈ M.leafTransition (h ▸ S.valuation (π v).val.2)
      rw [valuation_cast]
      exact (row (π v)).leaves h }
  refine ⟨U, hbisim, r, ?_, ?_⟩
  · intro N b
    have hs : ∀ i : Fin N, (π (b.vertex i.succ)).val.1 =
        M.condition.step (π (b.vertex i.castSucc)).val.1
          (.inl (r.edgeType (b.vertex i.castSucc) (b.direction i))) := by
      intro i
      rw [hnext _ (b.direction i) _ (b.follows i)]
      exact (row (π (b.vertex i.castSucc))).state (b.direction i)
    have hi : (π (b.vertex 0)).val.1 = M.condition.initial :=
      congrArg (fun s => s.val.1) (hinit _ b.starts)
    have hfold := fold_states (fun q a => M.condition.step q (.inl a)) N
      (fun i => (π (b.vertex i)).val.1)
      (fun i => r.edgeType (b.vertex i.castSucc) (b.direction i)) hs
    rw [hi] at hfold
    unfold WordCondition.AcceptsFinite
    rw [hfold]
    exact (row (π (b.vertex (Fin.last N)))).final b.ends
  · intro b
    let s := fun n => π (b.vertex n)
    let w := fun n => r.edgeType (b.vertex n) (b.direction n)
    have hs0 : s 0 = s₀ := hinit _ b.starts
    have hs : ∀ n, s (n+1) = (row (s n)).next (b.direction n) :=
      fun n => hnext _ (b.direction n) _ (b.follows n)
    have hrun : ∀ n, M.condition.run w n = (s n).val.1 := by
      intro n
      induction n with
      | zero => exact (congrArg (fun s => s.val.1) hs0).symm
      | succ n ih =>
        dsimp only [WordCondition.run]
        rw [ih, hs]
        exact ((row (s n)).state (b.direction n)).symm
    let p : ℕ → Vertex M S := fun n => if n % 2 = 0 then
      position (s (n/2)).val.1 (s (n/2)).val.2 else
      selection (s (n/2)).val.2 (row (s (n/2))).marking
    have pe : ∀ n, p (2*n) = position (s n).val.1 (s n).val.2 := by intro n; simp [p]
    have po : ∀ n, p (2*n+1) = selection (s n).val.2 (row (s n)).marking := by
      intro n
      have hn : (2*n+1)/2 = n := by omega
      dsimp only [p]
      rw [if_neg (by omega : (2*n+1)%2 ≠ 0), hn]
    have hp : (game M S).IsPlay p := by
      intro n
      have hmod := Nat.mod_lt n (by omega : 0 < 2)
      have hdiv := Nat.mod_add_div n 2
      by_cases hn : n % 2 = 0
      · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k := ⟨n/2, by omega⟩
        rw [pe, po, ← (row (s k)).chosen]
        exact hf _ (by simp [game, eve, position])
      · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k+1 := ⟨n/2, by omega⟩
        have heq : 2*k+1+1 = 2*(k+1) := by omega
        rw [po, heq, pe, hs]
        exact ⟨(row (s k)).edge (b.direction k), (row (s k)).response (b.direction k)⟩
    have hc : (game M S).Consistent true f p := by
      intro n hn
      have hmod := Nat.mod_lt n (by omega : 0 < 2)
      have hdiv := Nat.mod_add_div n 2
      by_cases hn0 : n % 2 = 0
      · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k := ⟨n/2, by omega⟩
        rw [pe, po]
        exact (row (s k)).chosen.symm
      · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k+1 := ⟨n/2, by omega⟩
        rw [po] at hn
        exact (hn.mpr rfl).elim
    have hp0 : p 0 = position M.condition.initial S.initial := by rw [pe 0, hs0]
    apply (AutomatonRunGame.parity_interleave M S w p
      (fun n => by rw [pe, hrun]; rfl) (fun n => by rw [po]; rfl)).mpr
    exact (hstart p hp hp0 hc).mpr rfl

end Lax369799Proofs.CloneGameRun
