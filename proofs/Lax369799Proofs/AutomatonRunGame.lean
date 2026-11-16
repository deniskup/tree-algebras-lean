import Lax369799.AutomatonRunGame
import Lax369799Proofs.ModalAcceptanceGame
import Lax369799Proofs.ModalTransitions
import Lax369799Proofs.ParityWinningRegions
import Mathlib.Data.List.OfFn
import Lax369799Proofs.FiniteRecurrence

namespace Lax369799Proofs.AutomatonRunGame
set_option backward.isDefEq.respectTransparency false
open Lax369799
open TransitionEncoding TransitionSystems UnfoldAutomata ModalTransitions
open ModalAcceptanceGame FiniteParityGames ParityWinningRegions

private theorem fold_prefix {α β : Type} (f : α → β → α) (s : ℕ → α)
    (N : ℕ) (w : Fin N → β) (hs : ∀ i : Fin N, s (i.val + 1) = f (s i.val) (w i)) :
    (List.ofFn w).foldl f (s 0) = s N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.ofFn_succ_last, List.foldl_append]
    have h := ih (fun i => w i.castSucc) (fun i => hs i.castSucc)
    simpa only [h, List.foldl_cons, List.foldl_nil, Fin.val_last] using (hs (Fin.last N)).symm

private theorem valuation_cast {P : Type} {n m : ℕ} (h : n = m)
    (ν : TransitionAlphabet P n) : (h ▸ ν : TransitionAlphabet P m) = ν := by
  cases h
  rfl

private theorem next_response {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    {S : RankedSystems.System (TransitionAlphabet P) 0} (r : Run M S)
    (g : Vertex M (decode S) → Vertex M (decode S)) (hg : (game M (decode S)).Legal false g)
    (q : Fin M.condition.states) (v : S.val.Vertex) (hv : Rank S v ≠ 0) :
    ∃ (t : Fin M.condition.states × S.val.Vertex) (i : Fin (Rank S v)),
      S.val.graph.edge v i.val (.inl t.2) ∧
      t.1 = M.condition.step q (.inl (r.edgeType v i)) ∧
      g (selection v (marking M r q v)) = position t.1 t.2 := by
  have he := hg (selection v (marking M r q v)) (by simp [game, eve, selection])
  have hn : ∃ p w, (decode S).edge v w ∧ w ∈ marking M r q v p := by
    let i : Fin (Rank S v) := ⟨0, Nat.pos_of_ne_zero hv⟩
    obtain ⟨t, ht, _⟩ := S.property.2.2 v i.val i.isLt
    cases t with
    | inr j => exact Fin.elim0 j
    | inl w => exact ⟨_, w, ⟨i.val, ht⟩, i, ht, rfl⟩
  cases h : g (selection v (marking M r q v)) with
  | inl t =>
    rw [h] at he
    change (decode S).edge v t.2 ∧ t.2 ∈ marking M r q v t.1 at he
    obtain ⟨i, hi, hq⟩ := he.2
    exact ⟨t, i, hi, hq.symm, rfl⟩
  | inr t =>
    rw [h] at he
    cases t with
    | inl t => exact False.elim he
    | inr b => cases b with
      | false => exact False.elim he
      | true => exact False.elim (he hn)

private theorem interleave_parity {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (w : ℕ → Fin M.unary)
    (p : ℕ → Vertex M S)
    (he : ∀ n, (game M S).priority (p (2*n)) =
      ceiling M.condition - M.condition.priority (M.condition.run w n))
    (ho : ∀ n, (game M S).priority (p (2*n+1)) = 0)
    (hw : M.condition.AcceptsInfinite w) : (game M S).EveWins p := by
  obtain ⟨c, hc, hr, hm⟩ := ModalAcceptanceGame.reverse_parity M.condition w |>.mp hw
  refine ⟨c, ⟨?_, ?_⟩, hc⟩
  · intro N
    obtain ⟨n, hn, heq⟩ := hr N
    exact ⟨2*n, by omega, (he n).trans heq⟩
  · intro b hb hrec
    apply hm b hb
    intro N
    obtain ⟨n, hn, heq⟩ := hrec (2*N)
    have hmod := Nat.mod_lt n (by omega : 0 < 2)
    have hdiv := Nat.mod_add_div n 2
    by_cases hn0 : n % 2 = 0
    · have hn' : n = 2*(n/2) := by omega
      exact ⟨n/2, by omega, (he (n/2)).symm.trans (hn' ▸ heq)⟩
    · have hn' : n = 2*(n/2)+1 := by omega
      have := (ho (n/2)).symm.trans (hn' ▸ heq)
      omega

/--
---
conclusion: Lax369799.AutomatonRunGame.parity_interleave
---
The intermediate selection priorities are zero. Word positions have
positive priorities, so inserting selections preserves the parity test.
-/
theorem parity_interleave {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (w : ℕ → Fin M.unary) (p : ℕ → Vertex M S)
    (he : ∀ n, (game M S).priority (p (2*n)) =
      ceiling M.condition - M.condition.priority (M.condition.run w n))
    (ho : ∀ n, (game M S).priority (p (2*n+1)) = 0) :
    M.condition.AcceptsInfinite w ↔ (game M S).EveWins p := by
  constructor
  · exact interleave_parity M S w p he ho
  · rintro ⟨c, ⟨hr, hm⟩, hc⟩
    have hcpos : 0 < c := by
      obtain ⟨N, hN⟩ := FiniteRecurrence.eventual_subset (fun n => {M.condition.run w n})
      have hrec := hN N le_rfl (Set.mem_singleton (M.condition.run w N))
      have hpos := ModalAcceptanceGame.priority_positive M.condition (M.condition.run w N)
      by_contra hnot
      have hc0 : c = 0 := by omega
      apply hm (ceiling M.condition - M.condition.priority (M.condition.run w N)) (by omega)
      intro K
      obtain ⟨n, hn, heq⟩ := hrec K
      exact ⟨2*n, by omega, (he n).trans (congrArg
        (fun q => ceiling M.condition - M.condition.priority q) heq.symm)⟩
    apply (ModalAcceptanceGame.reverse_parity M.condition w).mpr
    refine ⟨c, hc, ?_, ?_⟩
    · intro N
      obtain ⟨n, hn, heq⟩ := hr (2*N)
      have hmod := Nat.mod_lt n (by omega : 0 < 2)
      have hdiv := Nat.mod_add_div n 2
      by_cases hn0 : n % 2 = 0
      · have hn' : n = 2*(n/2) := by omega
        exact ⟨n/2, by omega, (he (n/2)).symm.trans (hn' ▸ heq)⟩
      · have hn' : n = 2*(n/2)+1 := by omega
        have := (ho (n/2)).symm.trans (hn' ▸ heq)
        omega
    · intro b hb hrec
      apply hm b hb
      intro N
      obtain ⟨n, hn, heq⟩ := hrec N
      exact ⟨2*n, by omega, (he n).trans heq⟩

/--
---
conclusion: Lax369799.AutomatonRunGame.run_winning
---
An opposing positional strategy selects a branch of the run. A first
leaf contradicts finite-branch acceptance; without a leaf, the selected
infinite branch contradicts the opposing strategy's parity guarantee.
-/
theorem run_winning {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    {S : RankedSystems.System (TransitionAlphabet P) 0} (r : Run M S) (hr : r.Accepting) :
    Winning (game M (decode S)) true (position M.condition.initial (decode S).initial) := by
  classical
  let := ModalAcceptanceGame.finite M (decode S)
  by_contra hwin
  obtain ⟨g, hg, hgv⟩ := (ParityWinningRegions.complementary _ _).mpr hwin
  have hchoice : ∀ s : Fin M.condition.states × S.val.Vertex,
      ∃ t : Fin M.condition.states × S.val.Vertex, Rank S s.2 ≠ 0 →
        ∃ i : Fin (Rank S s.2), S.val.graph.edge s.2 i.val (.inl t.2) ∧
          t.1 = M.condition.step s.1 (.inl (r.edgeType s.2 i)) ∧
          g (selection s.2 (marking M r s.1 s.2)) = position t.1 t.2 := by
    intro s
    by_cases hs : Rank S s.2 = 0
    · exact ⟨s, fun h => (h hs).elim⟩
    · obtain ⟨t, i, hi⟩ := next_response M r g hg s.1 s.2 hs
      exact ⟨t, fun _ => ⟨i, hi⟩⟩
  choose next hnext using hchoice
  let st : ℕ → Fin M.condition.states × S.val.Vertex :=
    fun n => Nat.recOn n (M.condition.initial, (decode S).initial) (fun _ t => next t)
  have hs0 : st 0 = (M.condition.initial, (decode S).initial) := rfl
  have hstep : ∀ n, Rank S (st n).2 ≠ 0 →
      ∃ i : Fin (Rank S (st n).2), S.val.graph.edge (st n).2 i.val (.inl (st (n+1)).2) ∧
        (st (n+1)).1 = M.condition.step (st n).1 (.inl (r.edgeType (st n).2 i)) ∧
        g (selection (st n).2 (marking M r (st n).1 (st n).2)) =
          position (st (n+1)).1 (st (n+1)).2 := fun n => hnext (st n)
  have hstart : (st 0).2 ∈ S.val.graph.initial := by
    change (decode S).initial ∈ S.val.graph.initial
    rw [Classical.choose_spec S.property.1]
    rfl
  have hnonleaf : ∀ n, Rank S (st n).2 ≠ 0 := by
    by_contra h
    push Not at h
    let N := Nat.find h
    have hend : Rank S (st N).2 = 0 := Nat.find_spec h
    have hbefore : ∀ n < N, Rank S (st n).2 ≠ 0 := fun n hn => Nat.find_min h hn
    choose dir hdir using fun i : Fin N => hstep i.val (hbefore i.val i.isLt)
    let b : FiniteBranch S N :=
      ⟨fun i => (st i.val).2, dir, hstart, fun i => (hdir i).1, hend⟩
    have hfold := fold_prefix (fun q a => M.condition.step q (.inl a))
      (fun n => (st n).1) N (fun i => r.edgeType (st i.val).2 (dir i))
      (fun i => (hdir i).2.1)
    have hfinal := hr.1 N b
    change M.condition.step
      ((List.ofFn (fun i => r.edgeType (st i.val).2 (dir i))).foldl
        (fun q a => M.condition.step q (.inl a)) (st 0).1)
      (.inr (r.leafType (st N).2 hend)) ∈ M.condition.final at hfinal
    rw [hfold] at hfinal
    have hlose : ∀ k, k ≤ N → (game M (decode S)).WinsFrom false g
        (position (st k).1 (st k).2) := by
      intro k hk
      induction k with
      | zero => exact hgv
      | succ k ih =>
        have hmark := ModalTransitions.run_marking M r (st k).1 (st k).2
          (fun hz => (hbefore k (by omega) hz).elim)
        have hsel := ParityWinningRegions.move (game M (decode S)) false g
          (position (st k).1 (st k).2)
          (selection (st k).2 (marking M r (st k).1 (st k).2)) (ih (by omega))
          ⟨rfl, hmark⟩ (fun he => (Bool.false_ne_true (he.mp trivial)).elim)
        have hi := hdir ⟨k, by omega⟩
        exact ParityWinningRegions.move (game M (decode S)) false g _ _ hsel
          ⟨⟨(dir ⟨k, by omega⟩).val, hi.1⟩, dir ⟨k, by omega⟩, hi.1, hi.2.1.symm⟩
          (fun _ => hi.2.2.symm)
    have hyes : Winning (game M (decode S)) true (position (st N).1 (st N).2) := by
      apply (ModalAcceptanceGame.winning_equation M (decode S) _ _).mpr
      apply Or.inl
      refine ⟨⟨r.leafType (st N).2 hend, ?_, hfinal⟩, ?_⟩
      · simpa only [decode, valuation_cast] using r.leaves (st N).2 hend
      · rintro w ⟨d, hd⟩
        have hlt := S.val.graph.direction_valid _ _ _ hd
        change d < Rank S (st N).2 at hlt
        omega
    exact ParityWinningRegions.disjoint _ _ ⟨hyes, g, hg, hlose N le_rfl⟩
  choose dir hdir using fun n => hstep n (hnonleaf n)
  let b : InfiniteBranch S :=
    ⟨fun n => (st n).2, dir, hstart, fun n => (hdir n).1⟩
  let w : ℕ → Fin M.unary := fun n => r.edgeType (st n).2 (dir n)
  have hrun : ∀ n, M.condition.run w n = (st n).1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (congrArg (fun q => M.condition.step q (.inl (w n))) ih).trans
        (hdir n).2.1.symm
  let p : ℕ → Vertex M (decode S) := fun n => if n % 2 = 0 then
    position (st (n/2)).1 (st (n/2)).2 else
    selection (st (n/2)).2 (marking M r (st (n/2)).1 (st (n/2)).2)
  have pe : ∀ n, p (2*n) = position (st n).1 (st n).2 := by intro n; simp [p]
  have po : ∀ n, p (2*n+1) = selection (st n).2 (marking M r (st n).1 (st n).2) := by
    intro n; simp [p, Nat.add_div]
  have hp : (game M (decode S)).IsPlay p := by
    intro n
    have hmod := Nat.mod_lt n (by omega : 0 < 2)
    have hdiv := Nat.mod_add_div n 2
    by_cases hn : n % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k := ⟨n/2, by omega⟩
      rw [pe, po]
      exact ⟨rfl, ModalTransitions.run_marking M r _ _ (fun hz => (hnonleaf _ hz).elim)⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k+1 := ⟨n/2, by omega⟩
      have heq : 2*k+1+1 = 2*(k+1) := by omega
      rw [po, heq, pe]
      exact ⟨⟨(dir k).val, (hdir k).1⟩, dir k, (hdir k).1, (hdir k).2.1.symm⟩
  have hc : (game M (decode S)).Consistent false g p := by
    intro n hn
    have hmod := Nat.mod_lt n (by omega : 0 < 2)
    have hdiv := Nat.mod_add_div n 2
    by_cases hn0 : n % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k := ⟨n/2, by omega⟩
      rw [pe] at hn
      exact (Bool.false_ne_true (hn.mp trivial)).elim
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k+1 := ⟨n/2, by omega⟩
      have heq : 2*k+1+1 = 2*(k+1) := by omega
      rw [po, heq, pe]
      exact (hdir k).2.2.symm
  have hpar : (game M (decode S)).EveWins p :=
    interleave_parity M (decode S) w p
      (fun n => by rw [pe, hrun]; rfl)
      (fun n => by rw [po]; rfl) (hr.2 b)
  exact Bool.false_ne_true ((hgv p hp (pe 0) hc).mp hpar)

end Lax369799Proofs.AutomatonRunGame
