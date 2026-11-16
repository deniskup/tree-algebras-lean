/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Emptiness.Zielonka.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Mathlib.Data.Set.Card
import Lax369799Proofs.ParityAttractors

/-!
# Positional determinacy of parity games on finite arenas

This file proves the theorem of Emerson–Jurdziński and Mostowski (in the form of Zielonka's
induction): in a parity game on a finite arena, every vertex is won by one of the two
players *with a positional strategy*, and moreover a single positional strategy works
uniformly on the whole winning region.

The statement is relativized to a subgame `S` (a set of vertices in which every vertex has a
successor), which is what the induction requires: the two subgames used in the induction
step are the complement of Eve's attractor to the vertices of maximal priority, and the
complement of Adam's attractor to his winning region in that subgame.

The main results are

* `Lax369799Proofs.WordAutomata.FinGame.Arena.determined`: every subgame is positionally determined;
* `Lax369799Proofs.WordAutomata.FinGame.Arena.exists_winsE_of_not_winsA`: if Adam has no positional winning
  strategy from `v`, then Eve has one.
-/

namespace Lax369799Proofs.WordAutomata

namespace FinGame

namespace Arena

variable {V : Type} [Fintype V]

/-- The subgame `S` of `a` is positionally determined: there are positional strategies of
the two players such that every vertex of `S` is won by one of them. -/
def Determined (a : Arena V) (S : Set V) : Prop :=
  ∃ f g, a.EveOK S f ∧ a.AdamOK S g ∧ ∀ v ∈ S, a.WinsE S f v ∨ a.WinsA S g v

omit [Fintype V] in
/-- A positional strategy that is legal everywhere in `S`, for both players. -/
theorem exists_default {a : Arena V} {S : Set V} (hS : a.Closed S) :
    ∃ d : V → V, ∀ v, v ∈ S → d v ∈ S ∧ a.E v (d v) := by
  classical
  have h : ∀ v : V, ∃ w, v ∈ S → w ∈ S ∧ a.E v w := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨w, hw1, hw2⟩ := hS v hv
      exact ⟨w, fun _ => ⟨hw1, hw2⟩⟩
    · exact ⟨v, fun hc => absurd hc hv⟩
  choose d hd using h
  exact ⟨d, hd⟩

/-- The induction step of Zielonka's proof, in the case where the maximal priority of the
subgame is even. -/
theorem determined_even (a : Arena V) (S : Set V) (hS : a.Closed S) (p : ℕ)
    (hple : ∀ v ∈ S, a.prio v ≤ p) (hpe : Even p) (hpex : ∃ v ∈ S, a.prio v = p)
    (IH : ∀ (b : Arena V) (T : Set V), b.Closed T → T.ncard < S.ncard → Determined b T) :
    Determined a S := by
  classical
  obtain ⟨d, hd⟩ := exists_default hS
  -- the vertices of maximal priority, and Eve's attractor to them
  set T : Set V := {v | v ∈ S ∧ a.prio v = p} with hT
  set X : Set V := a.attr S T with hX
  obtain ⟨fA, hfAok, hfAdec⟩ := exists_attrStrat (a := a) (S := S) (T := T) hS
  set S' : Set V := S \ X with hS'
  have hS'closed : a.Closed S' := closed_diff_attr hS
  have hS'card : S'.ncard < S.ncard := by
    obtain ⟨v0, hv0S, hv0p⟩ := hpex
    have hv0T : v0 ∈ T := ⟨hv0S, hv0p⟩
    have hv0X : v0 ∈ X := target_subset_attr ⟨hv0T, hv0S⟩
    refine Set.ncard_lt_ncard ⟨Set.diff_subset, ?_⟩ (Set.toFinite S)
    intro hsub
    exact (hsub hv0S).2 hv0X
  obtain ⟨f', g', hf'ok, hg'ok, hdisj'⟩ := IH a S' hS'closed hS'card
  -- Adam's winning region in the subgame `S'`
  set WA : Set V := {v | v ∈ S' ∧ a.WinsA S' g' v} with hWA
  by_cases hWAempty : ∀ v ∈ S', ¬ a.WinsA S' g' v
  · -- Eve wins everywhere in `S'`, hence everywhere in `S`
    have hEve' : ∀ v ∈ S', a.WinsE S' f' v := by
      intro v hv
      rcases hdisj' v hv with h | h
      · exact h
      · exact absurd h (hWAempty v hv)
    refine ⟨fun v => if v ∈ X then fA v else f' v, d, ?_, ?_, ?_⟩
    · intro v hvS hown
      by_cases hvX : v ∈ X
      · simpa [hvX] using hfAok v hvS hown
      · have := hf'ok v ⟨hvS, hvX⟩ hown
        simp only [hvX, if_false]
        exact ⟨this.1.1, this.2⟩
    · intro v hvS _
      exact hd v hvS
    · intro v hvS
      left
      intro π hπ hπ0 hcons
      by_cases hcase : ∃ N, ∀ n, N ≤ n → π n ∉ X
      · -- the play eventually stays in `S'`
        obtain ⟨N, hN⟩ := hcase
        have hpath' : a.PathIn S' (shift π N) := by
          refine ⟨(a.pathIn_shift hπ N).1, fun n => ⟨hπ.2 _, hN (n + N) (by omega)⟩⟩
        have hcons' : a.ConsE f' (shift π N) := by
          intro n hn
          have h1 : π (n + N) ∉ X := hN (n + N) (by omega)
          have := hcons (n + N) hn
          show π (n + 1 + N) = f' (π (n + N))
          have hcomm : n + 1 + N = n + N + 1 := by omega
          rw [hcomm, this]
          simp [h1]
        have hstart : shift π N 0 ∈ S' := hpath'.2 0
        have := hEve' _ hstart (shift π N) hpath' rfl hcons'
        exact (a.eveWinsPlay_shift N).1 this
      · -- the play visits `X` infinitely often, hence visits `T` infinitely often
        push_neg at hcase
        have hinf : InfOften (a.prioSeq π) p := by
          intro N
          obtain ⟨n, hn, hnX⟩ := hcase N
          have hcons' : ∀ k, shift π n k ∈ a.attr S T → shift π n k ∉ T →
              a.own (shift π n k) → shift π n (k + 1) = fA (shift π n k) := by
            intro k hk1 _ hk3
            have hmem : π (k + n) ∈ X := hk1
            have := hcons (k + n) hk3
            show π (k + 1 + n) = fA (π (k + n))
            have hcomm : k + 1 + n = k + n + 1 := by omega
            rw [hcomm, this]
            simp [hmem]
          obtain ⟨m, hm⟩ := reach_target (a := a) (S := S) (T := T) hfAdec
            (a.pathIn_shift hπ n) (by simpa [shift] using hnX) hcons'
          exact ⟨m + n, by omega, hm.2⟩
        exact ⟨p, maxInfOften_of_le (fun n => hple _ (hπ.2 n)) hinf, hpe⟩
  · -- Adam wins somewhere in `S'`
    push_neg at hWAempty
    obtain ⟨v0, hv0S', hv0win⟩ := hWAempty
    have hv0WA : v0 ∈ WA := ⟨hv0S', hv0win⟩
    -- Adam's attractor to his winning region
    set B : Set V := a.dual.attr S WA with hB
    obtain ⟨gA, hgAok, hgAdec⟩ := exists_attrStrat (a := a.dual) (S := S) (T := WA) hS
    have hWAsubB : WA ⊆ B := by
      intro v hv
      exact target_subset_attr ⟨hv, hv.1.1⟩
    have hBsubS : B ⊆ S := attr_subset
    set gB : V → V := fun v => if v ∈ WA then g' v else gA v with hgB
    -- Adam wins from his winning region in `S'`, even inside the bigger game `S`
    have claim1 : ∀ v ∈ WA, ∀ π, a.PathIn S π → π 0 = v →
        (∀ n, π n ∈ WA → ¬ a.own (π n) → π (n + 1) = g' (π n)) → ¬ a.EveWinsPlay π := by
      intro v hv π hπ hπ0 hcons
      have hstay : ∀ n, π n ∈ WA := by
        intro n
        induction n with
        | zero => rw [hπ0]; exact hv
        | succ k ih =>
            have hkS' : π k ∈ S' := ih.1
            have hkwin : a.WinsA S' g' (π k) := ih.2
            by_cases hown : a.own (π k)
            · have hnotX : π (k + 1) ∉ X :=
                eve_no_escape hkS'.1 hkS'.2 hown (hπ.2 (k + 1)) (hπ.1 k)
              have hmem : π (k + 1) ∈ S' := ⟨hπ.2 (k + 1), hnotX⟩
              exact ⟨hmem, a.winsA_step hkwin hkS' (hπ.1 k) (fun hc => absurd hown hc)⟩
            · have heq : π (k + 1) = g' (π k) := hcons k ih hown
              have hmem : π (k + 1) ∈ S' := by
                rw [heq]
                exact (hg'ok _ hkS' hown).1
              exact ⟨hmem, a.winsA_step hkwin hkS' (hπ.1 k) (fun _ => heq)⟩
      have hpath' : a.PathIn S' π := ⟨hπ.1, fun n => (hstay n).1⟩
      have hcons' : a.ConsA g' π := fun n hn => hcons n (hstay n) hn
      have := hv.2
      rw [← hπ0] at this
      exact this π hpath' rfl hcons'
    -- Adam wins from his attractor
    have claim2 : ∀ v ∈ B, ∀ π, a.PathIn S π → π 0 = v →
        (∀ n, π n ∈ B → ¬ a.own (π n) → π (n + 1) = gB (π n)) → ¬ a.EveWinsPlay π := by
      intro v hv π hπ hπ0 hcons
      have hconsA : ∀ k, π k ∈ a.dual.attr S WA → π k ∉ WA → a.dual.own (π k) →
          π (k + 1) = gA (π k) := by
        intro k hk1 hk2 hk3
        have := hcons k hk1 hk3
        rw [this, hgB]
        simp [hk2]
      obtain ⟨m, hm⟩ := reach_target (a := a.dual) (S := S) (T := WA) hgAdec
        (by exact hπ) (by rw [hπ0]; exact hv) hconsA
      have hcons2 : ∀ n, shift π m n ∈ WA → ¬ a.own (shift π m n) →
          shift π m (n + 1) = g' (shift π m n) := by
        intro n hn1 hn2
        have hnB : π (n + m) ∈ B := hWAsubB hn1
        have := hcons (n + m) hnB hn2
        show π (n + 1 + m) = g' (π (n + m))
        have hcomm : n + 1 + m = n + m + 1 := by omega
        rw [hcomm, this, hgB]
        simp [show π (n + m) ∈ WA from hn1]
      have := claim1 (π m) hm (shift π m) (a.pathIn_shift hπ m) (by simp) hcons2
      intro hwin
      exact this ((a.eveWinsPlay_shift m).2 hwin)
    -- the rest of the game
    set S'' : Set V := S \ B with hS''
    have hS''closed : a.Closed S'' := closed_diff_attr (a := a.dual) hS
    have hS''card : S''.ncard < S.ncard := by
      refine Set.ncard_lt_ncard ⟨Set.diff_subset, ?_⟩ (Set.toFinite S)
      intro hsub
      exact (hsub (hBsubS (hWAsubB hv0WA))).2 (hWAsubB hv0WA)
    obtain ⟨f'', g'', hf''ok, hg''ok, hdisj''⟩ := IH a S'' hS''closed hS''card
    refine ⟨fun v => if v ∈ S'' then f'' v else d v, fun v => if v ∈ B then gB v else g'' v,
      ?_, ?_, ?_⟩
    · intro v hvS hown
      by_cases hv : v ∈ S''
      · have := hf''ok v hv hown
        simp only [hv, if_true]
        exact ⟨this.1.1, this.2⟩
      · simpa [hv] using hd v hvS
    · intro v hvS hown
      by_cases hv : v ∈ B
      · simp only [hv, if_true, hgB]
        by_cases hw : v ∈ WA
        · simp only [hw, if_true]
          have := hg'ok v hw.1 hown
          exact ⟨this.1.1, this.2⟩
        · simp only [hw, if_false]
          exact hgAok v hvS hown
      · simp only [hv, if_false]
        have := hg''ok v ⟨hvS, hv⟩ hown
        exact ⟨this.1.1, this.2⟩
    · intro v hvS
      -- Adam wins from `B`
      have hBwin : ∀ w ∈ B, a.WinsA S (fun u => if u ∈ B then gB u else g'' u) w := by
        intro w hw π hπ hπ0 hcons
        refine claim2 w hw π hπ hπ0 ?_
        intro n hn1 hn2
        have := hcons n hn2
        rw [this]
        simp [hn1]
      by_cases hvB : v ∈ B
      · exact Or.inr (hBwin v hvB)
      · have hvS'' : v ∈ S'' := ⟨hvS, hvB⟩
        rcases hdisj'' v hvS'' with h | h
        · -- Eve wins and the play cannot leave `S''`
          left
          intro π hπ hπ0 hcons
          have hstay : ∀ n, π n ∈ S'' := by
            intro n
            induction n with
            | zero => rw [hπ0]; exact hvS''
            | succ k ih =>
                by_cases hown : a.own (π k)
                · have heq : π (k + 1) = f'' (π k) := by
                    have := hcons k hown
                    rw [this]
                    simp [ih]
                  rw [heq]
                  exact (hf''ok _ ih hown).1
                · refine ⟨hπ.2 (k + 1), ?_⟩
                  exact eve_no_escape (a := a.dual) ih.1 ih.2 (by simpa using hown)
                    (hπ.2 (k + 1)) (hπ.1 k)
          have hpath'' : a.PathIn S'' π := ⟨hπ.1, hstay⟩
          have hcons'' : a.ConsE f'' π := by
            intro n hn
            have := hcons n hn
            rw [this]
            simp [hstay n]
          exact h π hpath'' hπ0 hcons''
        · -- Adam wins; either the play stays in `S''`, or it enters `B`
          right
          intro π hπ hπ0 hcons
          by_cases hcase : ∃ m, π m ∈ B
          · obtain ⟨m, hm⟩ := hcase
            have := hBwin (π m) hm (shift π m) (a.pathIn_shift hπ m) (by simp)
              (a.consA_shift hcons m)
            intro hwin
            exact this ((a.eveWinsPlay_shift m).2 hwin)
          · push_neg at hcase
            have hstay : ∀ n, π n ∈ S'' := fun n => ⟨hπ.2 n, hcase n⟩
            have hpath'' : a.PathIn S'' π := ⟨hπ.1, hstay⟩
            have hcons'' : a.ConsA g'' π := by
              intro n hn
              have := hcons n hn
              rw [this]
              simp [hcase n]
            exact h π hpath'' hπ0 hcons''

/-- **Positional determinacy of parity games**: every subgame of a finite parity arena is
positionally determined. -/
theorem determined (a : Arena V) (S : Set V) (hS : a.Closed S) : Determined a S := by
  classical
  suffices H : ∀ n : ℕ, ∀ (b : Arena V) (T : Set V), T.ncard ≤ n → b.Closed T →
      Determined b T from H S.ncard a S le_rfl hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b T hcard hT
    have IH : ∀ (c : Arena V) (U : Set V), c.Closed U → U.ncard < T.ncard → Determined c U := by
      intro c U hU hlt
      exact ih U.ncard (lt_of_lt_of_le hlt hcard) c U le_rfl hU
    rcases Set.eq_empty_or_nonempty T with rfl | hne
    · exact ⟨id, id, by simp [EveOK], by simp [AdamOK], by simp⟩
    -- the maximal priority of the subgame
    set Tf : Finset V := (Set.toFinite T).toFinset with hTf
    have hTfne : Tf.Nonempty := by
      obtain ⟨v, hv⟩ := hne
      exact ⟨v, by simpa [hTf] using hv⟩
    set p : ℕ := Tf.sup b.prio with hp
    have hple : ∀ v ∈ T, b.prio v ≤ p := by
      intro v hv
      exact Finset.le_sup (f := b.prio) (by simpa [hTf] using hv)
    obtain ⟨v1, hv1, hv1p⟩ := Finset.exists_mem_eq_sup Tf hTfne b.prio
    have hpex : ∃ v ∈ T, b.prio v = p := ⟨v1, by simpa [hTf] using hv1, hv1p.symm⟩
    by_cases hpe : Even p
    · exact determined_even b T hT p hple hpe hpex IH
    · -- apply the even case to the dual arena
      have hdual : Determined b.dual T := by
        refine determined_even b.dual T hT (p + 1) (fun v hv => by
          simpa using Nat.succ_le_succ (hple v hv)) (by simpa [Nat.even_add_one] using hpe)
          ?_ IH
        obtain ⟨v, hv, hvp⟩ := hpex
        exact ⟨v, hv, by simp [hvp]⟩
      obtain ⟨f, g, hfok, hgok, hdisj⟩ := hdual
      refine ⟨g, f, (b.dual_adamOK T g).1 hgok, (b.dual_eveOK T f).1 hfok, ?_⟩
      intro v hv
      rcases hdisj v hv with h | h
      · exact Or.inr ((b.dual_winsE T f v).1 h)
      · exact Or.inl ((b.dual_winsA T g v).1 h)

/-- If Adam has no positional winning strategy from `v`, then Eve has one. -/
theorem exists_winsE_of_not_winsA (a : Arena V) (S : Set V) (hS : a.Closed S) {v : V}
    (hvS : v ∈ S) (hA : ∀ g, a.AdamOK S g → ¬ a.WinsA S g v) :
    ∃ f, a.EveOK S f ∧ a.WinsE S f v := by
  obtain ⟨f, g, hfok, hgok, hdisj⟩ := determined a S hS
  rcases hdisj v hvS with h | h
  · exact ⟨f, hfok, h⟩
  · exact absurd h (hA g hgok)

end Arena

end FinGame

end Lax369799Proofs.WordAutomata
