/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Safra.Complete.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Lax369799Proofs.SafraRuns
import Mathlib.Data.Finset.Max

/-!
# Safra's construction: completeness

This file proves the second half of the correctness of Safra's construction: if the Büchi
automaton accepts the ω-word `w`, then along the run of the construction on `w` some node is
present from some time on and is marked infinitely often
(`Lax369799Proofs.WordAutomata.Safra.exists_node_of_accepts`).

One follows an accepting run `ρ` of the Büchi automaton through the trees: at every time one
considers the deepest node whose label contains the current state of `ρ`.  From one step to
the next, this node either goes deeper, or moves to a sibling with a *smaller* slot (of
itself or of one of its ancestors), or moves up to a *marked* ancestor
(`Lax369799Proofs.WordAutomata.Safra.step_move`).  Moreover, whenever `ρ` visits the Büchi set, the node goes
strictly below any of its present ancestors, unless that ancestor is marked
(`Lax369799Proofs.WordAutomata.Safra.step_descend`).  Taking for `c` the longest position which is an ancestor
of the tracked node from some time on, these two facts force `c` to be marked infinitely
often.
-/

namespace Lax369799Proofs.WordAutomata

namespace Safra

open scoped Classical

variable {Q Gam : Type} [Fintype Q] {B : NBuchi Q Gam} {w : ℕ → Gam}

/-! ### Elementary facts about suffixes of lists -/

theorem prefix_tri {α : Type} : ∀ (x y : List α),
    x <+: y ∨ y <+: x ∨ ∃ (c : List α) (i j : α), i ≠ j ∧ (c ++ [i]) <+: x ∧ (c ++ [j]) <+: y := by
  intro x
  induction x with
  | nil => intro y; exact Or.inl List.nil_prefix
  | cons i x' ih =>
    intro y
    match y with
    | [] => exact Or.inr (Or.inl List.nil_prefix)
    | j :: y' =>
      by_cases hij : i = j
      · subst hij
        rcases ih y' with h | h | ⟨c, k, l, hkl, h1, h2⟩
        · exact Or.inl (List.cons_prefix_cons.2 ⟨rfl, h⟩)
        · exact Or.inr (Or.inl (List.cons_prefix_cons.2 ⟨rfl, h⟩))
        · refine Or.inr (Or.inr ⟨i :: c, k, l, hkl, ?_, ?_⟩)
          · show (i :: (c ++ [k])) <+: i :: x'
            exact List.cons_prefix_cons.2 ⟨rfl, h1⟩
          · show (i :: (c ++ [l])) <+: i :: y'
            exact List.cons_prefix_cons.2 ⟨rfl, h2⟩
      · exact Or.inr (Or.inr ⟨[], i, j, hij, by simp, by simp⟩)

/-- Two lists are comparable for the suffix order, or they diverge at some point. -/
theorem suffix_tri {α : Type} (x y : List α) :
    x <:+ y ∨ y <:+ x ∨ ∃ (c : List α) (i j : α), i ≠ j ∧ (i :: c) <:+ x ∧ (j :: c) <:+ y := by
  rcases prefix_tri x.reverse y.reverse with h | h | ⟨c, i, j, hij, h1, h2⟩
  · exact Or.inl (List.reverse_prefix.1 h)
  · exact Or.inr (Or.inl (List.reverse_prefix.1 h))
  · refine Or.inr (Or.inr ⟨c.reverse, i, j, hij, ?_, ?_⟩)
    · exact List.reverse_prefix.1 (by simpa using h1)
    · exact List.reverse_prefix.1 (by simpa using h2)

theorem suffix_comparable {α : Type} {x y z : List α} (h1 : x <:+ z) (h2 : y <:+ z) :
    x <:+ y ∨ y <:+ x := by
  rcases le_total x.length y.length with h | h
  · exact Or.inl (List.suffix_of_suffix_length_le h1 h2 h)
  · exact Or.inr (List.suffix_of_suffix_length_le h2 h1 h)

/-- Two children of a same node which are suffixes of a same list are equal. -/
theorem head_eq_of_cons_suffix {α : Type} {i j : α} {c z : List α} (h1 : (i :: c) <:+ z)
    (h2 : (j :: c) <:+ z) : i = j := by
  have := List.suffix_of_suffix_length_le h1 h2 (le_refl _)
  have := this.eq_of_length (by simp)
  simpa using this

/-- A strict suffix is a suffix of a child. -/
theorem exists_cons_suffix {α : Type} {s t : List α} (h : s <:+ t) (hne : s ≠ t) :
    ∃ i, (i :: s) <:+ t := by
  obtain ⟨l, rfl⟩ := h
  rcases l.eq_nil_or_concat with rfl | ⟨l', i, rfl⟩
  · exact absurd (by simp) hne
  · exact ⟨i, ⟨l', by simp⟩⟩

/-! ### Maximal and minimal positions -/

theorem exists_max_length {P : Pos Q → Prop} {N : ℕ} (hne : ∃ v, P v)
    (hbd : ∀ v, P v → v.length ≤ N) : ∃ v, P v ∧ ∀ u, P u → u.length ≤ v.length := by
  classical
  obtain ⟨v0, hv0⟩ := hne
  obtain ⟨v, hv, hlen⟩ :=
    Nat.findGreatest_spec (P := fun n => ∃ v : Pos Q, P v ∧ v.length = n) (hbd v0 hv0)
      ⟨v0, hv0, rfl⟩
  refine ⟨v, hv, fun u hu => ?_⟩
  have := Nat.le_findGreatest (P := fun n => ∃ v : Pos Q, P v ∧ v.length = n) (hbd u hu)
    ⟨u, hu, rfl⟩
  omega

theorem exists_min_length {P : Pos Q → Prop} (hne : ∃ v, P v) :
    ∃ v, P v ∧ ∀ u, P u → v.length ≤ u.length := by
  classical
  obtain ⟨v0, hv0⟩ := hne
  have hex : ∃ n, ∃ v : Pos Q, P v ∧ v.length = n := ⟨v0.length, v0, hv0, rfl⟩
  obtain ⟨v, hv, hlen⟩ := Nat.find_spec hex
  refine ⟨v, hv, fun u hu => ?_⟩
  have : Nat.find hex ≤ u.length := Nat.find_le ⟨u, hu, rfl⟩
  omega

/-! ### The chain of nodes containing a state, before the deletions -/

variable {T : STree Q} {a : Gam}

theorem lab2_length_le (hT : Inv T) {v : Pos Q} {q : Q} (h : q ∈ lab2 B T a v) :
    v.length ≤ Fintype.card Q := by
  match v with
  | [] => simp
  | i :: p =>
      have h1 : q ∈ lab1 B T a (i :: p) := lab2_subset_lab1 B T a _ h
      have h2 : T.lab p ≠ ∅ := by
        rw [lab1_cons] at h1
        split at h1
        · obtain ⟨q0, hq0, -⟩ := h1
          exact fun hc => by rw [hc] at hq0; exact hq0.1
        · obtain ⟨q0, hq0, -⟩ := h1
          exact fun hc => by
            have := hT.mono i p hq0
            rw [hc] at this
            exact this
      have := hT.length_lt h2
      simp only [List.length_cons]
      omega

theorem lab2_suffix_of_length_le {q : Q} :
    ∀ (r p : Pos Q), p.length ≤ r.length → q ∈ lab2 B T a p → q ∈ lab2 B T a r → p <:+ r := by
  intro r
  induction r with
  | nil =>
      intro p hlen _ _
      simp only [List.length_nil, Nat.le_zero, List.length_eq_zero_iff] at hlen
      subst hlen
      exact List.nil_suffix
  | cons i r ih =>
      intro p hlen hp hr
      rcases Nat.lt_or_ge r.length p.length with hlt | hge
      · have hplen : p.length = r.length + 1 := by simp only [List.length_cons] at hlen; omega
        match p, hplen with
        | j :: p', hplen =>
          have hp'len : p'.length = r.length := by simpa using hplen
          have hp' : q ∈ lab2 B T a p' := lab2_cons_subset B T a j p' hp
          have hr' : q ∈ lab2 B T a r := lab2_cons_subset B T a i r hr
          have hsuf : p' <:+ r := ih p' (le_of_eq hp'len) hp' hr'
          have : p' = r := hsuf.eq_of_length (by omega)
          subst this
          by_cases hij : j = i
          · subst hij; exact List.suffix_rfl
          · exfalso
            have hd := lab2_disjoint B T a (i := j) (j := i) p' hij
            have : q ∈ lab2 B T a (j :: p') ∩ lab2 B T a (i :: p') := ⟨hp, hr⟩
            rw [hd] at this
            exact this
      · exact (ih p hge hp (lab2_cons_subset B T a i r hr)).trans (List.suffix_cons i r)

theorem lab2_comparable {q : Q} {p r : Pos Q} (hp : q ∈ lab2 B T a p)
    (hr : q ∈ lab2 B T a r) : p <:+ r ∨ r <:+ p := by
  rcases le_total p.length r.length with h | h
  · exact Or.inl (lab2_suffix_of_length_le r p h hp hr)
  · exact Or.inr (lab2_suffix_of_length_le p r h hr hp)

/-- A state which is in the new label of a node and in the new label of one of its children
before the merge is in the new label of the child with the smallest slot containing it. -/
theorem exists_min_child {q : Q} {c : Pos Q} (hq2 : q ∈ lab2 B T a c)
    (h : ∃ i, q ∈ lab1 B T a (i :: c)) : ∃ i, q ∈ lab2 B T a (i :: c) := by
  classical
  obtain ⟨i0, hi0⟩ := h
  set S : Finset (Slot Q) := Finset.univ.filter (fun i => q ∈ lab1 B T a (i :: c)) with hS
  have hSne : S.Nonempty := ⟨i0, by simp [hS, hi0]⟩
  refine ⟨S.min' hSne, ?_, ?_⟩
  · exact ⟨(by simpa [hS] using S.min'_mem hSne : q ∈ lab1 B T a (S.min' hSne :: c)), hq2⟩
  · intro hmem
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨j, hlt, hmem'⟩ := hmem
    have hjS : j ∈ S := by simp [hS, hmem']
    exact absurd hlt (not_lt.2 (S.min'_le j hjS))

/-- The deepest node whose (pre-deletion) label contains a given state. -/
theorem exists_deepest_lab2 (hT : Inv T) {q : Q} (h0 : q ∈ lab2 B T a []) :
    ∃ v, q ∈ lab2 B T a v ∧ (∀ u, q ∈ lab2 B T a u → u <:+ v) ∧
      ∀ i, q ∉ lab1 B T a (i :: v) := by
  obtain ⟨v, hv, hmax⟩ :=
    exists_max_length (P := fun v => q ∈ lab2 B T a v) (N := Fintype.card Q) ⟨[], h0⟩
      (fun v hv => lab2_length_le hT hv)
  refine ⟨v, hv, fun u hu => lab2_suffix_of_length_le v u (hmax u hu) hu hv, ?_⟩
  intro i hi
  obtain ⟨j, hj⟩ := exists_min_child hv ⟨i, hi⟩
  have := hmax (j :: v) hj
  simp only [List.length_cons] at this
  omega

/-- After the deletions, the deepest node containing a state is the deepest non-deleted
ancestor of the deepest node before the deletions; if it is not that node, it is marked. -/
theorem exists_new_node {q : Q} {v : Pos Q} (hv : q ∈ lab2 B T a v) :
    ∃ z, z <:+ v ∧ q ∈ (stepTree B T a).lab z ∧ (z ≠ v → (stepTree B T a).mark z) := by
  by_cases hk : killed B T a v
  · obtain ⟨z, ⟨hzsuf, hzne, hzm⟩, hmin⟩ :=
      exists_min_length (P := fun z => z <:+ v ∧ z ≠ v ∧ vmark B T a z) hk
    have hnk : ¬ killed B T a z := by
      rintro ⟨c, hc, hcne, hcm⟩
      have hcv : c <:+ v := hc.trans hzsuf
      have hclt : c.length < z.length := by
        have h1 : c.length ≤ z.length := hc.length_le
        rcases eq_or_lt_of_le h1 with heq | hlt
        · exact absurd (hc.eq_of_length heq) hcne
        · exact hlt
      have hcnev : c ≠ v := by
        intro hcv'
        subst hcv'
        have := hzsuf.length_le
        omega
      have := hmin c ⟨hcv, hcnev, hcm⟩
      omega
    refine ⟨z, hzsuf, ?_, fun _ => ⟨hzm, hnk⟩⟩
    rw [stepTree_lab_of_not_killed B T a hnk]
    exact lab2_mono B T a hzsuf hv
  · exact ⟨v, List.suffix_rfl, by rw [stepTree_lab_of_not_killed B T a hk]; exact hv,
      fun h => absurd rfl h⟩

/-! ### How the tracked node moves -/

/-- `MoveLeft u v` says that `v` lies strictly to the left of `u`: at some level, `v` goes
through a sibling with a smaller slot. -/
def MoveLeft (u v : Pos Q) : Prop := ∃ (c : Pos Q) (i j : Slot Q), j < i ∧ (i :: c) <:+ u ∧
  (j :: c) <:+ v

/-- **How the tracked node moves.**  If `u` is the deepest node containing the state `q`,
then the deepest node `v` containing a successor `q'` of `q` in the next tree either lies
below `u`, or lies strictly to the left of `u`, or is a marked strict ancestor of `u`. -/
theorem step_move (hT : Inv T) {q q' : Q} {u : Pos Q} (hu : q ∈ T.lab u)
    (hstep : B.step q a q') :
    ∃ v, q' ∈ (stepTree B T a).lab v ∧ (∀ z, q' ∈ (stepTree B T a).lab z → z <:+ v) ∧
      (u <:+ v ∨ MoveLeft u v ∨ (v <:+ u ∧ v ≠ u ∧ (stepTree B T a).mark v)) := by
  classical
  have hroot : q' ∈ lab2 B T a [] := ⟨q, hT.mono' List.nil_suffix hu, hstep⟩
  obtain ⟨vs, hvs, hvsmax, hvsleaf⟩ := exists_deepest_lab2 hT hroot
  -- the label of an ancestor of `u` contains `q`, hence its successor after the step
  have hanc : ∀ (i : Slot Q) (c : Pos Q), (i :: c) <:+ u → q' ∈ lab1 B T a (i :: c) := by
    intro i c hic
    have hq : q ∈ T.lab (i :: c) := hT.mono' hic hu
    rw [lab1_cons_of_lab_ne B T a (Set.nonempty_iff_ne_empty.1 ⟨q, hq⟩)]
    exact ⟨q, hq, hstep⟩
  -- the position of `vs` relative to `u`
  have hrel : u <:+ vs ∨ MoveLeft u vs := by
    rcases suffix_tri u vs with h | h | ⟨c, i, j, hij, h1, h2⟩
    · exact Or.inl h
    · rcases eq_or_ne vs u with rfl | hne
      · exact Or.inl List.suffix_rfl
      · exfalso
        obtain ⟨i, hi⟩ := exists_cons_suffix h hne
        exact hvsleaf i (hanc i vs hi)
    · refine Or.inr ⟨c, i, j, ?_, h1, h2⟩
      -- the slot `j` chosen in `vs` is smaller than the slot `i` on the way to `u`
      have hj2 : q' ∈ lab2 B T a (j :: c) := lab2_mono B T a h2 hvs
      have hi1 : q' ∈ lab1 B T a (i :: c) := hanc i c h1
      rcases lt_trichotomy j i with h | h | h
      · exact h
      · exact absurd h.symm hij
      · exfalso
        exact hj2.2 (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨h, hi1⟩⟩)
  obtain ⟨v, hvsuf, hvmem, hvmark⟩ := exists_new_node hvs
  refine ⟨v, hvmem, ?_, ?_⟩
  · -- `v` is the deepest node of the new tree containing `q'`
    intro z hz
    have hz2 : q' ∈ lab2 B T a z := stepTree_lab_subset B T a z hz
    have hzs : z <:+ vs := hvsmax z hz2
    rcases eq_or_ne v vs with heq | hne
    · rw [heq]; exact hzs
    · by_contra hcon
      rcases suffix_comparable hvsuf hzs with h | h
      · have hne' : v ≠ z := by rintro rfl; exact hcon List.suffix_rfl
        have hkill : killed B T a z := ⟨v, h, hne', (hvmark hne).1⟩
        rw [stepTree_lab, if_pos hkill] at hz
        exact hz
      · exact hcon h
  · rcases eq_or_ne v vs with heq | hne
    · rw [heq]
      rcases hrel with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hmark := hvmark hne
      rcases hrel with h | ⟨c, i, j, hij, h1, h2⟩
      · -- `u` is an ancestor of `vs`, and so is `v`
        rcases suffix_comparable h hvsuf with h' | h'
        · exact Or.inl h'
        · rcases eq_or_ne v u with rfl | hne'
          · exact Or.inl List.suffix_rfl
          · exact Or.inr (Or.inr ⟨h', hne', hmark⟩)
      · -- `vs` is to the left of `u`; either `v` is still to the left, or it is above
        rcases suffix_comparable h2 hvsuf with h' | h'
        · exact Or.inr (Or.inl ⟨c, i, j, hij, h1, h'⟩)
        · rcases List.suffix_cons_iff.1 h' with heq' | hsub
          · exact Or.inr (Or.inl ⟨c, i, j, hij, h1, by rw [heq']⟩)
          · have hvu : v <:+ u := hsub.trans ((List.suffix_cons i c).trans h1)
            rcases eq_or_ne v u with rfl | hne'
            · exact Or.inl List.suffix_rfl
            · exact Or.inr (Or.inr ⟨hvu, hne', hmark⟩)

/-- **Visiting the Büchi set forces a descent.**  If the state `q` in the label of a present
node `c` is in the Büchi set, then its successor lies in a child of `c` after the step,
unless `c` is marked. -/
theorem step_descend (hT : Inv T) {q q' : Q} {c : Pos Q} (hq : q ∈ T.lab c) (hfin : q ∈ B.fin)
    (hstep : B.step q a q') (hq2 : q' ∈ lab2 B T a c) (hnk : ¬ killed B T a c) :
    (∃ i, q' ∈ (stepTree B T a).lab (i :: c)) ∨ (stepTree B T a).mark c := by
  obtain ⟨s, hs⟩ := hT.freshSlot_isSome c
  have h1 : q' ∈ lab1 B T a (s :: c) := by
    rw [lab1_cons, if_pos hs]
    exact ⟨q, ⟨hq, hfin⟩, hstep⟩
  obtain ⟨i, hi⟩ := exists_min_child hq2 ⟨s, h1⟩
  by_cases hk : killed B T a (i :: c)
  · obtain ⟨d, hd, hdne, hdm⟩ := hk
    have hdc : d <:+ c := (List.suffix_cons_iff.1 hd).resolve_left hdne
    rcases eq_or_ne d c with rfl | hne
    · exact Or.inr ⟨hdm, hnk⟩
    · exact absurd ⟨d, hdc, hne, hdm⟩ hnk
  · exact Or.inl ⟨i, by rw [stepTree_lab, if_neg hk]; exact hi⟩

/-- The deepest node whose label contains a given state. -/
theorem exists_deepest (hT : Inv T) {q : Q} (h0 : q ∈ T.lab []) :
    ∃ v, q ∈ T.lab v ∧ ∀ u, q ∈ T.lab u → u <:+ v := by
  obtain ⟨v, hv, hmax⟩ := exists_max_length (P := fun v => q ∈ T.lab v) (N := Fintype.card Q)
    ⟨[], h0⟩ (fun v hv => le_of_lt (hT.length_lt (Set.nonempty_iff_ne_empty.1 ⟨q, hv⟩)))
  exact ⟨v, hv, fun u hu => hT.suffix_of_mem_of_length_le v u (hmax u hu) hu hv⟩

/-! ### Completeness -/

/-- **Completeness of Safra's construction.**  If the Büchi automaton accepts the word, then
some node is present from some time on and is marked infinitely often. -/
theorem exists_node_of_accepts (hacc : B.Accepts w) :
    ∃ (p : Pos Q) (N : ℕ), (∀ n, N ≤ n → (treeRun B w n).lab p ≠ ∅) ∧
      {n | (treeRun B w n).mark p}.Infinite := by
  classical
  obtain ⟨rho, hrun, hvis⟩ := hacc
  have hroot : ∀ n, rho n ∈ (treeRun B w n).lab [] := fun n =>
    (mem_root_iff B w n (rho n)).2 ⟨rho, hrun.1, rfl, fun k _ _ => hrun.2 k⟩
  -- the tracked node: the deepest node containing the current state of the run
  have hdex : ∀ n, ∃ v, rho n ∈ (treeRun B w n).lab v ∧
      ∀ u, rho n ∈ (treeRun B w n).lab u → u <:+ v :=
    fun n => exists_deepest (inv_treeRun B w n) (hroot n)
  choose d hd1 hd2 using hdex
  -- how the tracked node moves
  have hmove : ∀ n, d n <:+ d (n + 1) ∨ MoveLeft (d n) (d (n + 1)) ∨
      (d (n + 1) <:+ d n ∧ d (n + 1) ≠ d n ∧ (treeRun B w (n + 1)).mark (d (n + 1))) := by
    intro n
    obtain ⟨v, hv1, hv2, hrel⟩ := step_move (inv_treeRun B w n) (hd1 n) (hrun.2 n)
    have hveq : v = d (n + 1) := by
      have h1 : v <:+ d (n + 1) := hd2 (n + 1) v hv1
      have h2 : d (n + 1) <:+ v := hv2 (d (n + 1)) (hd1 (n + 1))
      exact h1.eq_of_length (le_antisymm h1.length_le h2.length_le)
    rw [hveq] at hrel
    exact hrel
  -- the longest position which is eventually always an ancestor of the tracked node
  have hbd : ∀ c : Pos Q, (∃ N, ∀ n, N ≤ n → c <:+ d n) → c.length ≤ Fintype.card Q := by
    rintro c ⟨N, hN⟩
    have h1 : c <:+ d N := hN N (le_refl N)
    have h2 : (treeRun B w N).lab (d N) ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨_, hd1 N⟩
    have h3 := (inv_treeRun B w N).length_lt h2
    have h4 := h1.length_le
    omega
  obtain ⟨cs, ⟨N0, hN0⟩, hcsmax⟩ :=
    exists_max_length (P := fun c : Pos Q => ∃ N, ∀ n, N ≤ n → c <:+ d n)
      (N := Fintype.card Q) ⟨[], 0, fun n _ => List.nil_suffix⟩ hbd
  have halive : ∀ n, N0 ≤ n → (treeRun B w n).lab cs ≠ ∅ := fun n hn =>
    Set.nonempty_iff_ne_empty.1 ⟨rho n, (inv_treeRun B w n).mono' (hN0 n hn) (hd1 n)⟩
  refine ⟨cs, N0, halive, ?_⟩
  by_contra hfinmark
  rw [Set.not_infinite] at hfinmark
  obtain ⟨N1', hN1'⟩ := hfinmark.bddAbove
  set N1 := max N0 N1' + 1 with hN1def
  have hnomark : ∀ n, N1 ≤ n → ¬ (treeRun B w n).mark cs := by
    intro n hn hm
    have := hN1' (show n ∈ {n | (treeRun B w n).mark cs} from hm)
    have : N1' < N1 := by rw [hN1def]; omega
    omega
  -- after a visit of the Büchi set the tracked node is strictly below `cs`
  have hbelow : ∀ n, N1 ≤ n → rho n ∈ B.fin → ∃ i, (i :: cs) <:+ d (n + 1) := by
    intro n hn hfin
    have hcsn : cs <:+ d n := hN0 n (by rw [hN1def] at hn; omega)
    have hcsn1 : cs <:+ d (n + 1) := hN0 (n + 1) (by rw [hN1def] at hn; omega)
    have hq : rho n ∈ (treeRun B w n).lab cs := (inv_treeRun B w n).mono' hcsn (hd1 n)
    have hnk : ¬ killed B (treeRun B w n) (w n) cs := by
      intro hk
      refine halive (n + 1) (by rw [hN1def] at hn; omega) ?_
      rw [treeRun_succ, stepTree_lab, if_pos hk]
    have hq2 : rho (n + 1) ∈ lab2 B (treeRun B w n) (w n) cs := by
      have h1 : rho (n + 1) ∈ (treeRun B w (n + 1)).lab cs :=
        (inv_treeRun B w (n + 1)).mono' hcsn1 (hd1 (n + 1))
      exact stepTree_lab_subset B (treeRun B w n) (w n) cs h1
    rcases step_descend (inv_treeRun B w n) hq hfin (hrun.2 n) hq2 hnk with ⟨i, hi⟩ | hmk
    · exact ⟨i, hd2 (n + 1) (i :: cs) hi⟩
    · exact absurd hmk (hnomark (n + 1) (by omega))
  -- once strictly below, always strictly below
  have hstay : ∀ n, N1 ≤ n → (∃ i, (i :: cs) <:+ d n) → ∃ i, (i :: cs) <:+ d (n + 1) := by
    rintro n hn ⟨y, hy⟩
    have hcsn1 : cs <:+ d (n + 1) := hN0 (n + 1) (by rw [hN1def] at hn; omega)
    rcases eq_or_ne (d (n + 1)) cs with heq | hne
    · exfalso
      rcases hmove n with hcase | ⟨c, i, j, hij, hi, hj⟩ | ⟨hsuf, hne', hmk⟩
      · have hdn : d n = cs := by
          have h1 : d n <:+ cs := by rw [← heq]; exact hcase
          have h2 : cs <:+ d n := hN0 n (by rw [hN1def] at hn; omega)
          exact h1.eq_of_length (le_antisymm h1.length_le h2.length_le)
        rw [hdn] at hy
        have := hy.length_le
        simp only [List.length_cons] at this
        omega
      · have hcsn : cs <:+ d n := hN0 n (by rw [hN1def] at hn; omega)
        have hjcs : (j :: c) <:+ cs := by rw [← heq]; exact hj
        have hjd : (j :: c) <:+ d n := hjcs.trans hcsn
        exact absurd (head_eq_of_cons_suffix hi hjd) hij.ne'
      · rw [heq] at hmk
        exact hnomark (n + 1) (by omega) hmk
    · exact exists_cons_suffix hcsn1 (Ne.symm hne)
  -- there is a visit of the Büchi set after `N1`
  obtain ⟨n1, hn1, hn1'⟩ : ∃ n, rho n ∈ B.fin ∧ N1 ≤ n := by
    obtain ⟨n, hn, hn'⟩ := (hvis.diff (Set.finite_Iic N1)).nonempty
    simp only [Set.mem_Iic, not_le] at hn'
    exact ⟨n, hn, by omega⟩
  set N2 := n1 + 1 with hN2def
  have hbelow2 : ∀ m, N2 ≤ m → ∃ i, (i :: cs) <:+ d m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbelow n1 hn1' hn1
    | succ m hm ih => exact hstay m (by rw [hN2def] at hm; omega) ih
  -- the slot of the tracked node at the level of `cs` is nonincreasing
  have hxex : ∀ m, ∃ y : Slot Q, N2 ≤ m → (y :: cs) <:+ d m := by
    intro m
    by_cases hm : N2 ≤ m
    · obtain ⟨y, hy⟩ := hbelow2 m hm
      exact ⟨y, fun _ => hy⟩
    · exact ⟨⟨0, by simp [numSlots]⟩, fun hc => absurd hc hm⟩
  choose x hx using hxex
  have hanti : ∀ m, N2 ≤ m → (x (m + 1) : ℕ) ≤ (x m : ℕ) := by
    intro m hm
    have h1 : (x m :: cs) <:+ d m := hx m hm
    have h2 : (x (m + 1) :: cs) <:+ d (m + 1) := hx (m + 1) (by omega)
    have hcsm : cs <:+ d m := hN0 m (by rw [hN2def] at hm; rw [hN1def] at hn1'; omega)
    have hcsm1 : cs <:+ d (m + 1) := hN0 (m + 1) (by
      rw [hN2def] at hm; rw [hN1def] at hn1'; omega)
    rcases hmove m with hcase | ⟨c, i, j, hij, hi, hj⟩ | ⟨hsuf, hne, hmk⟩
    · have heq := head_eq_of_cons_suffix (h1.trans hcase) h2
      rw [heq]
    · rcases lt_trichotomy c.length cs.length with hlt | heqlen | hgt
      · exfalso
        have hic : (i :: c) <:+ cs :=
          List.suffix_of_suffix_length_le hi hcsm (by simp only [List.length_cons]; omega)
        have hjc : (j :: c) <:+ cs :=
          List.suffix_of_suffix_length_le hj hcsm1 (by simp only [List.length_cons]; omega)
        exact absurd (head_eq_of_cons_suffix hic hjc) hij.ne'
      · have hcd : c <:+ d m := (List.suffix_cons i c).trans hi
        have hccs : c = cs :=
          (List.suffix_of_suffix_length_le hcd hcsm (le_of_eq heqlen)).eq_of_length heqlen
        subst hccs
        have hxi : i = x m := head_eq_of_cons_suffix hi h1
        have hxj : j = x (m + 1) := head_eq_of_cons_suffix hj h2
        rw [← hxi, ← hxj]
        exact le_of_lt hij
      · have hcd : c <:+ d m := (List.suffix_cons i c).trans hi
        have hcd1 : c <:+ d (m + 1) := (List.suffix_cons j c).trans hj
        have hxc : (x m :: cs) <:+ c :=
          List.suffix_of_suffix_length_le h1 hcd (by simp only [List.length_cons]; omega)
        have hxc1 : (x (m + 1) :: cs) <:+ c :=
          List.suffix_of_suffix_length_le h2 hcd1 (by simp only [List.length_cons]; omega)
        have heq := head_eq_of_cons_suffix hxc hxc1
        rw [heq]
    · have heq := head_eq_of_cons_suffix (h2.trans hsuf) h1
      rw [heq]
  -- hence it is eventually constant, contradicting the maximality of `cs`
  have hmono : ∀ m, N2 ≤ m → ∀ k, (x (m + k) : ℕ) ≤ (x m : ℕ) := by
    intro m hm k
    induction k with
    | zero => exact le_refl _
    | succ k ih =>
        have := hanti (m + k) (by omega)
        have h2 : m + (k + 1) = (m + k) + 1 := by omega
        rw [h2]
        omega
  obtain ⟨m0, hm0N2, hm0min⟩ : ∃ m0, N2 ≤ m0 ∧ ∀ m, N2 ≤ m → (x m0 : ℕ) ≤ (x m : ℕ) := by
    have hex : ∃ v, ∃ m, N2 ≤ m ∧ (x m : ℕ) = v := ⟨_, N2, le_refl _, rfl⟩
    obtain ⟨m0, hm0, hval⟩ := Nat.find_spec hex
    refine ⟨m0, hm0, fun m hm => ?_⟩
    have : Nat.find hex ≤ (x m : ℕ) := Nat.find_min' hex ⟨m, hm, rfl⟩
    omega
  have hconst : ∀ m, m0 ≤ m → x m = x m0 := by
    intro m hm
    have h1 : (x m : ℕ) ≤ (x m0 : ℕ) := by
      have := hmono m0 hm0N2 (m - m0)
      rw [show m0 + (m - m0) = m from by omega] at this
      exact this
    have h2 : (x m0 : ℕ) ≤ (x m : ℕ) := hm0min m (by omega)
    exact Fin.ext (by omega)
  have hstable : ∃ N, ∀ n, N ≤ n → (x m0 :: cs) <:+ d n := by
    refine ⟨m0, fun n hn => ?_⟩
    rw [← hconst n hn]
    exact hx n (by omega)
  have := hcsmax (x m0 :: cs) hstable
  simp only [List.length_cons] at this
  omega

end Safra

end Lax369799Proofs.WordAutomata
