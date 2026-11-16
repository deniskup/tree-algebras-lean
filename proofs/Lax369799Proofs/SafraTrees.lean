/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Safra.Tree.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Lax369799Proofs.BuchiWordAutomata
import Mathlib.Data.Set.Card

/-!
# Safra trees

This file sets up the data structure underlying **Safra's determinization construction** for
nondeterministic Büchi automata on ω-words, together with its elementary invariants.

A *Safra tree* over a finite set of states `Q` is a finitely branching tree whose nodes carry
subsets of `Q`.  Nodes are identified with their *position*: a list of slots, the head of the
list being the slot of the node among the children of its parent, the tail being the position
of the parent.  Thus the empty list is the root and `p <:+ r` ("`p` is a suffix of `r`")
means that `p` is an ancestor of `r`.  A node is *present* when its label is nonempty.

The transition of the construction (`Lax369799Proofs.WordAutomata.Safra.stepTree`) is the usual one:

* every node with a label meeting the Büchi set `B.fin` gets a new child, in a free slot,
  labelled by that intersection (`Lax369799Proofs.WordAutomata.Safra.lab1`);
* every label is replaced by the set of its successors under the letter read
  (`Lax369799Proofs.WordAutomata.Safra.lab1` again);
* a state occurring in several children of a node is kept only in the child with the smallest
  slot, and this removal is inherited by all the descendants
  (`Lax369799Proofs.WordAutomata.Safra.lab2`);
* a node whose label is covered by the labels of its children is *marked*
  (`Lax369799Proofs.WordAutomata.Safra.vmark`) and all its strict descendants are deleted
  (`Lax369799Proofs.WordAutomata.Safra.killed`).

The three basic invariants (`Lax369799Proofs.WordAutomata.Safra.stepTree_child_subset`,
`Lax369799Proofs.WordAutomata.Safra.stepTree_disjoint`, `Lax369799Proofs.WordAutomata.Safra.stepTree_ssubset`) hold after one
step, whatever the tree one starts from; they imply the bound on the depth of the present
nodes (`Lax369799Proofs.WordAutomata.Safra.length_le_of_inv`) which makes the state space finite.
-/

namespace Lax369799Proofs.WordAutomata

namespace Safra

open scoped Classical

variable {Q Gam : Type}

/-- The number of slots available for the children of a node.  A node has at most
`Fintype.card Q` children with a nonempty label (they are pairwise disjoint), so one slot is
always free. -/
def numSlots (Q : Type) [Fintype Q] : ℕ := Fintype.card Q + 1

/-- The slots of the children of a node. -/
abbrev Slot (Q : Type) [Fintype Q] : Type := Fin (numSlots Q)

/-- The position of a node of a Safra tree: the list of the slots on the way *up* to the
root, so that the head is the slot of the node itself and the empty list is the root. -/
abbrev Pos (Q : Type) [Fintype Q] : Type := List (Slot Q)

/-- The set of states reachable in one step from a set of states. -/
def succSet (B : NBuchi Q Gam) (a : Gam) (X : Set Q) : Set Q := {q' | ∃ q ∈ X, B.step q a q'}

theorem succSet_mono (B : NBuchi Q Gam) (a : Gam) {X Y : Set Q} (h : X ⊆ Y) :
    succSet B a X ⊆ succSet B a Y := by
  rintro q ⟨p, hp, hstep⟩
  exact ⟨p, h hp, hstep⟩

@[simp] theorem succSet_empty (B : NBuchi Q Gam) (a : Gam) : succSet B a (∅ : Set Q) = ∅ := by
  ext q; simp [succSet]

variable [Fintype Q]

/-- A Safra tree: a labelling of the positions by sets of states (the empty set meaning that
the node is absent) together with the set of marked positions. -/
structure STree (Q : Type) [Fintype Q] where
  /-- The label of a node; `∅` means that the node is absent. -/
  lab : Pos Q → Set Q
  /-- The nodes that are marked, i.e. that have just completed a round. -/
  mark : Pos Q → Prop

/-- A slot which is free for a new child of `p`, if there is one: the first one, so that the
choice is canonical (and computable when the labels are). -/
noncomputable def freshSlot (T : STree Q) (p : Pos Q) : Option (Slot Q) :=
  (List.finRange (numSlots Q)).find? (fun i => decide (T.lab (i :: p) = ∅))

theorem lab_eq_empty_of_freshSlot {T : STree Q} {p : Pos Q} {i : Slot Q}
    (h : freshSlot T p = some i) : T.lab (i :: p) = ∅ := by
  rw [freshSlot] at h
  have hp := List.find?_some (p := fun i : Slot Q => decide (T.lab (i :: p) = ∅)) h
  exact of_decide_eq_true hp

/-- The label of a node after the creation of the new children and the powerset step. -/
noncomputable def lab1 (B : NBuchi Q Gam) (T : STree Q) (a : Gam) : Pos Q → Set Q
  | [] => succSet B a (T.lab [])
  | i :: p =>
      if freshSlot T p = some i then succSet B a (T.lab p ∩ B.fin)
      else succSet B a (T.lab (i :: p))

@[simp] theorem lab1_nil (B : NBuchi Q Gam) (T : STree Q) (a : Gam) :
    lab1 B T a [] = succSet B a (T.lab []) := rfl

theorem lab1_cons (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (i : Slot Q) (p : Pos Q) :
    lab1 B T a (i :: p) =
      if freshSlot T p = some i then succSet B a (T.lab p ∩ B.fin)
      else succSet B a (T.lab (i :: p)) := rfl

theorem lab1_cons_of_ne (B : NBuchi Q Gam) (T : STree Q) (a : Gam) {i : Slot Q} {p : Pos Q}
    (h : freshSlot T p ≠ some i) : lab1 B T a (i :: p) = succSet B a (T.lab (i :: p)) := by
  rw [lab1_cons, if_neg h]

/-- The label of a node after the horizontal merge: a state is kept only in the child with
the smallest slot containing it, and the removals are inherited by the descendants. -/
noncomputable def lab2 (B : NBuchi Q Gam) (T : STree Q) (a : Gam) : Pos Q → Set Q
  | [] => lab1 B T a []
  | i :: p =>
      (lab1 B T a (i :: p) ∩ lab2 B T a p) \ ⋃ (j : Slot Q) (_ : j < i), lab1 B T a (j :: p)

@[simp] theorem lab2_nil (B : NBuchi Q Gam) (T : STree Q) (a : Gam) :
    lab2 B T a [] = lab1 B T a [] := rfl

theorem lab2_cons (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (i : Slot Q) (p : Pos Q) :
    lab2 B T a (i :: p) =
      (lab1 B T a (i :: p) ∩ lab2 B T a p) \ ⋃ (j : Slot Q) (_ : j < i), lab1 B T a (j :: p) :=
  rfl

theorem lab2_subset_lab1 (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (p : Pos Q) :
    lab2 B T a p ⊆ lab1 B T a p := by
  cases p with
  | nil => exact subset_rfl
  | cons i p => exact fun q hq => hq.1.1

theorem lab2_cons_subset (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (i : Slot Q) (p : Pos Q) :
    lab2 B T a (i :: p) ⊆ lab2 B T a p := fun _ hq => hq.1.2

/-- Along a branch, the labels decrease. -/
theorem lab2_mono (B : NBuchi Q Gam) (T : STree Q) (a : Gam) {p r : Pos Q} (h : p <:+ r) :
    lab2 B T a r ⊆ lab2 B T a p := by
  obtain ⟨s, rfl⟩ := h
  induction s with
  | nil => exact subset_rfl
  | cons i s ih =>
      exact fun q hq => ih (lab2_cons_subset B T a i (s ++ p) hq)

/-- Two different children of a node have disjoint labels. -/
theorem lab2_disjoint (B : NBuchi Q Gam) (T : STree Q) (a : Gam) {i j : Slot Q} (p : Pos Q)
    (hij : i ≠ j) : lab2 B T a (i :: p) ∩ lab2 B T a (j :: p) = ∅ := by
  ext q
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hi hj
  rcases lt_trichotomy i j with h | h | h
  · exact hj.2 (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨h, lab2_subset_lab1 B T a _ hi⟩⟩)
  · exact absurd h hij
  · exact hi.2 (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨h, lab2_subset_lab1 B T a _ hj⟩⟩)

/-- A node is *marked* when its label is covered by the labels of its children: a round has
been completed. -/
def vmark (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (p : Pos Q) : Prop :=
  (lab2 B T a p).Nonempty ∧ lab2 B T a p ⊆ ⋃ i : Slot Q, lab2 B T a (i :: p)

/-- A node is deleted when one of its strict ancestors is marked. -/
def killed (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (p : Pos Q) : Prop :=
  ∃ c, c <:+ p ∧ c ≠ p ∧ vmark B T a c

theorem killed_of_killed_cons (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (i : Slot Q)
    (p : Pos Q) (h : killed B T a p) : killed B T a (i :: p) := by
  obtain ⟨c, hc, hcp, hm⟩ := h
  exact ⟨c, hc.trans (List.suffix_cons i p), by
    intro hcc
    subst hcc
    exact absurd (hc.eq_of_length (by simpa using (hc.length_le))) hcp, hm⟩

theorem killed_cons_of_vmark (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (i : Slot Q)
    (p : Pos Q) (h : vmark B T a p) : killed B T a (i :: p) :=
  ⟨p, List.suffix_cons i p, by simp, h⟩

/-- One step of Safra's construction. -/
noncomputable def stepTree (B : NBuchi Q Gam) (T : STree Q) (a : Gam) : STree Q where
  lab p := if killed B T a p then ∅ else lab2 B T a p
  mark p := vmark B T a p ∧ ¬ killed B T a p

theorem stepTree_lab (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (p : Pos Q) :
    (stepTree B T a).lab p = if killed B T a p then ∅ else lab2 B T a p := rfl

theorem stepTree_lab_subset (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (p : Pos Q) :
    (stepTree B T a).lab p ⊆ lab2 B T a p := by
  rw [stepTree_lab]
  split
  · exact Set.empty_subset _
  · exact subset_rfl

theorem stepTree_lab_of_not_killed (B : NBuchi Q Gam) (T : STree Q) (a : Gam) {p : Pos Q}
    (h : ¬ killed B T a p) : (stepTree B T a).lab p = lab2 B T a p := by
  rw [stepTree_lab, if_neg h]

theorem stepTree_mark (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (p : Pos Q) :
    (stepTree B T a).mark p ↔ vmark B T a p ∧ ¬ killed B T a p := Iff.rfl

/-! ### The invariants -/

/-- The label of a child is contained in the label of its parent. -/
theorem stepTree_child_subset (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (i : Slot Q)
    (p : Pos Q) : (stepTree B T a).lab (i :: p) ⊆ (stepTree B T a).lab p := by
  by_cases h : killed B T a p
  · rw [stepTree_lab, if_pos (killed_of_killed_cons B T a i p h)]
    exact Set.empty_subset _
  · rw [stepTree_lab_of_not_killed B T a h]
    exact (stepTree_lab_subset B T a (i :: p)).trans (lab2_cons_subset B T a i p)

/-- The labels decrease along a branch. -/
theorem stepTree_mono (B : NBuchi Q Gam) (T : STree Q) (a : Gam) {p r : Pos Q} (h : p <:+ r) :
    (stepTree B T a).lab r ⊆ (stepTree B T a).lab p := by
  obtain ⟨s, rfl⟩ := h
  induction s with
  | nil => exact subset_rfl
  | cons i s ih => exact (stepTree_child_subset B T a i (s ++ p)).trans ih

/-- Two different children of a node have disjoint labels. -/
theorem stepTree_disjoint (B : NBuchi Q Gam) (T : STree Q) (a : Gam) {i j : Slot Q}
    (p : Pos Q) (hij : i ≠ j) :
    (stepTree B T a).lab (i :: p) ∩ (stepTree B T a).lab (j :: p) = ∅ := by
  refine Set.eq_empty_of_subset_empty ?_
  rw [← lab2_disjoint B T a p hij]
  exact Set.inter_subset_inter (stepTree_lab_subset B T a _) (stepTree_lab_subset B T a _)

/-- The label of a present child is a *strict* subset of the label of its parent: this is
what bounds the depth of a Safra tree. -/
theorem stepTree_ssubset (B : NBuchi Q Gam) (T : STree Q) (a : Gam) (i : Slot Q) (p : Pos Q)
    (h : (stepTree B T a).lab (i :: p) ≠ ∅) :
    (stepTree B T a).lab (i :: p) ⊂ (stepTree B T a).lab p := by
  have hkill : ¬ killed B T a (i :: p) := by
    intro hk
    rw [stepTree_lab, if_pos hk] at h
    exact h rfl
  have hkp : ¬ killed B T a p := fun hk => hkill (killed_of_killed_cons B T a i p hk)
  have hvm : ¬ vmark B T a p := fun hv => hkill (killed_cons_of_vmark B T a i p hv)
  rw [stepTree_lab_of_not_killed B T a hkill, stepTree_lab_of_not_killed B T a hkp] at *
  refine ⟨lab2_cons_subset B T a i p, ?_⟩
  intro hsub
  -- otherwise the label of `p` is covered by the labels of its children, so `p` is marked
  refine hvm ⟨?_, ?_⟩
  · obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.2 h
    exact ⟨q, lab2_cons_subset B T a i p hq⟩
  · intro q hq
    exact Set.mem_iUnion.2 ⟨i, hsub hq⟩

/-! ### Consequences of the invariants -/

/-- The invariants of a Safra tree. -/
structure Inv (T : STree Q) : Prop where
  /-- The label of a child is contained in the label of its parent. -/
  mono : ∀ (i : Slot Q) (p : Pos Q), T.lab (i :: p) ⊆ T.lab p
  /-- Two different children of a node have disjoint labels. -/
  disj : ∀ {i j : Slot Q} (p : Pos Q), i ≠ j → T.lab (i :: p) ∩ T.lab (j :: p) = ∅
  /-- The label of a present child is a strict subset of the label of its parent. -/
  ssub : ∀ (i : Slot Q) (p : Pos Q), T.lab (i :: p) ≠ ∅ → T.lab (i :: p) ⊂ T.lab p

theorem inv_stepTree (B : NBuchi Q Gam) (T : STree Q) (a : Gam) : Inv (stepTree B T a) where
  mono i p := stepTree_child_subset B T a i p
  disj p hij := stepTree_disjoint B T a p hij
  ssub i p h := stepTree_ssubset B T a i p h

/-- The labels decrease along a branch. -/
theorem Inv.mono' {T : STree Q} (hT : Inv T) {p r : Pos Q} (h : p <:+ r) :
    T.lab r ⊆ T.lab p := by
  obtain ⟨s, rfl⟩ := h
  induction s with
  | nil => exact subset_rfl
  | cons i s ih => exact (hT.mono i (s ++ p)).trans ih

/-- The number of states of the label of a node, plus the depth of the node, is at most the
number of states of the automaton. -/
theorem Inv.ncard_add_length_le {T : STree Q} (hT : Inv T) :
    ∀ (p : Pos Q), T.lab p ≠ ∅ → (T.lab p).ncard + p.length ≤ Fintype.card Q := by
  intro p
  induction p with
  | nil =>
      intro _
      have h1 : (T.lab ([] : Pos Q)).ncard ≤ (Set.univ : Set Q).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
      rw [Set.ncard_univ] at h1
      simpa using h1
  | cons i p ih =>
      intro h
      have hp : T.lab p ≠ ∅ := by
        intro hp0
        exact h (Set.eq_empty_of_subset_empty (hp0 ▸ hT.mono i p))
      have hlt : (T.lab (i :: p)).ncard < (T.lab p).ncard :=
        Set.ncard_lt_ncard (hT.ssub i p h) (Set.toFinite _)
      have := ih hp
      simp only [List.length_cons]
      omega

/-- Present nodes have a bounded depth. -/
theorem Inv.length_lt {T : STree Q} (hT : Inv T) {p : Pos Q} (h : T.lab p ≠ ∅) :
    p.length < Fintype.card Q := by
  have h1 : 0 < (T.lab p).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 (Set.nonempty_iff_ne_empty.2 h)
  have := hT.ncard_add_length_le p h
  omega

/-- There is always a free slot for a new child. -/
theorem Inv.exists_free_slot {T : STree Q} (hT : Inv T) (p : Pos Q) :
    ∃ i : Slot Q, T.lab (i :: p) = ∅ := by
  by_contra hcon
  push_neg at hcon
  choose f hf using hcon
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have := hT.disj (i := i) (j := j) p hne
    have hmem : f i ∈ T.lab (i :: p) ∩ T.lab (j :: p) := ⟨hf i, hij ▸ hf j⟩
    rw [this] at hmem
    exact hmem
  have := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_fin] at this
  simp only [numSlots] at this
  omega

/-- The `freshSlot` of a node is defined as soon as the invariants hold. -/
theorem Inv.freshSlot_isSome {T : STree Q} (hT : Inv T) (p : Pos Q) :
    ∃ i : Slot Q, freshSlot T p = some i := by
  obtain ⟨i, hi⟩ := hT.exists_free_slot p
  rcases hfs : freshSlot T p with - | j
  · rw [freshSlot, List.find?_eq_none] at hfs
    exact absurd (decide_eq_true hi) (hfs i (List.mem_finRange i))
  · exact ⟨j, rfl⟩

/-- Two nodes whose labels contain a common state are comparable. -/
theorem Inv.suffix_of_mem_of_length_le {T : STree Q} (hT : Inv T) {q : Q} :
    ∀ (r p : Pos Q), p.length ≤ r.length → q ∈ T.lab p → q ∈ T.lab r → p <:+ r := by
  intro r
  induction r with
  | nil =>
      intro p hlen hp _
      simp only [List.length_nil, Nat.le_zero, List.length_eq_zero_iff] at hlen
      subst hlen
      exact List.nil_suffix
  | cons i r ih =>
      intro p hlen hp hr
      rcases Nat.lt_or_ge r.length p.length with hlt | hge
      · -- the lengths are equal
        have hplen : p.length = r.length + 1 := by simp only [List.length_cons] at hlen; omega
        match p, hplen with
        | j :: p', hplen =>
          have hp'len : p'.length = r.length := by simpa using hplen
          have hp' : q ∈ T.lab p' := hT.mono j p' hp
          have hr' : q ∈ T.lab r := hT.mono i r hr
          have : p' <:+ r := ih p' (le_of_eq hp'len) hp' hr'
          have hp'r : p' = r := this.eq_of_length (by omega)
          subst hp'r
          by_cases hij : j = i
          · subst hij; exact List.suffix_rfl
          · exfalso
            have hd := hT.disj (i := j) (j := i) p' hij
            have : q ∈ T.lab (j :: p') ∩ T.lab (i :: p') := ⟨hp, hr⟩
            rw [hd] at this
            exact this
      · exact (ih p hge hp (hT.mono i r hr)).trans (List.suffix_cons i r)

/-- Two nodes whose labels contain a common state are comparable. -/
theorem Inv.comparable {T : STree Q} (hT : Inv T) {q : Q} {p r : Pos Q} (hp : q ∈ T.lab p)
    (hr : q ∈ T.lab r) : p <:+ r ∨ r <:+ p := by
  rcases le_total p.length r.length with h | h
  · exact Or.inl (hT.suffix_of_mem_of_length_le r p h hp hr)
  · exact Or.inr (hT.suffix_of_mem_of_length_le p r h hr hp)

end Safra

end Lax369799Proofs.WordAutomata
