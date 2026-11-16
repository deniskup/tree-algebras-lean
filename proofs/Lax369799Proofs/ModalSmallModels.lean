import Lax369799.ModalSmallModels
import Lax369799Proofs.ParityGameSimulation
import Lax369799Proofs.ModalAcceptanceGame
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finite.Set

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.ModalSmallModels
open Lax369799
open TransitionSystems TransitionEncoding UnfoldAutomata ModalTransitions
open FiniteParityGames ParityWinningRegions
open ModalAcceptanceGame (Marking ceiling)

private abbrev Vertex {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) := Fin M.condition.states ⊕ ((S.Vertex × Marking M S) ⊕ Bool)
private def pos {P : Type} {M : UnfoldAutomaton (TransitionAlphabet P)} {S : TransitionSystem P}
    (q : Fin M.condition.states) : Vertex M S := .inl q
private def sel {P : Type} {M : UnfoldAutomaton (TransitionAlphabet P)} {S : TransitionSystem P}
    (v : S.Vertex) (ρ : Marking M S) : Vertex M S := .inr (.inl (v,ρ))
private def term {P : Type} {M : UnfoldAutomaton (TransitionAlphabet P)} {S : TransitionSystem P}
    (b : Bool) : Vertex M S := .inr (.inr b)

private def Edge {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Vertex M S → Vertex M S → Prop
  | .inl q,.inr (.inl (v,ρ)) => OneStep M q S v ρ
  | .inl _,.inr (.inr false) => True
  | .inr (.inl (v,ρ)),.inl q => ∃ w,S.edge v w ∧ w ∈ ρ q
  | .inr (.inl (v,ρ)),.inr (.inr true) => ¬∃ q w,S.edge v w ∧ w ∈ ρ q
  | .inr (.inr b),.inr (.inr c) => b = c
  | _,_ => False

private def owner {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Vertex M S → Prop
  | .inl _ => True
  | .inr _ => False

private def priority {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Vertex M S → ℕ
  | .inl q => ceiling M.condition - M.condition.priority q
  | .inr (.inr false) => 1
  | _ => 0

private noncomputable def merged {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) : Game (Vertex M S) where
  eve := owner M S
  edge := Edge M S
  priority := priority M S
  total := by
    classical
    intro v
    rcases v with q | (⟨v,ρ⟩ | b)
    · exact ⟨term false,trivial⟩
    · by_cases h : ∃ q w,S.edge v w ∧ w ∈ ρ q
      · obtain ⟨q,w,h⟩ := h;exact ⟨pos q,w,h⟩
      · exact ⟨term true,h⟩
    · exact ⟨term b,rfl⟩

private def project {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    ModalAcceptanceGame.Vertex M S → Vertex M S
  | .inl (q,_) => pos q
  | .inr (.inl (v,ρ)) => sel v ρ
  | .inr (.inr b) => term b

private theorem source_simulation {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    ParityGameSimulation.Simulation (ModalAcceptanceGame.game M S) (merged M S)
      (fun x y => y = project M S x) where
  owner := by
    intro x y h;subst y
    rcases x with ⟨q,v⟩ | (⟨v,ρ⟩ | b) <;> exact Iff.rfl
  priority := by
    intro x y h;subst y
    rcases x with ⟨q,v⟩ | (⟨v,ρ⟩ | b)
    · rfl
    · rfl
    · cases b <;> rfl
  eve_step := by
    intro x y h he x' hx
    subst y
    rcases x with ⟨q,v⟩ | (⟨v,ρ⟩ | b)
    · rcases x' with ⟨p,w⟩ | (⟨w,ρ⟩ | b)
      · exact False.elim hx
      · have hw : v = w := hx.1
        subst w
        exact ⟨sel v ρ,hx.2,rfl⟩
      · cases b with
        | false => exact ⟨term false,trivial,rfl⟩
        | true => exact False.elim hx
    · exact False.elim he
    · exact False.elim he
  adam_step := by
    intro x y h hn y' hy
    subst y
    rcases x with ⟨q,v⟩ | (⟨v,ρ⟩ | b)
    · exact (hn trivial).elim
    · rcases y' with q | (⟨w,σ⟩ | b)
      · obtain ⟨w,hw⟩ := hy
        exact ⟨ModalAcceptanceGame.position q w,hw,rfl⟩
      · exact False.elim hy
      · cases b with
        | false => exact False.elim hy
        | true => exact ⟨ModalAcceptanceGame.terminal true,hy,rfl⟩
    · rcases y' with q | (⟨w,σ⟩ | c)
      · exact False.elim hy
      · exact False.elim hy
      · exact ⟨ModalAcceptanceGame.terminal c,hy,rfl⟩

private theorem merged_winning {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P)
    (h : Winning (ModalAcceptanceGame.game M S) true
      (ModalAcceptanceGame.position M.condition.initial S.initial)) :
    Winning (merged M S) true (pos M.condition.initial) := by
  let : Finite (Vertex M S) := by unfold Vertex Marking;infer_instance
  exact ParityGameSimulation.winning _ _ _ (source_simulation M S) _ _ rfl h

private theorem losing_terminal {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (f : Vertex M S → Vertex M S) :
    ¬(merged M S).WinsFrom true f (term false) := by
  intro h
  have hp : (merged M S).IsPlay (fun _ => term false) := fun _ => rfl
  have hc : (merged M S).Consistent true f (fun _ => term false) := by
    intro _ hn
    exact (hn.mpr rfl).elim
  obtain ⟨c,⟨hr,_⟩,he⟩ := (h _ hp rfl hc).mpr rfl
  obtain ⟨n,_,hn⟩ := hr 0
  change 1 = c at hn
  subst c
  simpa using he

private theorem reachable_model {P W : Type} [Finite W] (w0 : W)
    (E : W → W → Prop) (ν : W → Set P) :
    ∃ (T : TransitionSystem P) (e : T.Vertex → W),
      Function.Injective e ∧ e T.initial = w0 ∧
      (∀ v w,T.edge v w ↔ E (e v) (e w)) ∧ (∀ v,T.valuation v = ν (e v)) ∧
      (∀ v w,E (e v) w → ∃ u,e u = w) ∧ T.size ≤ Nat.card W := by
  classical
  let R := {w : W // Relation.ReflTransGen E w0 w}
  let : Fintype R := Fintype.ofFinite R
  let e := Fintype.equivFin R
  let start : R := ⟨w0,.refl⟩
  let T : TransitionSystem P := {
    size := Fintype.card R
    initial := e start
    edge := fun v w => E (e.symm v).val (e.symm w).val
    valuation := fun v => ν (e.symm v).val
    reachable := by
      have path : ∀ w (h : Relation.ReflTransGen E w0 w),
          Relation.ReflTransGen (fun v w => E (e.symm v).val (e.symm w).val)
            (e start) (e ⟨w,h⟩) := by
        intro w h
        induction h with
        | refl => exact .refl
        | @tail b c h he ih =>
          apply ih.tail
          simpa only [e.symm_apply_apply] using he
      intro v
      have hp := path (e.symm v).val (e.symm v).property
      change Relation.ReflTransGen _ _ (e (e.symm v)) at hp
      simpa only [e.apply_symm_apply] using hp }
  refine ⟨T,(fun v => (e.symm v).val),?_,?_,fun _ _ => Iff.rfl,fun _ => rfl,?_,?_⟩
  · intro a b h
    exact e.symm.injective (Subtype.ext h)
  · exact congrArg Subtype.val (e.symm_apply_apply start)
  · intro v w hw
    let w' : R := ⟨w,(e.symm v).property.tail hw⟩
    exact ⟨e w',congrArg Subtype.val (e.symm_apply_apply w')⟩
  · change Fintype.card R ≤ Nat.card W
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective (fun r : R => r.val) Subtype.val_injective

private structure Ports {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (q : Fin M.condition.states) (v : S.Vertex) (ρ : Marking M S) where
  types : Set (Fin M.unary)
  allowed : (types = ∅ ∧ (∃ a ∈ M.leafTransition (S.valuation v),
      M.condition.step q (.inr a) ∈ M.condition.final) ∧ (∀ w,¬S.edge v w)) ∨
    Realized M (S.valuation v) types
  advance : ∀ b ∈ types,∃ w,S.edge v w ∧ w ∈ ρ (M.condition.step q (.inl b))

private theorem ports_exists {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (q : Fin M.condition.states) (v : S.Vertex) (ρ : Marking M S)
    (h : OneStep M q S v ρ) : Nonempty (Ports M S q v ρ) := by
  rcases h with ⟨ha,hn⟩ | ⟨B,hB,hb,hall⟩
  · exact ⟨⟨∅,Or.inl ⟨rfl,ha,hn⟩,fun _ h => h.elim⟩⟩
  · exact ⟨⟨B,Or.inr hB,hb⟩⟩

private noncomputable def restrict {V : Type} (G : Game V) (f : V → V) (hf : G.Legal true f) : Game V where
  eve := G.eve
  priority := G.priority
  edge := fun v w => G.edge v w ∧ (G.eve v → w = f v)
  total := by
    classical
    intro v
    by_cases hv : G.eve v
    · exact ⟨f v,hf v (by simp [hv]),fun _ => rfl⟩
    · obtain ⟨w,hw⟩ := G.total v
      exact ⟨w,hw,fun h => (hv h).elim⟩

private theorem restrict_winning {V : Type} (G : Game V) (f : V → V) (hf : G.Legal true f)
    (v : V) (h : G.WinsFrom true f v) : Winning (restrict G f hf) true v := by
  refine ⟨f,?_,?_⟩
  · intro w hw
    exact ⟨hf w hw,fun _ => rfl⟩
  · intro p hp hs hc
    exact h p (fun n => (hp n).1) hs (fun n hn => (hp n).2 (hn.mpr rfl))

/--
---
conclusion: Lax369799.ModalSmallModels.small_model
---
Merge the input vertices at each word state, transferring the winning
strategy by alternating simulation. A positional strategy selects one
local transition per winning word state. Keep its required successors
and restrict to reachable states; a second simulation proves acceptance.
-/
theorem small_model {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P)
    (h : Winning (ModalAcceptanceGame.game M S) true
      (ModalAcceptanceGame.position M.condition.initial S.initial)) :
    ∃ T : TransitionSystem P,T.size ≤ M.condition.states ∧
      Winning (ModalAcceptanceGame.game M T) true
        (ModalAcceptanceGame.position M.condition.initial T.initial) := by
  classical
  obtain ⟨f,hf,hw⟩ := merged_winning M S h
  let H := merged M S
  let W := {q : Fin M.condition.states // H.WinsFrom true f (pos q)}
  let start : W := ⟨M.condition.initial,hw⟩
  have choices (q : W) : ∃ v ρ,f (pos q.val) = sel v ρ ∧ OneStep M q.val S v ρ := by
    have he := hf (pos q.val) (by simp [merged,owner,pos])
    rcases hd : f (pos q.val) with p | (⟨v,ρ⟩ | b)
    · rw [hd] at he;exact False.elim he
    · rw [hd] at he;exact ⟨v,ρ,rfl,he⟩
    · cases b with
      | true => rw [hd] at he;exact False.elim he
      | false =>
        have ht := ParityWinningRegions.move H true f (pos q.val) (term false)
          q.property (by exact trivial) (fun _ => hd.symm)
        exact (losing_terminal M S f ht).elim
  choose source mark hchoice hone using choices
  let data (q : W) := (ports_exists M S q.val (source q) (mark q) (hone q)).some
  have selection_wins (q : W) : H.WinsFrom true f (sel (source q) (mark q)) := by
    apply ParityWinningRegions.move H true f (pos q.val) _ q.property
    · exact hone q
    · intro _;exact (hchoice q).symm
  have next_wins (q : W) (b : Fin M.unary) (hb : b ∈ (data q).types) :
      H.WinsFrom true f (pos (M.condition.step q.val (.inl b))) := by
    apply ParityWinningRegions.move H true f _ _ (selection_wins q)
    · exact (data q).advance b hb
    · intro hn;exact (hn.mpr rfl).elim
  let next (q : W) (b : Fin M.unary) (hb : b ∈ (data q).types) : W :=
    ⟨M.condition.step q.val (.inl b),next_wins q b hb⟩
  let E : W → W → Prop := fun q p => ∃ b ∈ (data q).types,p.val = M.condition.step q.val (.inl b)
  obtain ⟨T,e,hei,hstart,hedge,hval,hclosed,hsize⟩ :=
    reachable_model start E (fun q => S.valuation (source q))
  let state (v : T.Vertex) := (e v).val
  let diag : Marking M T := fun p => {w | state w = p}
  have successor (v : T.Vertex) (b : Fin M.unary) (hb : b ∈ (data (e v)).types) :
      ∃ w,T.edge v w ∧ state w = M.condition.step (state v) (.inl b) := by
    obtain ⟨w,hw⟩ := hclosed v (next (e v) b hb) ⟨b,hb,rfl⟩
    exact ⟨w,(hedge v w).mpr (hw.symm ▸ (show E (e v) (next (e v) b hb) from ⟨b,hb,rfl⟩)),
      congrArg Subtype.val hw⟩
  have hlocal (v : T.Vertex) : OneStep M (state v) T v diag := by
    rcases (data (e v)).allowed with ⟨hempty,ha,hn⟩ | hB
    · refine Or.inl ⟨?_,?_⟩
      · rw [hval v];exact ha
      · intro w hw
        obtain ⟨b,hb,_⟩ := (hedge v w).mp hw
        rw [hempty] at hb;exact hb.elim
    · refine Or.inr ⟨(data (e v)).types,?_,?_,?_⟩
      · rw [hval v];exact hB
      · intro b hb
        exact successor v b hb
      · intro w hw
        obtain ⟨b,hb,he⟩ := (hedge v w).mp hw
        exact ⟨b,hb,he⟩
  have hcard : T.size ≤ M.condition.states := hsize.trans
    (by simpa using Nat.card_le_card_of_injective (fun q : W => q.val) Subtype.val_injective)
  have hmodel : Winning (ModalAcceptanceGame.game M T) true
      (ModalAcceptanceGame.position M.condition.initial T.initial) := by
    let K := restrict H f hf
    let R : Vertex M S → ModalAcceptanceGame.Vertex M T → Prop := fun x y =>
      (∃ v : T.Vertex,x = pos (state v) ∧ y = ModalAcceptanceGame.position (state v) v) ∨
      (∃ v : T.Vertex,x = f (pos (state v)) ∧ y = ModalAcceptanceGame.selection v diag) ∨
      (x = term true ∧ y = ModalAcceptanceGame.terminal true)
    have sim : ParityGameSimulation.Simulation K (ModalAcceptanceGame.game M T) R := {
      owner := by
        intro x y hr
        rcases hr with ⟨v,rfl,rfl⟩ | ⟨v,rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Iff.rfl
        · change H.eve (f (pos (state v))) ↔ False
          rw [hchoice (e v)]
          exact Iff.rfl
        · exact Iff.rfl
      priority := by
        intro x y hr
        rcases hr with ⟨v,rfl,rfl⟩ | ⟨v,rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rfl
        · change H.priority (f (pos (state v))) = 0
          rw [hchoice (e v)]
          rfl
        · rfl
      eve_step := by
        intro x y hr he x' hx
        rcases hr with ⟨v,rfl,rfl⟩ | ⟨v,rfl,rfl⟩ | ⟨rfl,rfl⟩
        · have hxeq : x' = f (pos (state v)) := hx.2 trivial
          subst x'
          exact ⟨ModalAcceptanceGame.selection v diag,⟨rfl,hlocal v⟩,Or.inr (Or.inl ⟨v,rfl,rfl⟩)⟩
        · change H.eve (f (pos (state v))) at he
          rw [hchoice (e v)] at he
          exact he.elim
        · exact he.elim
      adam_step := by
        intro x y hr hn y' hy
        rcases hr with ⟨v,rfl,rfl⟩ | ⟨v,rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (hn trivial).elim
        · rcases y' with ⟨p,w⟩ | (⟨w,σ⟩ | b)
          · have hp : state w = p := hy.2
            subst p
            obtain ⟨b,hb,he⟩ := (hedge v w).mp hy.1
            refine ⟨pos (state w),⟨?_,?_⟩,Or.inl ⟨w,rfl,rfl⟩⟩
            · change H.edge (f (pos (state v))) (pos (state w))
              rw [hchoice (e v)]
              change ∃ t,S.edge (source (e v)) t ∧ t ∈ mark (e v) (state w)
              change state w = M.condition.step (state v) (.inl b) at he
              rw [he]
              exact (data (e v)).advance b hb
            · change H.eve (f (pos (state v))) → _
              rw [hchoice (e v)]
              intro hh;exact hh.elim
          · exact False.elim hy
          · cases b with
            | false => exact False.elim hy
            | true =>
              refine ⟨term true,⟨?_,?_⟩,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩
              · change H.edge (f (pos (state v))) (term true)
                rw [hchoice (e v)]
                change ¬∃ p w,S.edge (source (e v)) w ∧ w ∈ mark (e v) p
                rcases (data (e v)).allowed with ⟨_,_,hnone⟩ | hB
                · rintro ⟨p,w,hw,_⟩;exact hnone w hw
                · obtain ⟨b,hb⟩ := ModalTransitions.realized_nonempty M _ _ hB
                  obtain ⟨w,hw,hs⟩ := successor v b hb
                  exact False.elim (hy ⟨state w,w,hw,rfl⟩)
              · change H.eve (f (pos (state v))) → _
                rw [hchoice (e v)]
                intro hh;exact hh.elim
        · rcases y' with ⟨p,w⟩ | (⟨w,σ⟩ | b)
          · exact False.elim hy
          · exact False.elim hy
          · have hb : true = b := hy
            subst b
            exact ⟨term true,⟨rfl,fun hh => hh.elim⟩,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩ }
    have hk : Winning K true (pos M.condition.initial) := restrict_winning H f hf _ hw
    have hi : state T.initial = M.condition.initial := congrArg Subtype.val hstart
    have hrel : R (pos M.condition.initial) (ModalAcceptanceGame.position M.condition.initial T.initial) := by
      apply Or.inl
      exact ⟨T.initial,congrArg pos hi.symm,congrArg (fun p => ModalAcceptanceGame.position p T.initial) hi.symm⟩
    let : Finite (ModalAcceptanceGame.Vertex M T) := ModalAcceptanceGame.finite M T
    exact ParityGameSimulation.winning K (ModalAcceptanceGame.game M T) R sim _ _ hrel hk
  exact ⟨T,hcard,hmodel⟩

end Lax369799Proofs.ModalSmallModels
