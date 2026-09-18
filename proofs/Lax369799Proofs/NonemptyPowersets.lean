import Lax369799.NonemptyPowersets
import Lax369799Proofs.Flattening

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.NonemptyPowersets
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.Algebras Lax369799.PolynomialContexts Lax369799.NonemptyPowersets
open Lax369799Proofs.Pullbacks

private noncomputable def flat {A : RankedSet} {n : ℕ} (S : System (System A) n) : System A n :=
  ⟨flatten (relabel (fun _ T => T.val) S.val), by
    obtain ⟨T, ht⟩ := Flattening.flatten_system S
    rw [← ht]
    exact T.property⟩

private noncomputable abbrev raw {A : RankedSet} {n : ℕ} (S : System (System A) n) :=
  Flattening.graph (relabel (fun _ T => T.val) S.val)

private theorem flat_labels {A B : RankedSet} {n : ℕ} (S : System (System A) n)
    (q : ∀ v u, B (((S.val.graph.label v).2).val.graph.label u).1) :
    flat (withLabels S (fun v => withLabels (S.val.graph.label v).2 (q v))) =
      withLabels (flat S) (fun v => q (vertex (raw S) v).1 (vertex (raw S) v).2) := by
  rfl

private abbrev Choice {B : RankedSet} (a : Symbol (Carrier B)) := {b : B a.1 // b ∈ a.2.val}

private def chosenSymbol {B : RankedSet} (a : Symbol (Carrier B)) (q : Choice a) : Symbol B := ⟨a.1, q.val⟩

private theorem chosen_cast {B : RankedSet} {a b : Symbol (Carrier B)} (h : a = b) (q : Choice a) :
    chosenSymbol b (cast (congrArg Choice h) q) = chosenSymbol a q := by
  cases h
  rfl

private theorem values_choices {B : RankedSet} (E : Algebra B) {n : ℕ}
    (S : System (Carrier B) n) (b : B n) :
    b ∈ values E S ↔ ∃ q : ∀ v, Choice (S.val.graph.label v),
      E.eval n (withLabels S (fun v => (q v).val)) = b := by
  constructor
  · rintro ⟨q, hq, he⟩
    exact ⟨fun v => ⟨q v, hq v⟩, he⟩
  · rintro ⟨q, he⟩
    exact ⟨fun v => (q v).val, fun v => (q v).property, he⟩

private theorem values_iso {B : RankedSet} (E : Algebra B) {n : ℕ}
    (S T : System (Carrier B) n) (h : Isomorphic S.val T.val) : values E S = values E T := by
  classical
  obtain ⟨f, hf, hc⟩ := h
  let e := Equiv.ofBijective f.toFun hf
  let ec : (∀ v, Choice (S.val.graph.label v)) ≃ (∀ w, Choice (T.val.graph.label w)) :=
    Equiv.piCongr e (fun v => Equiv.cast (congrArg Choice (f.label v).symm))
  have he (q : ∀ v, Choice (S.val.graph.label v)) :
      E.eval n (withLabels S (fun v => (q v).val)) =
        E.eval n (withLabels T (fun v => (ec q v).val)) := by
    apply E.isomorphic
    refine ⟨{
      toFun := f.toFun
      initial := f.initial
      root := f.root
      edge := f.edge
      label := ?_ }, hf, hc⟩
    intro v
    change chosenSymbol (T.val.graph.label (e v)) (ec q (e v)) = chosenSymbol (S.val.graph.label v) (q v)
    dsimp only [ec]
    rw [Equiv.piCongr_apply_apply]
    exact chosen_cast (f.label v).symm (q v)
  ext b
  rw [values_choices, values_choices]
  constructor
  · rintro ⟨q, hb⟩
    exact ⟨ec q, (he q).symm.trans hb⟩
  · rintro ⟨q, hb⟩
    obtain ⟨q', rfl⟩ := ec.surjective q
    exact ⟨q', (he q').trans hb⟩

private theorem unit_value {B : RankedSet} (E : Algebra B) (n : ℕ) (X : Carrier B n) :
    evaluate E n (atomicSystem X) = X := by
  apply Subtype.ext
  ext b
  change b ∈ values E (atomicSystem X) ↔ b ∈ X.val
  have hu (q : Fin 1 → B n) :
      E.eval n (withLabels (atomicSystem X) q) = q 0 := by
    have he : q = fun _ => q 0 := funext (fun v => congrArg q (Subsingleton.elim v 0))
    rw [he]
    exact E.unit n (q 0)
  constructor
  · rintro ⟨q, hq, he⟩
    rw [hu] at he
    exact he ▸ hq (0 : Fin 1)
  · intro hb
    exact ⟨fun _ => b, fun _ => hb, E.unit n b⟩

private theorem extend_choices {B : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation (Carrier B) n V)
    (q : ∀ v : (trim G).Vertex, Choice ((trim G).graph.label v)) :
    ∃ p : ∀ v, Choice (G.label v), ∀ v, p (vertex G v) = q v := by
  classical
  let qr := Equiv.piCongrLeft (fun v : {v // G.Reachable v} => Choice (G.label v.val)) (index G).symm q
  let p (v : V) : Choice (G.label v) := if h : G.Reachable v then qr ⟨v, h⟩ else
    ⟨Classical.choose (G.label v).2.property, Classical.choose_spec (G.label v).2.property⟩
  refine ⟨p, ?_⟩
  intro v
  dsimp only [p]
  have hv : G.Reachable (vertex G v) := ((index G).symm v).property
  simp only [dif_pos hv]
  exact Equiv.piCongrLeft_apply_apply
    (fun v : {v // G.Reachable v} => Choice (G.label v.val)) (index G).symm q v

private theorem associative_value {B : RankedSet} (E : Algebra B) (n : ℕ)
    (S : System (System (Carrier B)) n) :
    evaluate E n (relabelSystem (evaluate E) S) = evaluate E n (flat S) := by
  classical
  apply Subtype.ext
  ext b
  change b ∈ values E (relabelSystem (evaluate E) S) ↔ b ∈ values E (flat S)
  constructor
  · rintro ⟨q, hq, he⟩
    choose p hp hv using hq
    let C := withLabels S (fun v => withLabels (S.val.graph.label v).2 (p v))
    have ha := E.associative n C (flat C) rfl
    have hl : relabelSystem E.eval C = withLabels (relabelSystem (evaluate E) S) q := by
      change withLabels S (fun v => E.eval _ (withLabels (S.val.graph.label v).2 (p v))) = _
      simp only [hv]
      rfl
    rw [hl] at ha
    refine ⟨fun v => p (vertex (raw S) v).1 (vertex (raw S) v).2,
      fun v => hp (vertex (raw S) v).1 (vertex (raw S) v).2, ?_⟩
    rw [← flat_labels]
    exact ha.symm.trans he
  · rintro ⟨q, hq, he⟩
    obtain ⟨p, hp⟩ := extend_choices (raw S) (fun v => ⟨q v, hq v⟩)
    let qs := fun v u => (p ⟨v, u⟩).val
    let C := withLabels S (fun v => withLabels (S.val.graph.label v).2 (qs v))
    have ha := E.associative n C (flat C) rfl
    refine ⟨fun v => E.eval _ (withLabels (S.val.graph.label v).2 (qs v)),
      fun v => ⟨qs v, fun u => (p ⟨v, u⟩).property, rfl⟩, ?_⟩
    change E.eval n (relabelSystem E.eval C) = b
    rw [ha]
    have hf : flat C = withLabels (flat S) q := by
      change flat (withLabels S (fun v => withLabels (S.val.graph.label v).2 (qs v))) = _
      rw [flat_labels]
      congr 1
      funext v
      exact congrArg Subtype.val (hp v)
    rw [hf]
    exact he

/--
---
conclusion: Lax369799.NonemptyPowersets.algebra
---
Choices in flattened systems extend to the removed vertices because each
allowed label set is nonempty. Associativity then follows from the original
algebra's flattening law.
-/
theorem algebra {B : RankedSet} (E : Algebra B) :
    ∃ F : Algebra (Carrier B), F.eval = evaluate E := by
  refine ⟨{
    eval := evaluate E
    isomorphic := fun _ S T h => Subtype.ext (values_iso E S T h)
    unit := unit_value E
    associative := ?_ }, rfl⟩
  intro n S T h
  have ht : T = flat S := Subtype.ext h
  subst T
  exact associative_value E n S

/--
---
conclusion: Lax369799.NonemptyPowersets.finite_carrier
---
Each sort is a subtype of the powerset of a finite sort.
-/
theorem finite_carrier {B : RankedSet} (hB : RankwiseFinite B) : RankwiseFinite (Carrier B) := by
  intro n
  let : Finite (B n) := hB n
  infer_instance

end Lax369799Proofs.NonemptyPowersets
