import Lax369799.RankedLifting
import Mathlib.Data.Fintype.Prod

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.RankedLifting
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.TransitionSystems
open Lax369799.TransitionEncoding Lax369799.BisimulationQuotient

private noncomputable def encode {P : Type} (S : TransitionSystem P)
    (D : S.Vertex → Type) [∀ v, Fintype (D v)] (next : ∀ v, D v → S.Vertex)
    (_hnext : ∀ v d, S.edge v (next v d))
    (honto : ∀ v w, S.edge v w → ∃ d, next v d = w) : System (TransitionAlphabet P) 0 := by
  classical
  let e := fun v => Fintype.equivFin (D v)
  let G : Presentation (TransitionAlphabet P) 0 S.Vertex := {
    label := fun v => ⟨Fintype.card (D v), S.valuation v⟩
    initial := {S.initial}
    root := ∅
    edge := fun v d t => ∃ i : D v, d = (e v i).val ∧ t = .inl (next v i)
    direction_valid := by rintro v d t ⟨i, rfl, rfl⟩; exact (e v i).isLt }
  refine ⟨⟨S.size, G, ?_⟩, ⟨S.initial, rfl⟩, rfl, ?_⟩
  · intro v
    refine ⟨S.initial, Or.inl rfl, Relation.ReflTransGen.mono ?_ _ _ (S.reachable v)⟩
    intro x y h
    obtain ⟨i, rfl⟩ := honto x y h
    exact ⟨(e x i).val, i, rfl, rfl⟩
  · intro v d hd
    let i := (e v).symm ⟨d, hd⟩
    refine ⟨.inl (next v i), ⟨i, by simp [i], rfl⟩, ?_⟩
    rintro t ⟨j, hj, rfl⟩
    have he : e v j = (⟨d, hd⟩ : Fin (Fintype.card (D v))) := Fin.ext hj.symm
    have hij : j = i := (e v).injective (he.trans (by simp [i]))
    rw [hij]

private theorem decode_encode {P : Type} (S : TransitionSystem P)
    (D : S.Vertex → Type) [∀ v, Fintype (D v)] (next : ∀ v, D v → S.Vertex)
    (hnext : ∀ v d, S.edge v (next v d))
    (honto : ∀ v w, S.edge v w → ∃ d, next v d = w) :
    decode (encode S D next hnext honto) = S := by
  classical
  have hi : (decode (encode S D next hnext honto)).initial = S.initial := by
    have h := Classical.choose_spec (encode S D next hnext honto).property.1
    change ({S.initial} : Set S.Vertex) = {Classical.choose (encode S D next hnext honto).property.1} at h
    exact (Set.singleton_injective h).symm
  have he : (decode (encode S D next hnext honto)).edge = S.edge := by
    funext v w
    apply propext
    change (∃ d, ∃ i : D v, d = (Fintype.equivFin (D v) i).val ∧
      Sum.inl w = Sum.inl (next v i)) ↔ _
    constructor
    · rintro ⟨d, i, _, h⟩
      exact (Sum.inl.inj h).symm ▸ hnext v i
    · intro h
      obtain ⟨i, rfl⟩ := honto v w h
      exact ⟨_, i, rfl, rfl⟩
  cases S
  unfold decode
  congr 1

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

/--
---
conclusion: Lax369799.RankedLifting.map_lift
---
At a target vertex, enumerate each successor together with a copy index
bounded by the source size. For each source vertex, map these copies onto
all its successors lying over that target successor. The resulting two
rankings have identical direction sets along the given functional map.
-/
theorem map_lift {P : Type} (S T : TransitionSystem P) (f : SystemMap S T) :
    ∃ (R U : System (TransitionAlphabet P) 0), decode R = S ∧ decode U = T ∧
      Nonempty (Morphism R.val U.val) := by
  classical
  let N := fun v : T.Vertex => {w : T.Vertex // T.edge v w}
  let D := fun v : T.Vertex => N v × Fin S.size
  let F := fun (v : S.Vertex) (w : N (f.toFun v)) =>
    {u : S.Vertex // S.edge v u ∧ f.toFun u = w.val}
  have hF (v : S.Vertex) (w : N (f.toFun v)) : Nonempty (F v w) := by
    obtain ⟨u, hu, he⟩ := f.backward v w.val w.property
    exact ⟨u, hu, he⟩
  have hcard (v : S.Vertex) (w : N (f.toFun v)) : Fintype.card (F v w) ≤ S.size := by
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin S.size)
  have hex (v : S.Vertex) (w : N (f.toFun v)) : ∃ g : Fin S.size → F v w, Function.Surjective g := by
    let : Nonempty (F v w) := hF v w
    exact finite_onto S.size (hcard v w)
  choose g hg using hex
  let nextS := fun (v : S.Vertex) (d : D (f.toFun v)) => (g v d.1 d.2).val
  let nextT := fun (_v : T.Vertex) (d : D _v) => d.1.val
  have hs (v) (d : D (f.toFun v)) : S.edge v (nextS v d) := (g v d.1 d.2).property.1
  have ht (v) (d : D v) : T.edge v (nextT v d) := d.1.property
  have hsonto (v w) (hw : S.edge v w) : ∃ d, nextS v d = w := by
    let u : N (f.toFun v) := ⟨f.toFun w, f.forward v w hw⟩
    obtain ⟨i, hi⟩ := hg v u ⟨w, hw, rfl⟩
    exact ⟨(u, i), congrArg Subtype.val hi⟩
  have htonto (v w) (hw : T.edge v w) : ∃ d, nextT v d = w :=
    ⟨(⟨w, hw⟩, S.initial), rfl⟩
  let R := encode S (fun v => D (f.toFun v)) nextS hs hsonto
  let U := encode T D nextT ht htonto
  refine ⟨R, U, decode_encode S _ _ _ _, decode_encode T _ _ _ _, ⟨?_⟩⟩
  refine {
    toFun := f.toFun
    initial := ?_
    root := fun _ h => False.elim h
    label := ?_
    edge := ?_ }
  · intro v hv
    change v = S.initial at hv
    subst v
    exact f.initial
  · intro v
    exact congrArg (Sigma.mk (Fintype.card (D (f.toFun v)))) (f.valuation v).symm
  · rintro v d t ⟨i, hd, he⟩
    refine ⟨i, hd, ?_⟩
    rw [he]
    exact congrArg Sum.inl (g v i.1 i.2).property.2

end Lax369799Proofs.RankedLifting
