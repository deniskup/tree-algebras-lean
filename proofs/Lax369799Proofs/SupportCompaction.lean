import Lax369799.SupportCompaction
import Lax369799Proofs.SupportedSystems
import Lax369799Proofs.Renaming

namespace Lax369799Proofs.SupportCompaction
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems Renaming Resolutions

private theorem graph_ext {A : RankedSet} {n : ℕ} {V : Type}
    (G H : Presentation A n V) (hl : G.label = H.label) (hi : G.initial = H.initial)
    (hr : G.root = H.root) (he : G.edge = H.edge) : G = H := by
  cases G
  cases H
  cases hl
  cases hi
  cases hr
  cases he
  rfl

private theorem system_ext {A : RankedSet} {n : ℕ} (S T : SetSystem A n)
    (hs : S.size = T.size) (hg : HEq S.graph T.graph) : S = T := by
  cases S
  cases T
  cases hs
  cases hg
  rfl

/--
---
conclusion: Lax369799.SupportCompaction.compact_exists
---
Enumerate exactly the output indices occurring on an edge. Pull back
variable targets along this enumeration. The vertex graph is unchanged,
so reachability and deterministic successors are preserved.
-/
theorem compact_exists {A : RankedSet} {n : ℕ} (S : RankedSystems.System A n) :
    ∃ (m : ℕ) (σ : Fin m → Fin n) (T : SupportedSystems.System A m),
      Function.Injective σ ∧ renameSystem σ T.val = S := by
  classical
  let W := {i : Fin n // ∃ v d, S.val.graph.edge v d (.inr i)}
  let e := Fintype.equivFin W
  let σ : Fin (Fintype.card W) → Fin n := fun i => (e.symm i).val
  have hσ : Function.Injective σ := fun i j h => e.symm.injective (Subtype.ext h)
  let G : Presentation A (Fintype.card W) S.val.Vertex := {
    label := S.val.graph.label
    initial := S.val.graph.initial
    root := S.val.graph.root
    edge := fun v d t => S.val.graph.edge v d (Sum.map id σ t)
    direction_valid := fun v d t h => S.val.graph.direction_valid v d _ h }
  have hreach : ∀ v, G.Reachable v := by
    intro v
    obtain ⟨r, hr, hp⟩ := S.val.reachable v
    exact ⟨r, hr, Relation.ReflTransGen.mono (fun _ _ ⟨d, hd⟩ => ⟨d, hd⟩) _ _ hp⟩
  have hpre : ∀ v d t, S.val.graph.edge v d t →
      ∃ u, G.edge v d u ∧ Sum.map id σ u = t := by
    intro v d t ht
    cases t with
    | inl w => exact ⟨.inl w, ht, rfl⟩
    | inr i =>
      let j := e ⟨i, v, d, ht⟩
      have hj : σ j = i := by simp [σ, j]
      refine ⟨.inr j, ?_, congrArg Sum.inr hj⟩
      change S.val.graph.edge v d (.inr (σ j))
      rw [hj]
      exact ht
  have hinj : Function.Injective (Sum.map (id : S.val.Vertex → S.val.Vertex) σ) := by
    intro x y h
    cases x <;> cases y <;> simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq] at h ⊢
    · exact h
    · exact hσ h
  let U : RankedSystems.System A (Fintype.card W) :=
    ⟨⟨S.val.size, G, hreach⟩, S.property.1, S.property.2.1, by
      intro v d hd
      obtain ⟨t, ht, hu⟩ := S.property.2.2 v d hd
      obtain ⟨u, he, hm⟩ := hpre v d t ht
      refine ⟨u, he, ?_⟩
      intro u' hu'
      exact hinj ((hu _ hu').trans hm.symm)⟩
  have hsupport : SupportedSystems.FullySupported U := fun i => (e.symm i).property
  refine ⟨Fintype.card W, σ, ⟨U, hsupport⟩, hσ, ?_⟩
  have he : (renameSystem σ U).val.graph.edge = S.val.graph.edge := by
    funext v d t
    apply propext
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro ht
      obtain ⟨u, hu, he⟩ := hpre v d t ht
      exact ⟨u, hu, he.symm⟩
  apply Subtype.ext
  have hg : (renameSystem σ U).val.graph = S.val.graph := graph_ext _ _ rfl rfl rfl he
  exact system_ext _ _ rfl (heq_of_eq hg)

/--
---
conclusion: Lax369799.SupportCompaction.rename_supported_iff
---
Every old variable occurs, so the new output support is exactly the
image of the variable map.
-/
theorem rename_supported_iff {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (T : SupportedSystems.System A m) :
    SupportedSystems.FullySupported (renameSystem σ T.val) ↔ Function.Surjective σ := by
  constructor
  · intro h j
    obtain ⟨v, d, t, ht, he⟩ := h j
    cases t with
    | inl w => cases he
    | inr i => exact ⟨i, (Sum.inr.inj he).symm⟩
  · intro h j
    obtain ⟨i, rfl⟩ := h j
    obtain ⟨v, d, hd⟩ := T.property i
    exact ⟨v, d, .inr i, hd, rfl⟩

/--
---
conclusion: Lax369799.SupportCompaction.rename_set_injective
---
-/
theorem rename_set_injective {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) : Function.Injective (@Resolutions.rename A m n σ) := by
  intro S T h
  cases S with | mk ss sg sr =>
    cases T with | mk ts tg tr =>
      have hs : ss = ts := congrArg SetSystem.size h
      subst ts
      have hg : (Resolutions.rename σ ⟨ss, sg, sr⟩).graph =
          (Resolutions.rename σ ⟨ss, tg, tr⟩).graph :=
        eq_of_heq (SetSystem.mk.inj h).2
      have hl : sg.label = tg.label := congrArg (fun G : Presentation A n (Fin ss) => G.label) hg
      have hi : sg.initial = tg.initial := congrArg (fun G : Presentation A n (Fin ss) => G.initial) hg
      have hr : sg.root = tg.root := congrArg (fun G : Presentation A n (Fin ss) => G.root) hg
      have he : sg.edge = tg.edge := by
        funext v d t
        apply propext
        have hem := congrArg (fun G => G.edge v d (Sum.map id σ t)) hg
        constructor
        · intro ht
          have hx : (Resolutions.rename σ ⟨ss, sg, sr⟩).graph.edge v d (Sum.map id σ t) :=
            ⟨t, ht, rfl⟩
          rw [hem] at hx
          obtain ⟨u, hu, htu⟩ := hx
          have hmap : Function.Injective (Sum.map (id : Fin ss → Fin ss) σ) := by
            intro x y hxy
            cases x <;> cases y <;> simp_all
            exact hσ hxy
          exact hmap htu ▸ hu
        · intro ht
          have hx : (Resolutions.rename σ ⟨ss, tg, tr⟩).graph.edge v d (Sum.map id σ t) :=
            ⟨t, ht, rfl⟩
          rw [← hem] at hx
          obtain ⟨u, hu, htu⟩ := hx
          have hmap : Function.Injective (Sum.map (id : Fin ss → Fin ss) σ) := by
            intro x y hxy
            cases x <;> cases y <;> simp_all
            exact hσ hxy
          exact hmap htu ▸ hu
      have hgraph : sg = tg := by
        cases sg
        cases tg
        cases hl
        cases hi
        cases hr
        cases he
        rfl
      cases hgraph
      rfl

/--
---
conclusion: Lax369799.SupportCompaction.rename_system_injective
---
-/
theorem rename_system_injective {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) : Function.Injective (@renameSystem A m n σ) := by
  intro S T h
  apply Subtype.ext
  exact rename_set_injective σ hσ (congrArg Subtype.val h)

/--
---
conclusion: Lax369799.SupportCompaction.support_image
---
-/
theorem support_image {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (T : SupportedSystems.System A m) (j : Fin n) :
    (∃ v d, (renameSystem σ T.val).val.graph.edge v d (.inr j)) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨v, d, t, ht, he⟩
    cases t with
    | inl w => cases he
    | inr i => exact ⟨i, (Sum.inr.inj he).symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨v, d, hd⟩ := T.property i
    exact ⟨v, d, .inr i, hd, rfl⟩

/--
---
conclusion: Lax369799.SupportCompaction.compact_unique
---
-/
theorem compact_unique {A : RankedSet} {m k n : ℕ}
    (σ : Fin m → Fin n) (τ : Fin k → Fin n)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (S : SupportedSystems.System A m) (T : SupportedSystems.System A k)
    (h : renameSystem σ S.val = renameSystem τ T.val) :
    ∃ e : Fin m ≃ Fin k, (∀ i, τ (e i) = σ i) ∧ renameSystem e S.val = T.val := by
  classical
  have himage : Set.range σ = Set.range τ := by
    ext j
    rw [← support_image σ S j, ← support_image τ T j, h]
  have hg : ∀ i, ∃ j, τ j = σ i := fun i =>
    (Set.ext_iff.mp himage (σ i)).mp (Set.mem_range_self i)
  choose g hg using hg
  have hginj : Function.Injective g := by
    intro i j hij
    apply hσ
    rw [← hg i, ← hg j, hij]
  have hgsurj : Function.Surjective g := by
    intro j
    obtain ⟨i, hi⟩ := (Set.ext_iff.mp himage (τ j)).mpr (Set.mem_range_self j)
    exact ⟨i, hτ ((hg i).trans hi)⟩
  let e : Fin m ≃ Fin k := Equiv.ofBijective g ⟨hginj, hgsurj⟩
  refine ⟨e, hg, rename_system_injective τ hτ ?_⟩
  have hc : renameSystem τ (renameSystem e S.val) = renameSystem σ S.val := by
    apply Subtype.ext
    change Resolutions.rename τ (Resolutions.rename e S.val.val) = _
    rw [Lax369799Proofs.Renaming.rename_composition]
    have he : τ ∘ e = σ := funext hg
    rw [he]
    rfl
  exact hc.trans h

end Lax369799Proofs.SupportCompaction
