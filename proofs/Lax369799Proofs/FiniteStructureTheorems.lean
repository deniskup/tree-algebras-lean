import Lax369799.FiniteStructureTheorems
import Lax369799Proofs.FiniteMorphisms

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteStructureTheorems
open Lax369799.RankedSystems (RankedSet Presentation)
open Lax369799.FinitePresentations Lax369799.FiniteMorphisms
open Lax369799.FiniteStructureTheorems
open Lax369799Proofs.Pullbacks (Map)
open Lax369799Proofs.FiniteMorphisms (toEnumeration fromEnumeration)

private theorem morphism_ext {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (f g : Morphism S T) (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

private def identity {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) : Morphism S S where
  toFun := id
  initial := fun _ h => h
  root := fun _ h => h
  label := fun _ => rfl
  edge := by intro v d t h; cases t <;> exact h

private theorem identity_folding {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    Folding (identity S) := by
  refine ⟨⟨?_, ?_, ?_⟩, Function.surjective_id⟩
  · exact fun v h => ⟨v, h, rfl⟩
  · exact fun v h => ⟨v, h, rfl⟩
  · intro v d t ht
    exact ⟨t, ht, by cases t <;> rfl⟩

private def compose {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S T) (g : Morphism T U) : Morphism S U where
  toFun := g.toFun ∘ f.toFun
  initial := fun v h => g.initial _ (f.initial v h)
  root := fun v h => g.root _ (f.root v h)
  label := fun v => (g.label _).trans (f.label v)
  edge := by
    intro v d t h
    have hh := g.edge _ d _ (f.edge v d t h)
    cases t <;> exact hh

private theorem compose_local {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S T) (g : Morphism T U)
    (hf : LocallySurjective f) (hg : LocallySurjective g) : LocallySurjective (compose f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hg.1 w hw
    obtain ⟨u, hu, rfl⟩ := hf.1 v hv
    exact ⟨u, hu, rfl⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hg.2.1 w hw
    obtain ⟨u, hu, rfl⟩ := hf.2.1 v hv
    exact ⟨u, hu, rfl⟩
  · intro v d t ht
    obtain ⟨s, hs, rfl⟩ := hg.2.2 (f.toFun v) d t ht
    obtain ⟨r, hr, rfl⟩ := hf.2.2 v d s hs
    exact ⟨r, hr, by cases r <;> rfl⟩

/--
---
conclusion: Lax369799.FiniteStructureTheorems.composition
---
Local edge lifts compose; global surjectivity composes separately.
-/
theorem composition {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S T) (g : Morphism T U) :
    ∃ h : Morphism S U, h.toFun = g.toFun ∘ f.toFun ∧
      (LocallySurjective f → LocallySurjective g → LocallySurjective h) ∧
      (Folding f → Folding g → Folding h) := by
  refine ⟨compose f g, rfl, compose_local f g, ?_⟩
  exact fun hf hg => ⟨compose_local f g hf.1 hg.1, hg.2.comp hf.2⟩

def Fiber {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) :=
  {p : S.Vertex × T.Vertex // f.toFun p.1 = g.toFun p.2}

private noncomputable instance {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) : Fintype (Fiber f g) := by
  classical
  unfold Fiber
  infer_instance

def graph {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) : Presentation A n (Fiber f g) where
  label := fun v => S.graph.label v.val.1
  initial := fun v => S.graph.initial v.val.1 ∧ T.graph.initial v.val.2
  root := fun v => S.graph.root v.val.1 ∧ T.graph.root v.val.2
  edge := fun v d t =>
    S.graph.edge v.val.1 d (Sum.map (fun w => w.val.1) id t) ∧
    T.graph.edge v.val.2 d (Sum.map (fun w => w.val.2) id t)
  direction_valid := fun _ _ _ h => S.graph.direction_valid _ _ _ h.1

def first {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) : Map (graph f g) S.graph where
  toFun := fun v => v.val.1
  initial := fun _ h => h.1
  root := fun _ h => h.1
  label := fun _ => rfl
  edge := fun _ _ _ h => h.1

def second {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) : Map (graph f g) T.graph where
  toFun := fun v => v.val.2
  initial := fun _ h => h.2
  root := fun _ h => h.2
  label := by
    intro v
    exact (g.label v.val.2).symm.trans ((congrArg U.graph.label v.property.symm).trans (f.label v.val.1))
  edge := fun _ _ _ h => h.2

def pair {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) (V : FiniteSystem A n)
    (a : Morphism V S) (b : Morphism V T)
    (h : f.toFun ∘ a.toFun = g.toFun ∘ b.toFun) : Map V.graph (graph f g) where
  toFun := fun v => ⟨(a.toFun v, b.toFun v), congrFun h v⟩
  initial := fun v hv => ⟨a.initial v hv, b.initial v hv⟩
  root := fun v hv => ⟨a.root v hv, b.root v hv⟩
  label := fun v => a.label v
  edge := by
    intro v d t ht
    have ha := a.edge v d t ht
    have hb := b.edge v d t ht
    cases t <;> exact ⟨ha, hb⟩

private theorem from_local {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    {G : Presentation A n V} {T : FiniteSystem A n} (f : Map G T.graph)
    (hi : ∀ w, T.graph.initial w → ∃ v, G.initial v ∧ f.toFun v = w)
    (hr : ∀ w, T.graph.root w → ∃ v, G.root v ∧ f.toFun v = w)
    (he : ∀ v d t, T.graph.edge (f.toFun v) d t →
      ∃ s, G.edge v d s ∧ Sum.map f.toFun id s = t) :
    LocallySurjective (fromEnumeration f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, h⟩ := hi w hw
    exact ⟨Fintype.equivFin V v, by simpa [enumerate, reindex] using hv,
      by simpa [fromEnumeration] using h⟩
  · intro w hw
    obtain ⟨v, hv, h⟩ := hr w hw
    exact ⟨Fintype.equivFin V v, by simpa [enumerate, reindex] using hv,
      by simpa [fromEnumeration] using h⟩
  · intro v d t ht
    obtain ⟨s, hs, h⟩ := he ((Fintype.equivFin V).symm v) d t ht
    refine ⟨Sum.map (Fintype.equivFin V) id s, ?_, ?_⟩
    · cases s <;> simpa [enumerate, reindex] using hs
    · cases s <;> simpa [fromEnumeration] using h

private theorem second_local {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) (hf : LocallySurjective f) :
    LocallySurjective (fromEnumeration (second f g)) := by
  apply from_local
  · intro w hw
    obtain ⟨v, hv, he⟩ := hf.1 _ (g.initial w hw)
    exact ⟨⟨(v, w), he⟩, ⟨hv, hw⟩, rfl⟩
  · intro w hw
    obtain ⟨v, hv, he⟩ := hf.2.1 _ (g.root w hw)
    exact ⟨⟨(v, w), he⟩, ⟨hv, hw⟩, rfl⟩
  · intro v d t ht
    have hg := g.edge v.val.2 d t ht
    rw [← v.property] at hg
    obtain ⟨s, hs, he⟩ := hf.2.2 v.val.1 d _ hg
    cases t with
    | inl w =>
      cases s with
      | inl u => exact ⟨.inl ⟨(u, w), Sum.inl.inj he⟩, ⟨hs, ht⟩, rfl⟩
      | inr i => cases he
    | inr i =>
      cases s with
      | inl u => cases he
      | inr j =>
        have hj : j = i := Sum.inr.inj he
        subst j
        exact ⟨.inr i, ⟨hs, ht⟩, rfl⟩

private theorem first_local {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) (hg : LocallySurjective g) :
    LocallySurjective (fromEnumeration (first f g)) := by
  apply from_local
  · intro v hv
    obtain ⟨w, hw, he⟩ := hg.1 _ (f.initial v hv)
    exact ⟨⟨(v, w), he.symm⟩, ⟨hv, hw⟩, rfl⟩
  · intro v hv
    obtain ⟨w, hw, he⟩ := hg.2.1 _ (f.root v hv)
    exact ⟨⟨(v, w), he.symm⟩, ⟨hv, hw⟩, rfl⟩
  · intro v d t ht
    have hf := f.edge v.val.1 d t ht
    rw [v.property] at hf
    obtain ⟨s, hs, he⟩ := hg.2.2 v.val.2 d _ hf
    cases t with
    | inl w =>
      cases s with
      | inl u => exact ⟨.inl ⟨(w, u), (Sum.inl.inj he).symm⟩, ⟨ht, hs⟩, rfl⟩
      | inr i => cases he
    | inr i =>
      cases s with
      | inl u => cases he
      | inr j =>
        have hj : j = i := Sum.inr.inj he
        subst j
        exact ⟨.inr i, ⟨ht, hs⟩, rfl⟩

/--
---
conclusion: Lax369799.FiniteStructureTheorems.pullback
---
Take the entire fiber product with componentwise marks and transitions.
Enumeration retains unreachable vertices. Pairing vertex maps proves the
universal property, and global surjectivity lifts all vertices separately.
-/
theorem pullback {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) :
    ∃ (P : FiniteSystem A n) (p : Morphism P S) (q : Morphism P T),
      f.toFun ∘ p.toFun = g.toFun ∘ q.toFun ∧
      (∀ (V : FiniteSystem A n) (a : Morphism V S) (b : Morphism V T),
        f.toFun ∘ a.toFun = g.toFun ∘ b.toFun →
        ∃! h : Morphism V P, p.toFun ∘ h.toFun = a.toFun ∧ q.toFun ∘ h.toFun = b.toFun) ∧
      (LocallySurjective f → LocallySurjective q) ∧
      (LocallySurjective g → LocallySurjective p) ∧
      (Folding f → Folding q) ∧ (Folding g → Folding p) := by
  classical
  refine ⟨enumerate (graph f g), fromEnumeration (first f g), fromEnumeration (second f g),
    ?_, ?_, second_local f g, first_local f g, ?_, ?_⟩
  · funext v
    exact ((Fintype.equivFin (Fiber f g)).symm v).property
  · intro V a b hab
    refine ⟨toEnumeration (pair f g V a b hab), ⟨?_, ?_⟩, ?_⟩
    · funext v
      simp [fromEnumeration, toEnumeration, first, pair]
    · funext v
      simp [fromEnumeration, toEnumeration, second, pair]
    · intro h ⟨hp, hq⟩
      apply morphism_ext
      funext v
      apply (Fintype.equivFin (Fiber f g)).symm.injective
      apply Subtype.ext
      apply Prod.ext
      · simpa [fromEnumeration, toEnumeration, first, pair] using congrFun hp v
      · simpa [fromEnumeration, toEnumeration, second, pair] using congrFun hq v
  · intro hf
    refine ⟨second_local f g hf.1, ?_⟩
    intro w
    obtain ⟨v, h⟩ := hf.2 (g.toFun w)
    exact ⟨Fintype.equivFin (Fiber f g) ⟨(v, w), h⟩,
      by simp [fromEnumeration, second]⟩
  · intro hg
    refine ⟨first_local f g hg.1, ?_⟩
    intro v
    obtain ⟨w, h⟩ := hg.2 (f.toFun v)
    exact ⟨Fintype.equivFin (Fiber f g) ⟨(v, w), h.symm⟩,
      by simp [fromEnumeration, first]⟩

/--
---
conclusion: Lax369799.FiniteStructureTheorems.unfold_equivalence
---
Pull back the two foldings to the middle presentation and compose with
the remaining foldings. Identity and exchange give the other two laws.
-/
theorem unfold_equivalence (A : RankedSet) (n : ℕ) :
    Equivalence (@UnfoldEquivalent A n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    exact ⟨S, identity S, identity S, identity_folding S, identity_folding S⟩
  · rintro S T ⟨U, f, g, hf, hg⟩
    exact ⟨U, g, f, hg, hf⟩
  · rintro S T U ⟨P, pS, pT, hpS, hpT⟩ ⟨Q, qT, qU, hqT, hqU⟩
    obtain ⟨R, rP, rQ, _, _, _, _, hQ, hP⟩ := pullback pT qT
    obtain ⟨s, _, _, hs⟩ := composition rP pS
    obtain ⟨u, _, _, hu⟩ := composition rQ qU
    exact ⟨R, s, u, hs (hP hqT) hpS, hu (hQ hpT) hqU⟩

end Lax369799Proofs.FiniteStructureTheorems
