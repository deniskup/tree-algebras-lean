import Lax369799.FinitePresentations
import Mathlib.Logic.Equiv.Defs
import Lax369799Proofs.Pullbacks

namespace Lax369799Proofs.UntrimmedFlattening
open Lax369799.RankedSystems (RankedSet RankedMap Symbol Presentation)
open Lax369799.FinitePresentations

/-- Substitution before choosing enumerations of the finite vertex sets. -/
def substitute {A B : RankedSet} {n : ℕ} {V : Type} {W : V → Type}
    (P : Presentation B n V) (Q : ∀ v, Presentation A (P.label v).1 (W v)) :
    Presentation A n ((v : V) × W v) where
  label := fun v => (Q v.1).label v.2
  initial := fun v => P.initial v.1 ∧ (Q v.1).initial v.2
  root := fun v => (Q v.1).root v.2 ∨ (P.root v.1 ∧ (Q v.1).initial v.2)
  edge := fun v d t =>
    (∃ w, (Q v.1).edge v.2 d (.inl w) ∧ t = .inl ⟨v.1, w⟩) ∨
    (∃ i : Fin (P.label v.1).1, (Q v.1).edge v.2 d (.inr i) ∧
      ((∃ w : (v : V) × W v, P.edge v.1 i.val (.inl w.1) ∧
        (Q w.1).initial w.2 ∧ t = .inl w) ∨
       (∃ j, P.edge v.1 i.val (.inr j) ∧ t = .inr j)))
  direction_valid := by
    intro v d t h
    rcases h with ⟨w, hw, _⟩ | ⟨i, hi, _⟩
    · exact (Q v.1).direction_valid _ d _ hw
    · exact (Q v.1).direction_valid _ d _ hi

def substituteAssoc {A B C : RankedSet} {n : ℕ} {V : Type}
    {W : V → Type} {X : ∀ v, W v → Type}
    (P : Presentation C n V) (Q : ∀ v, Presentation B (P.label v).1 (W v))
    (R : ∀ v w, Presentation A ((Q v).label w).1 (X v w)) :
    PresentationIso (substitute (substitute P Q) (fun v => R v.1 v.2))
      (substitute P (fun v => substitute (Q v) (R v))) where
  vertex := Equiv.sigmaAssoc X
  label := fun _ => rfl
  initial := by rintro ⟨⟨v, w⟩, u⟩; exact and_assoc.symm
  root := by
    rintro ⟨⟨v, w⟩, u⟩
    change (_ ∨ (_ ∧ _)) ∨ (_ ∧ _ ∧ _) ↔ _ ∨ ((_ ∨ (_ ∧ _)) ∧ _)
    tauto
  edge := by
    rintro ⟨⟨v, w⟩, u⟩ d t
    constructor
    · intro h
      rcases h with ⟨z, hz, he⟩ | ⟨i, hi, h⟩
      · rcases hz with ⟨u', hu', he'⟩ | ⟨j, hj, h⟩
        · have hz := Sum.inl.inj he'
          subst z
          have ht : t = .inl ⟨⟨v, w⟩, u'⟩ := by
            apply (Equiv.sumCongr (Equiv.sigmaAssoc X) (Equiv.refl _)).injective
            exact he
          subst t
          exact Or.inl ⟨u', hu', rfl⟩
        · rcases h with ⟨z', hq, hr, he'⟩ | ⟨j', _, he'⟩
          · have hz := Sum.inl.inj he'
            subst z
            have ht : t = .inl ⟨⟨v, z'.1⟩, z'.2⟩ := by
              apply (Equiv.sumCongr (Equiv.sigmaAssoc X) (Equiv.refl _)).injective
              exact he
            subst t
            exact Or.inr ⟨j, hj, Or.inl ⟨⟨⟨v, z'.1⟩, z'.2⟩,
              Or.inl ⟨z'.1, hq, rfl⟩, hr, rfl⟩⟩
          · cases he'
      · rcases hi with ⟨u', _, he⟩ | ⟨j, hj, hq⟩
        · cases he
        · rcases hq with ⟨w', _, _, he⟩ | ⟨i', hqi, he⟩
          · cases he
          · have hii := Sum.inr.inj he
            subst i'
            rcases h with ⟨z, hp, hz, he⟩ | ⟨l, hp, he⟩
            · have ht : t = .inl ⟨⟨z.1, z.2.1⟩, z.2.2⟩ := by
                apply (Equiv.sumCongr (Equiv.sigmaAssoc X) (Equiv.refl _)).injective
                exact he
              subst t
              exact Or.inr ⟨j, hj, Or.inl ⟨⟨⟨z.1, z.2.1⟩, z.2.2⟩,
                Or.inr ⟨i, hqi, Or.inl ⟨⟨z.1, z.2.1⟩, hp, hz.1, rfl⟩⟩, hz.2, rfl⟩⟩
            · have ht : t = .inr l := by
                apply (Equiv.sumCongr (Equiv.sigmaAssoc X) (Equiv.refl _)).injective
                exact he
              subst t
              exact Or.inr ⟨j, hj, Or.inr ⟨l, Or.inr ⟨i, hqi, Or.inr ⟨l, hp, rfl⟩⟩, rfl⟩⟩
    · intro h
      rcases h with ⟨u', hu, rfl⟩ | ⟨j, hj, h⟩
      · exact Or.inl ⟨⟨w, u'⟩, Or.inl ⟨u', hu, rfl⟩, rfl⟩
      · rcases h with ⟨z, hq, hz, rfl⟩ | ⟨l, hq, rfl⟩
        · rcases hq with ⟨w', hw, he⟩ | ⟨i, hi, h⟩
          · have hz' := Sum.inl.inj he
            cases z with
            | mk z u' =>
              dsimp only at hz'
              subst z
              exact Or.inl ⟨⟨w', u'⟩, Or.inr ⟨j, hj, Or.inl ⟨⟨w', u'⟩, hw, hz, rfl⟩⟩, rfl⟩
          · rcases h with ⟨z', hp, hq, he⟩ | ⟨l, _, he⟩
            · have hz' := Sum.inl.inj he
              cases z with
              | mk z u' =>
                dsimp only at hz'
                subst z
                exact Or.inr ⟨i, Or.inr ⟨j, hj, Or.inr ⟨i, hi, rfl⟩⟩,
                  Or.inl ⟨⟨z'.1, ⟨z'.2, u'⟩⟩, hp, ⟨hq, hz⟩, rfl⟩⟩
            · cases he
        · rcases hq with ⟨w', _, he⟩ | ⟨i, hi, h⟩
          · cases he
          · rcases h with ⟨z, _, _, he⟩ | ⟨l', hp, he⟩
            · cases he
            · have hl := Sum.inr.inj he
              subst l'
              exact Or.inr ⟨i, Or.inr ⟨j, hj, Or.inr ⟨i, hi, rfl⟩⟩,
                Or.inr ⟨l, hp, rfl⟩⟩

def isoSymm {A : RankedSet} {n : ℕ} {V W : Type}
    {G : Presentation A n V} {H : Presentation A n W}
    (f : PresentationIso G H) : PresentationIso H G where
  vertex := f.vertex.symm
  label := by intro w; simpa using (f.label (f.vertex.symm w)).symm
  initial := by intro w; simpa using (f.initial (f.vertex.symm w)).symm
  root := by intro w; simpa using (f.root (f.vertex.symm w)).symm
  edge := by
    intro w d t
    have h := (f.edge (f.vertex.symm w) d (Sum.map f.vertex.symm id t)).symm
    cases t <;> simpa using h

def isoTrans {A : RankedSet} {n : ℕ} {V W X : Type}
    {G : Presentation A n V} {H : Presentation A n W} {K : Presentation A n X}
    (f : PresentationIso G H) (g : PresentationIso H K) : PresentationIso G K where
  vertex := f.vertex.trans g.vertex
  label := fun v => (g.label _).trans (f.label v)
  initial := fun v => (g.initial _).trans (f.initial v)
  root := fun v => (g.root _).trans (f.root v)
  edge := by
    intro v d t
    have h := (g.edge (f.vertex v) d (Sum.map f.vertex id t)).trans (f.edge v d t)
    cases t <;> exact h

def reindexIso {A : RankedSet} {n : ℕ} {V W : Type}
    (G : Presentation A n V) (e : V ≃ W) : PresentationIso G (reindex G e) where
  vertex := e
  label := by intro v; exact congrArg G.label (e.symm_apply_apply v)
  initial := by intro v; change G.initial (e.symm (e v)) ↔ _; rw [e.symm_apply_apply]
  root := by intro v; change G.root (e.symm (e v)) ↔ _; rw [e.symm_apply_apply]
  edge := by
    intro v d t
    change G.edge (e.symm (e v)) d (Sum.map e.symm id (Sum.map e id t)) ↔ _
    cases t <;> simp

def substituteMap {A B : RankedSet} {n : ℕ} {V : Type} {W X : V → Type}
    (P : Presentation B n V) (Q : ∀ v, Presentation A (P.label v).1 (W v))
    (R : ∀ v, Presentation A (P.label v).1 (X v))
    (f : ∀ v, Pullbacks.Map (Q v) (R v)) : Pullbacks.Map (substitute P Q) (substitute P R) where
  toFun := fun v => ⟨v.1, (f v.1).toFun v.2⟩
  label := fun v => (f v.1).label v.2
  initial := fun v h => ⟨h.1, (f v.1).initial v.2 h.2⟩
  root := fun v h => h.elim (fun h => Or.inl ((f v.1).root v.2 h))
    (fun h => Or.inr ⟨h.1, (f v.1).initial v.2 h.2⟩)
  edge := by
    intro v d t h
    rcases h with ⟨w, hw, rfl⟩ | ⟨i, hi, h⟩
    · exact Or.inl ⟨(f v.1).toFun w, (f v.1).edge v.2 d (.inl w) hw, rfl⟩
    · rcases h with ⟨w, hw, hi', rfl⟩ | ⟨j, hj, rfl⟩
      · exact Or.inr ⟨i, (f v.1).edge v.2 d (.inr i) hi,
          Or.inl ⟨⟨w.1, (f w.1).toFun w.2⟩, hw, (f w.1).initial w.2 hi', rfl⟩⟩
      · exact Or.inr ⟨i, (f v.1).edge v.2 d (.inr i) hi, Or.inr ⟨j, hj, rfl⟩⟩

def isoMap {A : RankedSet} {n : ℕ} {V W : Type}
    {G : Presentation A n V} {H : Presentation A n W}
    (f : PresentationIso G H) : Pullbacks.Map G H :=
  ⟨f.vertex, fun v => (f.initial v).mpr, fun v => (f.root v).mpr,
    f.label, fun v d t => (f.edge v d t).mpr⟩

def substituteInnerIso {A B : RankedSet} {n : ℕ} {V : Type} {W X : V → Type}
    (P : Presentation B n V) (Q : ∀ v, Presentation A (P.label v).1 (W v))
    (R : ∀ v, Presentation A (P.label v).1 (X v))
    (f : ∀ v, PresentationIso (Q v) (R v)) : PresentationIso (substitute P Q) (substitute P R) where
  vertex := Equiv.sigmaCongrRight (fun v => (f v).vertex)
  label := fun v => (f v.1).label v.2
  initial := fun v => and_congr_right (fun _ => (f v.1).initial v.2)
  root := fun v => or_congr ((f v.1).root v.2)
    (and_congr_right (fun _ => (f v.1).initial v.2))
  edge := by
    intro v d t
    constructor
    · intro h
      have h' := (substituteMap P R Q (fun v => isoMap (isoSymm (f v)))).edge _ d _ h
      cases v with
      | mk v u =>
        cases t with
        | inl w =>
          cases w with
          | mk w z =>
            change (substitute P Q).edge ⟨v, (f v).vertex.symm ((f v).vertex u)⟩ d
              (.inl ⟨w, (f w).vertex.symm ((f w).vertex z)⟩) at h'
            simpa using h'
        | inr i =>
          change (substitute P Q).edge ⟨v, (f v).vertex.symm ((f v).vertex u)⟩ d (.inr i) at h'
          simpa using h'
    · exact (substituteMap P Q R (fun v => isoMap (f v))).edge v d t

def substituteOuterReindex {A B : RankedSet} {n : ℕ} {V V' : Type} {W : V → Type}
    (P : Presentation B n V) (Q : ∀ v, Presentation A (P.label v).1 (W v)) (e : V ≃ V') :
    PresentationIso (substitute (reindex P e) (fun v => Q (e.symm v))) (substitute P Q) where
  vertex := Equiv.sigmaCongrLeft e.symm
  label := fun _ => rfl
  initial := fun _ => Iff.rfl
  root := fun _ => Iff.rfl
  edge := by
    intro v d t
    let f := Equiv.sigmaCongrLeft (β := W) e.symm
    constructor
    · intro h
      rcases h with ⟨w, hw, he⟩ | ⟨i, hi, h⟩
      · have ht : t = .inl ⟨v.1, w⟩ := by
          apply (Equiv.sumCongr f (Equiv.refl _)).injective
          exact he
        subst t
        exact Or.inl ⟨w, hw, rfl⟩
      · rcases h with ⟨w, hw, hi', he⟩ | ⟨j, hj, he⟩
        · obtain ⟨w, rfl⟩ := f.surjective w
          have ht : t = .inl w := by
            apply (Equiv.sumCongr f (Equiv.refl _)).injective
            exact he
          subst t
          exact Or.inr ⟨i, hi, Or.inl ⟨w, hw, hi', rfl⟩⟩
        · have ht : t = .inr j := by
            apply (Equiv.sumCongr f (Equiv.refl _)).injective
            exact he
          subst t
          exact Or.inr ⟨i, hi, Or.inr ⟨j, hj, rfl⟩⟩
    · intro h
      rcases h with ⟨w, hw, rfl⟩ | ⟨i, hi, h⟩
      · exact Or.inl ⟨w, hw, rfl⟩
      · rcases h with ⟨w, hw, hi', rfl⟩ | ⟨j, hj, rfl⟩
        · exact Or.inr ⟨i, hi, Or.inl ⟨f w, hw, hi', rfl⟩⟩
        · exact Or.inr ⟨i, hi, Or.inr ⟨j, hj, rfl⟩⟩

/--
---
conclusion: Lax369799.FinitePresentations.flatten_associative
---
Keep all vertices at each stage. Reassociate the three vertex coordinates,
then account for the finite enumerations on the two intermediate graphs.
The associator preserves and reflects every mark and transition.
-/
theorem flatten_associative {A : RankedSet} {n : ℕ}
    (S : FiniteSystem (FiniteSystem (FiniteSystem A)) n) :
    Isomorphic (flatten (flatten S)) (flatten (relabel (fun _ T => flatten T) S)) := by
  classical
  let Q := fun v => (Inner S.graph v).graph
  let R := fun v w => (Inner (Q v) w).graph
  let M := substitute S.graph Q
  let e := Fintype.equivFin ((v : S.Vertex) × (Inner S.graph v).Vertex)
  let L := substitute (reindex M e) (fun v => R (e.symm v).1 (e.symm v).2)
  let Z := substitute S.graph (fun v => substitute (Q v) (R v))
  let H := substitute S.graph (fun v => (flatten (Inner S.graph v)).graph)
  let leftEnum := Fintype.equivFin ((v : (flatten S).Vertex) × (Inner (flatten S).graph v).Vertex)
  let rightEnum := Fintype.equivFin ((v : S.Vertex) × (flatten (Inner S.graph v)).Vertex)
  have out : PresentationIso L (substitute M (fun v => R v.1 v.2)) :=
    substituteOuterReindex M (fun v => R v.1 v.2) e
  have assoc : PresentationIso (substitute M (fun v => R v.1 v.2)) Z :=
    substituteAssoc S.graph Q R
  have inside : PresentationIso Z H := substituteInnerIso S.graph _ _
    (fun v => reindexIso (substitute (Q v) (R v))
      (Fintype.equivFin ((w : (Inner S.graph v).Vertex) × (Inner (Q v) w).Vertex)))
  exact ⟨isoTrans (isoSymm (reindexIso L leftEnum))
    (isoTrans out (isoTrans assoc (isoTrans inside (reindexIso H rightEnum))))⟩

private def outerUnitIso {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    PresentationIso (flattenPresentation (Lax369799.FinitePresentations.atomic S).graph) S.graph where
  vertex := {
    toFun := fun v => v.2
    invFun := fun v => ⟨(0 : Fin 1), v⟩
    left_inv := by
      rintro ⟨v, w⟩
      have hv : v = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst v
      rfl
    right_inv := fun _ => rfl }
  label := fun _ => rfl
  initial := by intro v; change S.graph.initial v.2 ↔ True ∧ S.graph.initial v.2; simp
  root := by intro v; change S.graph.root v.2 ↔ S.graph.root v.2 ∨ (False ∧ _); simp
  edge := by
    intro v d t
    constructor
    · intro h
      cases t with
      | inl w =>
        have he : w = ⟨v.1, w.2⟩ := by
          obtain ⟨v, u⟩ := v
          obtain ⟨w, z⟩ := w
          have hv : v = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
          have hw : w = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
          subst v
          subst w
          rfl
        exact Or.inl ⟨w.2, h, congrArg Sum.inl he⟩
      | inr i => exact Or.inr ⟨i, h, Or.inr ⟨i, ⟨i, rfl, rfl⟩, rfl⟩⟩
    · intro h
      rcases h with ⟨w, hw, rfl⟩ | ⟨i, hi, h⟩
      · exact hw
      · rcases h with ⟨w, ⟨j, _, he⟩, _⟩ | ⟨j, ⟨l, hl, he⟩, rfl⟩
        · cases he
        · have hj := Sum.inr.inj he
          have hi' : i = l := Fin.ext hl
          subst j
          subst i
          exact hi

/--
---
conclusion: Lax369799.FinitePresentations.outer_atomic
---
Flattening a single outer atomic vertex leaves its label unchanged, up
to the finite enumeration of its vertices.
-/
theorem outer_atomic {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    Isomorphic (flatten (Lax369799.FinitePresentations.atomic S)) S := by
  classical
  exact ⟨isoTrans (isoSymm (reindexIso _ (Fintype.equivFin _))) (outerUnitIso S)⟩

private def innerUnitIso {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    PresentationIso (flattenPresentation (relabel (fun _ a => Lax369799.FinitePresentations.atomic a) S).graph)
      S.graph where
  vertex := {
    toFun := Sigma.fst
    invFun := fun v => ⟨v, (0 : Fin 1)⟩
    left_inv := by
      rintro ⟨v, w⟩
      have hw : w = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst w
      rfl
    right_inv := fun _ => rfl }
  label := fun _ => rfl
  initial := by intro v; change S.graph.initial v.1 ↔ S.graph.initial v.1 ∧ True; simp
  root := by intro v; change S.graph.root v.1 ↔ False ∨ (S.graph.root v.1 ∧ True); simp
  edge := by
    intro v d t
    constructor
    · intro h
      let i : Fin (S.graph.label v.1).1 := ⟨d, S.graph.direction_valid _ d _ h⟩
      cases t with
      | inl w => exact Or.inr ⟨i, ⟨i, rfl, rfl⟩, Or.inl ⟨w, h, True.intro, rfl⟩⟩
      | inr j => exact Or.inr ⟨i, ⟨i, rfl, rfl⟩, Or.inr ⟨j, h, rfl⟩⟩
    · intro h
      rcases h with ⟨w, ⟨i, _, he⟩, _⟩ | ⟨i, ⟨j, hd, he⟩, h⟩
      · cases he
      · have hij := Sum.inr.inj he
        subst j
        subst d
        rcases h with ⟨w, hw, _, rfl⟩ | ⟨j, hj, rfl⟩ <;> assumption

/--
---
conclusion: Lax369799.FinitePresentations.inner_atomic
---
Each atomic inner component contributes exactly its outer vertex, with
the same marks and successors. Projection is an isomorphism.
-/
theorem inner_atomic {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    Isomorphic (flatten (relabel (fun _ a => Lax369799.FinitePresentations.atomic a) S)) S := by
  classical
  exact ⟨isoTrans (isoSymm (reindexIso _ (Fintype.equivFin _))) (innerUnitIso S)⟩

/--
---
conclusion: Lax369799.FinitePresentations.flatten_natural
---
Relabelling changes neither vertex sets nor marks and transitions, so
both constructions use the same finite enumeration and labelling.
-/
theorem flatten_natural {A B : RankedSet} (f : RankedMap A B) {n : ℕ}
    (S : FiniteSystem (FiniteSystem A) n) :
    relabel f (flatten S) = flatten (relabel (fun _ T => relabel f T) S) := rfl

def isoRefl {A : RankedSet} {n : ℕ} {V : Type} (G : Presentation A n V) :
    PresentationIso G G where
  vertex := Equiv.refl _
  label := fun _ => rfl
  initial := fun _ => Iff.rfl
  root := fun _ => Iff.rfl
  edge := by intro v d t; cases t <;> rfl

theorem flatten_labels_iso {A B : RankedSet} {n : ℕ} (P : FiniteSystem B n)
    (F G : RankedMap B (FiniteSystem A))
    (h : ∀ r b, Isomorphic (F r b) (G r b)) :
    Isomorphic (flatten (relabel F P)) (flatten (relabel G P)) := by
  classical
  let f v := Classical.choice (h (P.graph.label v).1 (P.graph.label v).2)
  let Q := fun v => (F (P.graph.label v).1 (P.graph.label v).2).graph
  let R := fun v => (G (P.graph.label v).1 (P.graph.label v).2).graph
  let eqF := Fintype.equivFin ((v : P.Vertex) × (F (P.graph.label v).1 (P.graph.label v).2).Vertex)
  let eqG := Fintype.equivFin ((v : P.Vertex) × (G (P.graph.label v).1 (P.graph.label v).2).Vertex)
  exact ⟨isoTrans (isoSymm (reindexIso (substitute P.graph Q) eqF))
    (isoTrans (substituteInnerIso P.graph Q R f) (reindexIso (substitute P.graph R) eqG))⟩

private theorem presentation_ext {A : RankedSet} {n : ℕ} {V : Type}
    (G H : Presentation A n V) (hl : G.label = H.label) (hi : G.initial = H.initial)
    (hr : G.root = H.root) (he : G.edge = H.edge) : G = H := by
  cases G
  cases H
  cases hl
  cases hi
  cases hr
  cases he
  rfl

theorem iso_eq_reindex {A : RankedSet} {n : ℕ} {V W : Type}
    {P : Presentation A n V} {Q : Presentation A n W} (f : PresentationIso P Q) :
    Q = reindex P f.vertex := by
  have hl : Q.label = (reindex P f.vertex).label := by
    funext w
    obtain ⟨v, rfl⟩ := f.vertex.surjective w
    exact (f.label v).trans (congrArg P.label (f.vertex.symm_apply_apply v)).symm
  have hi : Q.initial = (reindex P f.vertex).initial := by
    ext w
    obtain ⟨v, rfl⟩ := f.vertex.surjective w
    change Q.initial (f.vertex v) ↔ P.initial (f.vertex.symm (f.vertex v))
    rw [f.vertex.symm_apply_apply]
    exact f.initial v
  have hr : Q.root = (reindex P f.vertex).root := by
    ext w
    obtain ⟨v, rfl⟩ := f.vertex.surjective w
    change Q.root (f.vertex v) ↔ P.root (f.vertex.symm (f.vertex v))
    rw [f.vertex.symm_apply_apply]
    exact f.root v
  have he : Q.edge = (reindex P f.vertex).edge := by
    funext w d t
    apply propext
    obtain ⟨v, rfl⟩ := f.vertex.surjective w
    obtain ⟨s, rfl⟩ := (Equiv.sumCongr f.vertex (Equiv.refl (Fin n))).surjective t
    have h := f.edge v d s
    cases s <;> simpa [reindex] using h
  exact presentation_ext Q (reindex P f.vertex) hl hi hr he

def relabelIso {A B : RankedSet} (g : RankedMap A B) {n : ℕ}
    {S T : FiniteSystem A n} (f : PresentationIso S.graph T.graph) :
    PresentationIso (relabel g S).graph (relabel g T).graph where
  vertex := f.vertex
  label := fun v => congrArg (fun a : Symbol A => Sigma.mk a.1 (g a.1 a.2)) (f.label v)
  initial := f.initial
  root := f.root
  edge := f.edge

def flattenGraphIso {A : RankedSet} {n : ℕ} {V W : Type}
    {P : Presentation (FiniteSystem A) n V} {Q : Presentation (FiniteSystem A) n W}
    (f : PresentationIso P Q) : PresentationIso (flattenPresentation P) (flattenPresentation Q) := by
  have he := iso_eq_reindex f
  exact Eq.mp (congrArg (fun R => PresentationIso (flattenPresentation P) (flattenPresentation R)) he.symm)
    (isoSymm (substituteOuterReindex P (fun v => (Inner P v).graph) f.vertex))

theorem flatten_iso {A : RankedSet} {n : ℕ} (S T : FiniteSystem (FiniteSystem A) n)
    (h : Isomorphic S T) : Isomorphic (flatten S) (flatten T) := by
  classical
  obtain ⟨f⟩ := h
  exact ⟨isoTrans (isoSymm (reindexIso _ (Fintype.equivFin _)))
    (isoTrans (flattenGraphIso f) (reindexIso _ (Fintype.equivFin _)))⟩

end Lax369799Proofs.UntrimmedFlattening
