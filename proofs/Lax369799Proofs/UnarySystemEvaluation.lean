import Lax369799.UnarySystemEvaluation
import Lax369799Proofs.UnaryGraphEvaluation
import Lax369799Proofs.FinitePathEvaluation
import Lax369799Proofs.PresentationCovers

namespace Lax369799Proofs.UnarySystemEvaluation
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet System Presentation)
open FinitePresentations FiniteSyntacticAlgebra UnfoldAutomata
open Lax369799.UnarySystemEvaluation

private noncomputable def first {A : RankedSet} (S : System A 0) : S.val.Vertex :=
  Classical.choose S.property.1

private theorem initial_eq {A : RankedSet} (S : System A 0) : S.val.graph.initial = {first S} :=
  Classical.choose_spec S.property.1

private theorem initial_unique {A : RankedSet} (S : System A 0) {v : S.val.Vertex}
    (h : v ∈ S.val.graph.initial) : v = first S := by rwa [initial_eq] at h

private theorem one {A : RankedSet} {S : System A 0} (hu : ∀ v, Rank S v ≤ 1)
    (v : S.val.Vertex) (d : Fin (Rank S v)) : Rank S v = 1 := by
  have := hu v
  have := d.isLt
  omega

private theorem cast_label {A : RankedSet} (s : RankedSystems.Symbol A) {n : ℕ} (h : s.1 = n) :
    (⟨n, h ▸ s.2⟩ : RankedSystems.Symbol A) = s := by cases s; cases h; rfl

private theorem finite_walk {A : RankedSet} {V : Type} (G : Presentation A 0 V) {a z : V}
    (h : Relation.ReflTransGen G.Step a z) :
    ∃ (k : ℕ) (p : Fin (k + 1) → V), p 0 = a ∧ p (Fin.last k) = z ∧
      ∀ i : Fin k, ∃ d, G.edge (p i.castSucc) d (.inl (p i.succ)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun i => Fin.elim0 i⟩
  | @tail y z hp hyz ih =>
    obtain ⟨k, p, hstart, hend, hedge⟩ := ih
    refine ⟨k + 1, Fin.lastCases z p, ?_, by simp, ?_⟩
    · change Fin.lastCases z p (Fin.castSucc (0 : Fin (k + 1))) = a
      rw [Fin.lastCases_castSucc]
      exact hstart
    · intro i
      cases i using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last, hend]
        exact hyz
      | cast i => simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using hedge i

private theorem finite_branch_exists {A : RankedSet} (S : System A 0) (z : S.val.Vertex)
    (hz : Rank S z = 0) : ∃ k, Nonempty (FiniteBranch S k) := by
  classical
  obtain ⟨r, hr, hp⟩ := S.val.reachable z
  have hr' : r = first S := by
    rcases hr with hr | hr
    · exact initial_unique S hr
    · rw [S.property.2.1] at hr
      exact hr.elim
  subst r
  obtain ⟨k, p, hstart, hend, hedge⟩ := finite_walk S.val.graph hp
  choose d hd using hedge
  refine ⟨k, ⟨{
    vertex := p
    direction := fun i => ⟨d i, S.val.graph.direction_valid _ _ _ (hd i)⟩
    starts := ?_
    follows := hd
    ends := ?_ }⟩⟩
  · rw [hstart, initial_eq]
    rfl
  · simpa only [hend] using hz

private def finitePath {A : RankedSet} {S : System A 0} (hu : ∀ v, Rank S v ≤ 1)
    {k : ℕ} (b : FiniteBranch S k) : FiniteSystem A 0 :=
  FinitePathEvaluation.path (fun i => unaryLabel hu (b.vertex i.castSucc) (b.direction i))
    (b.ends ▸ (S.val.graph.label (b.vertex (Fin.last k))).2)

private theorem finite_step {A : RankedSet} {S : System A 0} (hu : ∀ v, Rank S v ≤ 1)
    {k : ℕ} (b : FiniteBranch S k) (i : Fin k) :
    S.val.graph.edge (b.vertex i.castSucc) 0 (.inl (b.vertex i.succ)) := by
  have hd : (b.direction i).val = 0 := by have := (b.direction i).isLt; have := hu (b.vertex i.castSucc); omega
  simpa only [hd] using b.follows i

private def finiteCover {A : RankedSet} {S : System A 0} (hu : ∀ v, Rank S v ≤ 1)
    {k : ℕ} (b : FiniteBranch S k) :
    Lax369799.PresentationCovers.Cover (finitePath hu b).graph S.val.graph where
  toFun := b.vertex
  label := by
    intro v
    cases v using Fin.lastCases with
    | last =>
      change S.val.graph.label (b.vertex (Fin.last k)) =
        Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) _ _ (Fin.last k)
      rw [Fin.lastCases_last]
      exact (cast_label _ b.ends).symm
    | cast i =>
      change S.val.graph.label (b.vertex i.castSucc) =
        Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) _ _ i.castSucc
      rw [Fin.lastCases_castSucc]
      exact (cast_label _ (one hu _ (b.direction i))).symm
  initial := by intro v hv; change v = (0 : Fin (k + 1)) at hv; subst v; exact b.starts
  root := by intro _ h; exact h.elim
  edge := by
    rintro v d t ⟨i, rfl, rfl, rfl⟩
    exact finite_step hu b i
  initial_lift := by
    intro v hv
    have hv' := (initial_unique S hv).trans (initial_unique S b.starts).symm
    exact ⟨(0 : Fin (k + 1)), rfl, hv'.symm⟩
  root_lift := by intro v hv; rw [S.property.2.1] at hv; exact hv.elim
  edge_lift := by
    intro v d t ht
    cases v using Fin.lastCases with
    | last =>
      have hd := S.val.graph.direction_valid _ _ _ ht
      change d < Rank S (b.vertex (Fin.last k)) at hd
      rw [b.ends] at hd
      omega
    | cast i =>
      have hd := S.val.graph.direction_valid _ _ _ ht
      change d < Rank S (b.vertex i.castSucc) at hd
      have hd0 : d = 0 := by have := hu (b.vertex i.castSucc); omega
      subst d
      have h1 := one hu _ (b.direction i)
      have huniq := (S.property.2.2 (b.vertex i.castSucc) 0 (by rw [show
        (S.val.graph.label (b.vertex i.castSucc)).1 = 1 from h1]; decide)).choose_spec.2
      refine ⟨.inl i.succ, ⟨i, rfl, rfl, rfl⟩, ?_⟩
      exact (huniq _ (finite_step hu b i)).trans (huniq _ ht).symm

private theorem finite_evaluation {A : RankedSet} (E : Lax369799.SetSystemAlgebras.SetAlgebra A)
    {S : System A 0} (hu : ∀ v, Rank S v ≤ 1) {k : ℕ} (b : FiniteBranch S k) :
    E.eval 0 (ofSetSystem S.val) = E.eval 0 (finitePath hu b) := by
  exact (SetSystemAlgebras.folding_invariance E _ _ (finiteCover hu b)
    (PresentationCovers.surjective_of_reachable (finiteCover hu b) S.val.reachable)).symm


private theorem successor_exists {A : RankedSet} (S : System A 0)
    (h1 : ∀ v, Rank S v = 1) (v : S.val.Vertex) : ∃ w, S.val.graph.edge v 0 (.inl w) := by
  obtain ⟨t, ht, _⟩ := S.property.2.2 v 0 (by rw [show (S.val.graph.label v).1 = 1 from h1 v]; decide)
  cases t with
  | inl w => exact ⟨w, ht⟩
  | inr j => exact Fin.elim0 j

private noncomputable def next {A : RankedSet} (S : System A 0) (h1 : ∀ v, Rank S v = 1)
    (v : S.val.Vertex) : S.val.Vertex := Classical.choose (successor_exists S h1 v)

private theorem next_edge {A : RankedSet} (S : System A 0) (h1 : ∀ v, Rank S v = 1)
    (v : S.val.Vertex) : S.val.graph.edge v 0 (.inl (next S h1 v)) :=
  Classical.choose_spec (successor_exists S h1 v)

private theorem edge_eq {A : RankedSet} (S : System A 0) (h1 : ∀ v, Rank S v = 1)
    (v : S.val.Vertex) (d : ℕ) (t : S.val.Vertex ⊕ Fin 0) (ht : S.val.graph.edge v d t) :
    d = 0 ∧ t = .inl (next S h1 v) := by
  have hd := S.val.graph.direction_valid _ _ _ ht
  have hd0 : d = 0 := by change d < Rank S v at hd; rw [h1] at hd; omega
  subst d
  obtain ⟨z, _, hz⟩ := S.property.2.2 v 0 (by rw [show (S.val.graph.label v).1 = 1 from h1 v]; decide)
  exact ⟨rfl, (hz _ ht).trans (hz _ (next_edge S h1 v)).symm⟩

private def canonicalCover {A : RankedSet} (S : System A 0) (h1 : ∀ v, Rank S v = 1) :
    Lax369799.PresentationCovers.Cover
      (UnaryGraphEvaluation.graph (next S h1) (first S) (fun v => h1 v ▸ (S.val.graph.label v).2))
      S.val.graph where
  toFun := id
  label := fun v => (cast_label _ (h1 v)).symm
  initial := by intro v hv; rw [initial_eq]; exact hv
  root := by intro _ h; exact h.elim
  edge := by rintro v d t ⟨rfl, rfl⟩; exact next_edge S h1 v
  initial_lift := by intro v hv; rw [initial_eq] at hv; exact ⟨v, hv, rfl⟩
  root_lift := by intro v hv; rw [S.property.2.1] at hv; exact hv.elim
  edge_lift := by
    intro v d t ht
    obtain ⟨rfl, rfl⟩ := edge_eq S h1 v d t ht
    exact ⟨.inl (next S h1 v), ⟨rfl, rfl⟩, rfl⟩

private theorem canonical_evaluation {A : RankedSet} (E : Lax369799.SetSystemAlgebras.SetAlgebra A)
    (S : System A 0) (h1 : ∀ v, Rank S v = 1) :
    E.eval 0 (enumerate (UnaryGraphEvaluation.graph (next S h1) (first S)
      (fun v => h1 v ▸ (S.val.graph.label v).2))) = E.eval 0 (ofSetSystem S.val) := by
  exact (SetSystemAlgebras.raw_cover E (canonicalCover S h1) Function.surjective_id).trans
    (E.isomorphic 0 _ _ ⟨UntrimmedFlattening.isoSymm
      (UntrimmedFlattening.reindexIso S.val.graph (Fintype.equivFin _))⟩)

private theorem canonical_reachable {A : RankedSet} (S : System A 0) (h1 : ∀ v, Rank S v = 1) :
    ∀ v, ∃ n, UnaryGraphEvaluation.trace (next S h1) (first S) n = v := by
  intro v
  obtain ⟨r, hr, hp⟩ := S.val.reachable v
  have hr' : r = first S := by
    rcases hr with hr | hr
    · exact initial_unique S hr
    · rw [S.property.2.1] at hr; exact hr.elim
  subst r
  induction hp with
  | refl => exact ⟨0, rfl⟩
  | @tail y z hp hyz ih =>
    obtain ⟨n, rfl⟩ := ih
    obtain ⟨d, hd⟩ := hyz
    have heq := Sum.inl.inj (edge_eq S h1 _ d _ hd).2
    exact ⟨n + 1, heq.symm⟩

private theorem infinite_reaches {A : RankedSet} {S : System A 0} (hu : ∀ v, Rank S v ≤ 1)
    (b : InfiniteBranch S) : ∀ v, ∃ n, b.vertex n = v := by
  intro v
  obtain ⟨r, hr, hp⟩ := S.val.reachable v
  have hr' : r = b.vertex 0 := by
    rcases hr with hr | hr
    · exact (initial_unique S hr).trans (initial_unique S b.starts).symm
    · rw [S.property.2.1] at hr; exact hr.elim
  subst r
  induction hp with
  | refl => exact ⟨0, rfl⟩
  | @tail y z hp hyz ih =>
    obtain ⟨n, rfl⟩ := ih
    obtain ⟨d, hd⟩ := hyz
    have hdir : (b.direction n).val = 0 := by have := (b.direction n).isLt; have := hu (b.vertex n); omega
    have hdvalid := S.val.graph.direction_valid _ _ _ hd
    change d < Rank S (b.vertex n) at hdvalid
    have hd0 : d = 0 := by have := hu (b.vertex n); omega
    subst d
    have h1 := one hu _ (b.direction n)
    have hzero : 0 < (S.val.graph.label (b.vertex n)).1 := by change 0 < Rank S (b.vertex n); rw [h1]; decide
    obtain ⟨t, _, ht⟩ := S.property.2.2 (b.vertex n) 0 hzero
    have hb : S.val.graph.edge (b.vertex n) 0 (.inl (b.vertex (n + 1))) := by simpa only [hdir] using b.follows n
    exact ⟨n + 1, Sum.inl.inj ((ht _ hb).trans (ht _ hd).symm)⟩

private theorem infinite_evaluation {A : RankedSet} (E : Lax369799.SetSystemAlgebras.SetAlgebra A)
    (F : Set (A 0)) [Finite (A 1)] {S : System A 0} (hu : ∀ v, Rank S v ≤ 1)
    (b : InfiniteBranch S) :
    E.eval 0 (ofSetSystem S.val) ∈ F ↔ AlgebraicOmegaWords.Accepts E.toAlgebra F
      (fun n => unaryLabel hu (b.vertex n) (b.direction n)) := by
  have h1 (v : S.val.Vertex) : Rank S v = 1 := by
    obtain ⟨n, rfl⟩ := infinite_reaches hu b v
    exact one hu _ (b.direction n)
  have htrace (n : ℕ) : UnaryGraphEvaluation.trace (next S h1) (first S) n = b.vertex n := by
    induction n with
    | zero => exact (initial_unique S b.starts).symm
    | succ n ih =>
      change next S h1 (UnaryGraphEvaluation.trace (next S h1) (first S) n) = b.vertex (n + 1)
      rw [ih]
      exact (Sum.inl.inj (edge_eq S h1 _ _ _ (b.follows n)).2).symm
  have h := UnaryGraphEvaluation.agreement E F (next S h1) (first S)
    (fun v => h1 v ▸ (S.val.graph.label v).2) (canonical_reachable S h1)
  rw [canonical_evaluation E S h1] at h
  convert h using 2
  funext n
  dsimp only [Function.comp_apply]
  have hs : (⟨1, unaryLabel hu (b.vertex n) (b.direction n)⟩ : RankedSystems.Symbol A) =
      ⟨1, h1 (UnaryGraphEvaluation.trace (next S h1) (first S) n) ▸
        (S.val.graph.label (UnaryGraphEvaluation.trace (next S h1) (first S) n)).2⟩ :=
    (cast_label _ (one hu _ (b.direction n))).trans
      ((congrArg S.val.graph.label (htrace n)).symm.trans (cast_label _ (h1 _)).symm)
  exact eq_of_heq (Sigma.mk.inj hs).2


/--
---
conclusion: Lax369799.UnarySystemEvaluation.agreement
---
A terminating branch covers the entire unary system. An infinite branch
visits every vertex, and the unary graph evaluation theorem applies.
If there is a leaf, reachability supplies a terminating branch; otherwise
all vertices are unary and the successor function supplies an infinite one.
-/
theorem agreement {A : RankedSet} (E : Lax369799.SetSystemAlgebras.SetAlgebra A)
    (F : Set (A 0)) [Finite (A 1)] (S : System A 0) (hu : ∀ v, Rank S v ≤ 1) :
    E.eval 0 (ofSetSystem S.val) ∈ F ↔
      (∀ k (b : FiniteBranch S k), FiniteBranchWords.value E.toAlgebra (finiteWord hu b) (leafValue b) ∈ F) ∧
      (∀ b : InfiniteBranch S, AlgebraicOmegaWords.Accepts E.toAlgebra F (infiniteWord hu b)) := by
  constructor
  · intro h
    constructor
    · intro k b
      have he := finite_evaluation E hu b
      rw [he, show E.eval 0 (finitePath hu b) =
        FiniteBranchWords.value E.toAlgebra (finiteWord hu b) (leafValue b) from
          FinitePathEvaluation.evaluation E.toAlgebra _ _] at h
      exact h
    · intro b
      exact (infinite_evaluation E F hu b).mp h
  · rintro ⟨hf, hi⟩
    by_cases hleaf : ∃ v, Rank S v = 0
    · obtain ⟨z, hz⟩ := hleaf
      obtain ⟨k, ⟨b⟩⟩ := finite_branch_exists S z hz
      rw [finite_evaluation E hu b]
      exact (FinitePathEvaluation.evaluation E.toAlgebra _ _).symm ▸ hf k b
    · have h1 (v : S.val.Vertex) : Rank S v = 1 := by
        have hne : Rank S v ≠ 0 := fun h => hleaf ⟨v, h⟩
        have := hu v
        omega
      let b : InfiniteBranch S := {
        vertex := UnaryGraphEvaluation.trace (next S h1) (first S)
        direction := fun n => ⟨0, by rw [h1]; decide⟩
        starts := by change first S ∈ S.val.graph.initial; rw [initial_eq]; rfl
        follows := fun n => next_edge S h1 _ }
      exact (infinite_evaluation E F hu b).mpr (hi b)

end Lax369799Proofs.UnarySystemEvaluation
