import Lax369799Proofs.AtomicFlattening
import Lax369799Proofs.YieldObservations
import Lax369799Proofs.DeterministicElements
import Lax369799.PolynomialContexts
import Mathlib.Tactic.FinCases

/- A nonempty, root-free test of distributing a unary substitution over
   its possible variable targets. The unary component repeats its variable. -/
namespace NonlinearSubstitutionAudit
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799Proofs.Pullbacks
open Lax369799.Resolutions

abbrev A : RankedSet := fun _ => Unit

def binary {n : ℕ} (σ : Fin 2 → Fin n) : System A n :=
  ⟨{ size := 1
     graph := {
       label := fun _ => ⟨2, ()⟩
       initial := Set.univ
       root := ∅
       edge := fun _ d t => ∃ i : Fin 2, d = i.val ∧ t = .inr (σ i)
       direction_valid := by rintro v d t ⟨i, rfl, _⟩; exact i.isLt }
     reachable := fun v => ⟨v, Or.inl trivial, .refl⟩ }, by
    refine ⟨⟨(0 : Fin 1), by ext v; simp [Subsingleton.elim v (0 : Fin 1)]⟩, rfl, ?_⟩
    intro v d hd
    refine ⟨.inr (σ ⟨d, hd⟩), ⟨⟨d, hd⟩, rfl, rfl⟩, ?_⟩
    rintro t ⟨i, hi, rfl⟩
    exact congrArg (fun j => Sum.inr (σ j)) (Fin.ext hi.symm)⟩

def repeated : System A 1 := binary (fun _ => 0)
def mixed : System A 2 := binary id

-- b(x₀ + x₁), with b = a(x,x).
def pattern : SetSystem (SetSystem A) 2 where
  size := 1
  graph := {
    label := fun _ => ⟨1, repeated.val⟩
    initial := Set.univ
    root := ∅
    edge := fun _ d t => d = 0 ∧ ∃ i : Fin 2, t = .inr i
    direction_valid := by rintro v d t ⟨rfl, _⟩; exact Nat.zero_lt_one }
  reachable := fun v => ⟨v, Or.inl trivial, .refl⟩

-- a(x₀,x₀) + a(x₁,x₁).
def uniform : SetSystem A 2 where
  size := 2
  graph := {
    label := fun _ => ⟨2, ()⟩
    initial := Set.univ
    root := ∅
    edge := fun v d t => d < 2 ∧ t = .inr v
    direction_valid := fun _ _ _ h => h.1 }
  reachable := fun v => ⟨v, Or.inl trivial, .refl⟩

theorem mixed_resolution : DirectResolution (flatten pattern) mixed := by
  let f : Map mixed.val.graph (Lax369799Proofs.Flattening.graph pattern) := {
    toFun := fun _ => ⟨(0 : Fin 1), (0 : Fin 1)⟩
    initial := fun _ _ => ⟨trivial, trivial⟩
    root := fun _ h => False.elim h
    label := fun _ => rfl
    edge := by
      rintro v d t ⟨i, rfl, rfl⟩
      exact Or.inr ⟨(0 : Fin 1), ⟨i, rfl, rfl⟩,
        Or.inr ⟨i, ⟨rfl, i, rfl⟩, rfl⟩⟩ }
  exact ⟨lift f⟩

-- Splitting the repeated variable retains the two independent choices.
def variableOrigin : Fin 2 → Fin 1 := fun _ => 0

theorem mixed_is_resolution_of_repeated : IsResolution repeated.val mixed variableOrigin := by
  refine ⟨{
    toFun := id
    initial := fun _ _ => trivial
    root := fun _ h => False.elim h
    label := fun _ => rfl
    edge := ?_ }⟩
  rintro v d t ⟨s, ⟨i, rfl, rfl⟩, rfl⟩
  exact ⟨i, rfl, rfl⟩

def splitPattern : System (System A) 2 := atomicSystem mixed

noncomputable def splitResolution : FlattenResolution pattern splitPattern where
  vertex := fun _ => (0 : Fin 1)
  variableMap := fun _ => variableOrigin
  initial := fun _ _ => trivial
  resolves := fun _ => mixed_is_resolution_of_repeated
  transition := by
    rintro v i w ⟨j, _, h⟩
    cases h
  exit := by
    rintro v i j ⟨l, _, he⟩
    exact ⟨rfl, j, rfl⟩

theorem resolutions_recover_mixed :
    ∃ U : System A 2, SystemFlattening splitPattern U ∧
      DirectResolution (flatten pattern) U ∧ UnfoldsTo mixed.val U.val := by
  obtain ⟨U, hu⟩ := Lax369799Proofs.Flattening.flatten_system splitPattern
  refine ⟨U, hu,
    Lax369799Proofs.Flattening.flatten_resolution_sound pattern splitPattern splitResolution U hu, ?_⟩
  rw [hu]
  exact Lax369799Proofs.AtomicFlattening.outer_atomic_cover mixed.val

theorem no_uniform_initial_yield : ¬ InitYield uniform mixed := by
  rintro ⟨D, ⟨f⟩, ⟨g, hg⟩⟩
  obtain ⟨v, _⟩ := D.property.1
  have out (i : Fin 2) : f.toFun v = i := by
    have he : mixed.val.graph.edge (g.toFun v) i.val (.inr i) := ⟨i, rfl, rfl⟩
    obtain ⟨t, ht, heq⟩ := hg.2.2 v i.val (.inr i) he
    cases t with
    | inl w => cases heq
    | inr j =>
      have hj : j = i := Sum.inr.inj heq
      subst j
      have hf := (f.edge v i.val (.inr i) ht).2
      exact (Sum.inr.inj hf).symm
  have impossible : (0 : Fin 2) = 1 := (out 0).symm.trans (out 1)
  exact (by decide : (0 : Fin 2) ≠ 1) impossible

theorem no_uniform_root_yield (U : System A 2) : ¬ InitYield (uproot uniform) U := by
  rintro ⟨D, ⟨f⟩, _⟩
  obtain ⟨v, hv⟩ := D.property.1
  have hi := f.initial v (by rw [hv]; rfl)
  exact hi

theorem distribution_fails : ¬ YieldBelow (flatten pattern) uniform := by
  intro h
  have hm : Yield (flatten pattern) mixed.val := Or.inl ⟨mixed,
    ⟨mixed, mixed_resolution, ⟨Lax369799Proofs.MorphismTheorems.identity _,
      Lax369799Proofs.MorphismTheorems.identity_surjective _⟩⟩, rfl⟩
  rcases h mixed.val hm with ⟨U, hu, he⟩ | ⟨U, hu, _⟩
  · have he' : U = mixed := Subtype.ext he.symm
    subst U
    exact no_uniform_initial_yield hu
  · exact no_uniform_root_yield U hu

-- The separate continuity consequence: every abstract unary value must
-- distribute over a nondeterministic choice of output variable.
def choice {B : RankedSet} (b : B 1) : SetSystem B 2 where
  size := 1
  graph := {
    label := fun _ => ⟨1, b⟩
    initial := Set.univ
    root := ∅
    edge := fun _ d t => d = 0 ∧ ∃ i : Fin 2, t = .inr i
    direction_valid := by rintro v d t ⟨rfl, _⟩; exact Nat.zero_lt_one }
  reachable := fun v => ⟨v, Or.inl trivial, .refl⟩

private theorem choice_projection {B : RankedSet} (b : B 1) (i : Fin 2) :
    Lax369799.DeterministicElements.projection (choice b) i = atomic b := by
  have he : (Lax369799.DeterministicElements.projection (choice b) i).graph.edge =
      (atomic b).graph.edge := by
    funext v d t
    apply propext
    change (d = 0 ∧ ∃ j : Fin 2, Sum.map id (fun _ => i) t = .inr j) ↔
      ∃ k : Fin 1, d = k.val ∧ t = .inr k
    cases t with
    | inl w => simp
    | inr k =>
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simp
  unfold Lax369799.DeterministicElements.projection choice atomic
  congr 1
  congr 1

-- This uses the continuity-bearing SetAlgebra interface, not the repaired
-- finite-presentation algebra, which does not assert continuity.
theorem continuity_forces_distribution {B : RankedSet} (E : Lax369799.SetAlgebras.SetAlgebra B)
    (b : B 1) :
    E.eval 2 (choice b) = E.eval 2 (Lax369799.DeterministicElements.parallel (fun _ : Fin 2 => b)) := by
  have h := Lax369799Proofs.DeterministicElements.normal_value E (by decide : 0 < 2)
    (choice b) (fun _ => Nat.le_refl 1)
  simpa only [choice_projection, E.unit] using h.symm

def repeatedLabel {B : RankedSet} (a : B 2) : System B 1 :=
  Lax369799.PolynomialContexts.withLabels repeated (fun _ => a)

theorem continuity_forces_expanded_distribution {B : RankedSet}
    (E : Lax369799.SetAlgebras.SetAlgebra B) (a : B 2) :
    E.eval 2 (flatten (choice (repeatedLabel a).val)) = E.eval 2 (flatten
      (Lax369799.DeterministicElements.parallel (fun _ : Fin 2 => (repeatedLabel a).val))) := by
  rw [← E.associative 2 (choice (repeatedLabel a).val), ← E.associative 2
    (Lax369799.DeterministicElements.parallel (fun _ : Fin 2 => (repeatedLabel a).val))]
  exact continuity_forces_distribution E (E.eval 1 (repeatedLabel a).val)

#print axioms distribution_fails
#print axioms mixed_is_resolution_of_repeated
#print axioms resolutions_recover_mixed
#print axioms continuity_forces_distribution
#print axioms continuity_forces_expanded_distribution
end NonlinearSubstitutionAudit

namespace OriginalContinuityBridgeAudit
set_option backward.isDefEq.respectTransparency false
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.PresentationCovers Lax369799.SyntacticOrder
open Lax369799Proofs Lax369799Proofs.Pullbacks

abbrev B : RankedSet := fun _ => Bool

def Good {V : Type} (G : Presentation B 0 V) : Prop :=
  ∀ v, v ∈ G.initial → ∀ d e w z,
    G.edge v d (.inl w) → G.edge v e (.inl z) → (G.label w).2 = (G.label z).2

def language : Lax369799.Algebras.Language B := fun U => Good U.val.graph

theorem good_map {V W : Type} {G : Presentation B 0 V} {H : Presentation B 0 W}
    (f : Map G H) (h : Good H) : Good G := by
  intro v hv d e w z hw hz
  have hh := h (f.toFun v) (f.initial v hv) d e (f.toFun w) (f.toFun z)
    (f.edge v d (.inl w) hw) (f.edge v e (.inl z) hz)
  exact (congrArg (fun a : Symbol B => a.2) (f.label w)).symm.trans
    (hh.trans (congrArg (fun a : Symbol B => a.2) (f.label z)))

theorem good_cover {V W : Type} {G : Presentation B 0 V} {H : Presentation B 0 W}
    (f : Cover G H) (h : Good G) : Good H := by
  intro w hw d e y z hy hz
  obtain ⟨v, hv, rfl⟩ := f.initial_lift w hw
  obtain ⟨s, hs, he⟩ := f.edge_lift v d (.inl y) hy
  obtain ⟨t, ht, hf⟩ := f.edge_lift v e (.inl z) hz
  cases s with
  | inr i => exact Fin.elim0 i
  | inl a =>
    cases t with
    | inr i => exact Fin.elim0 i
    | inl b =>
      have he := Sum.inl.inj he
      have hf := Sum.inl.inj hf
      subst y; subst z
      exact (congrArg (fun a : Symbol B => a.2) (f.label a)).trans
        ((h v hv d e a b hs ht).trans
          (congrArg (fun a : Symbol B => a.2) (f.label b)).symm)

theorem language_unfold : Lax369799.Algebras.UnfoldInvariantLanguage language := by
  intro S T ⟨U, ⟨f, hf⟩, ⟨g, hg⟩⟩
  let fm : Map U.graph S.val.graph := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  let gm : Map U.graph T.val.graph := ⟨g.toFun, g.initial, g.root, g.label, g.edge⟩
  let fc : Cover U.graph S.val.graph := ⟨f.toFun, f.label, f.initial, f.root, f.edge, hf.1, hf.2.1, hf.2.2⟩
  let gc : Cover U.graph T.val.graph := ⟨g.toFun, g.label, g.initial, g.root, g.edge, hg.1, hg.2.1, hg.2.2⟩
  exact ⟨fun h => good_cover gc (good_map fm h), fun h => good_cover fc (good_map gm h)⟩

def closeGraph (S : SetSystem B 2) : Presentation B 0 (S.Vertex ⊕ Fin 2) where
  label := Sum.elim S.graph.label (fun i => ⟨0, i == 1⟩)
  initial := Sum.elim S.graph.initial (fun _ => False)
  root := Sum.elim S.graph.root (fun _ => False)
  edge := fun v d t => match v with
    | .inl v => ∃ s, S.graph.edge v d s ∧ t = .inl s
    | .inr _ => False
  direction_valid := by
    intro v d t h
    cases v with
    | inl v => obtain ⟨s, hs, _⟩ := h; exact S.graph.direction_valid v d s hs
    | inr i => exact False.elim h

def closing : SetContext B 2 0 where
  system := {
    size := 3
    graph := {
      label := Fin.cases ⟨2, .inr ⟨rfl⟩⟩ (fun i => ⟨0, .inl (i == 1)⟩)
      initial := {0}
      root := ∅
      edge := fun v d t => v = 0 ∧ ∃ i : Fin 2, d = i.val ∧ t = .inl i.succ
      direction_valid := by rintro v d t ⟨rfl, i, rfl, _⟩; exact i.isLt }
    reachable := by
      intro v
      refine ⟨0, Or.inl rfl, ?_⟩
      refine Fin.cases ?_ (fun i => ?_) v
      · exact .refl
      · exact Relation.ReflTransGen.single ⟨i.val, rfl, i, rfl, rfl⟩ }
  one_hole := by
    refine ⟨0, ⟨⟨rfl⟩, rfl⟩, ?_⟩
    intro v hv
    fin_cases v
    · rfl
    all_goals obtain ⟨h, he⟩ := hv; cases he

private def closingVertex (S : SetSystem B 2) :
    ((v : closing.system.Vertex) × (Inner (relabel (substitution S) closing.system) v).Vertex) →
      S.Vertex ⊕ Fin 2 := fun v =>
  Fin.cases (fun w => .inl w) (fun i _ => .inr i) v.1 v.2

private def closingCover (S : SetSystem B 2) :
    Cover (Flattening.graph (relabel (substitution S) closing.system)) (closeGraph S) where
  toFun := closingVertex S
  label := by rintro ⟨v, w⟩; fin_cases v <;> rfl
  initial := by
    rintro ⟨v, w⟩ ⟨hv, hw⟩
    change v = (0 : Fin 3) at hv
    subst v
    exact hw
  root := by
    rintro ⟨v, w⟩ (h | ⟨h, _⟩)
    · fin_cases v
      · exact h
      all_goals exact False.elim h
    · exact False.elim h
  edge := by
    rintro ⟨v, w⟩ d t ht
    fin_cases v
    · rcases ht with ⟨u, hu, rfl⟩ | ⟨i, hi, ht⟩
      · exact ⟨.inl u, hu, rfl⟩
      · rcases ht with ⟨⟨q, u⟩, ⟨_, j, hij, hq⟩, _, rfl⟩ | ⟨j, _, _⟩
        · have hij : i = j := Fin.ext hij
          subst j
          have hq : q = i.succ := Sum.inl.inj hq
          subst q
          exact ⟨.inr i, hi, rfl⟩
        · exact Fin.elim0 j
    all_goals
      rcases ht with ⟨u, ⟨i, _, _⟩, _⟩ | ⟨i, _, _⟩ <;> exact Fin.elim0 i
  initial_lift := by
    intro v hv
    cases v with
    | inl v => exact ⟨⟨(0 : Fin 3), v⟩, ⟨rfl, hv⟩, rfl⟩
    | inr i => exact False.elim hv
  root_lift := by
    intro v hv
    cases v with
    | inl v => exact ⟨⟨(0 : Fin 3), v⟩, Or.inl hv, rfl⟩
    | inr i => exact False.elim hv
  edge_lift := by
    rintro ⟨v, w⟩ d t ht
    fin_cases v
    · obtain ⟨s, hs, rfl⟩ := ht
      cases s with
      | inl u => exact ⟨.inl ⟨(0 : Fin 3), u⟩, Or.inl ⟨u, hs, rfl⟩, rfl⟩
      | inr i => exact ⟨.inl ⟨i.succ, (0 : Fin 1)⟩,
          Or.inr ⟨i, hs, Or.inl ⟨⟨i.succ, (0 : Fin 1)⟩, ⟨rfl, i, rfl, rfl⟩, trivial, rfl⟩⟩, rfl⟩
    all_goals exact False.elim ht

private theorem closing_yields (S : SetSystem B 2) :
    YieldEquivalent (plug closing S) (trim (closeGraph S)) := by
  let f := closingCover S
  let g : Map _ _ := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  exact (Yields.morphism_yields (trimMap g)).2
    (trimMap_surjective g f.initial_lift f.root_lift f.edge_lift)

def mixed : System B 2 := relabelSystem (fun _ _ => false) NonlinearSubstitutionAudit.mixed

def uniform : SetSystem B 2 := relabel (fun _ _ => false) NonlinearSubstitutionAudit.uniform

def repeated : System B 1 := NonlinearSubstitutionAudit.repeatedLabel (B := B) false

noncomputable def expanded : SetSystem B 2 :=
  flatten (NonlinearSubstitutionAudit.choice repeated.val)

noncomputable def expandedParallel : SetSystem B 2 :=
  flatten (Lax369799.DeterministicElements.parallel (fun _ : Fin 2 => repeated.val))

theorem close_deterministic (S : System B 2) : (trim (closeGraph S.val)).Deterministic := by
  obtain ⟨r, hr⟩ := S.property.1
  apply Yields.trim_deterministic (closeGraph S.val) (.inl r)
  · ext v
    cases v with
    | inl v =>
      change S.val.graph.initial v ↔ (Sum.inl v : S.val.Vertex ⊕ Fin 2) = .inl r
      rw [hr]
      change (v = r) ↔ (Sum.inl v : S.val.Vertex ⊕ Fin 2) = .inl r
      exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
    | inr i =>
      change False ↔ (Sum.inr i : S.val.Vertex ⊕ Fin 2) = .inl r
      simp
  · ext v
    cases v with
    | inl v => change S.val.graph.root v ↔ False; rw [S.property.2.1]; rfl
    | inr i => rfl
  · intro v d hd
    cases v with
    | inr i => exact False.elim (Nat.not_lt_zero d hd)
    | inl v =>
      obtain ⟨t, ht, unique⟩ := S.property.2.2 v d hd
      refine ⟨.inl t, ⟨t, ht, rfl⟩, ?_⟩
      rintro u ⟨s, hs, rfl⟩
      exact congrArg Sum.inl (unique s hs)

theorem good_uniform : Good (closeGraph uniform) := by
  intro v hv d e w z hw hz
  cases v with
  | inr i => exact False.elim hv
  | inl v =>
    obtain ⟨s, ⟨_, hs⟩, he⟩ := hw
    obtain ⟨t, ⟨_, ht⟩, hf⟩ := hz
    subst s; subst t
    have he := Sum.inl.inj he
    have hf := Sum.inl.inj hf
    subst w; subst z
    rfl

theorem not_good_mixed : ¬ Good (closeGraph mixed.val) := by
  intro h
  have hh := h (.inl (0 : Fin 1)) trivial 0 1 (.inr 0) (.inr 1)
    ⟨.inr 0, ⟨0, rfl, rfl⟩, rfl⟩ ⟨.inr 1, ⟨1, rfl, rfl⟩, rfl⟩
  have impossible : (false : Bool) = true := hh
  cases impossible

theorem accepting_of_good {V : Type} [Fintype V] (G : Presentation B 0 V)
    (hg : Good G) (hr : G.root = ∅) : Accepting language (trim G) := by
  intro T hT
  rcases hT with ⟨U, ⟨D, ⟨d⟩, g, hgc⟩, rfl⟩ | ⟨U, ⟨D, ⟨d⟩, _⟩, rfl⟩
  · let dm := PresentationObservations.toPresentation d
    let gc : Cover D.val.graph U.val.graph :=
      ⟨g.toFun, g.label, g.initial, g.root, g.edge, hgc.1, hgc.2.1, hgc.2.2⟩
    exact ⟨U, good_cover gc (good_map dm hg), Or.inl rfl⟩
  · obtain ⟨v, hv⟩ := D.property.1
    have hi := d.initial v (by rw [hv]; rfl)
    change (trim G).graph.root _ at hi
    change G.root _ at hi
    rw [hr] at hi
    exact False.elim hi

theorem uniform_accepted : Accepting language (plug closing uniform) := by
  have h := accepting_of_good (closeGraph uniform) good_uniform (by ext v; cases v <;> rfl)
  exact fun T ht => h T ((closing_yields uniform T).mp ht)

theorem mixed_rejected : ¬ Accepting language (plug closing mixed.val) := by
  intro h
  let M : System B 0 := ⟨trim (closeGraph mixed.val), close_deterministic mixed⟩
  have ha : Accepting language M.val := fun T ht => h T ((closing_yields mixed.val T).mpr ht)
  have hm := (Acceptance.accepting_system language language_unfold M).mp ha
  exact not_good_mixed (good_cover (FiniteAcceptance.trimProjection _) hm)

theorem mixed_resolution : DirectResolution expanded mixed := by
  let f : Map mixed.val.graph (Flattening.graph (NonlinearSubstitutionAudit.choice repeated.val)) := {
    toFun := fun _ => ⟨(0 : Fin 1), (0 : Fin 1)⟩
    initial := fun _ _ => ⟨trivial, trivial⟩
    root := fun _ h => False.elim h
    label := fun _ => rfl
    edge := by
      rintro v d t ⟨i, rfl, rfl⟩
      exact Or.inr ⟨(0 : Fin 1), ⟨i, rfl, rfl⟩,
        Or.inr ⟨i, ⟨rfl, i, rfl⟩, rfl⟩⟩ }
  exact ⟨lift f⟩

theorem expanded_rejected : ¬ Accepting language (plug closing expanded) := by
  intro h
  obtain ⟨f⟩ := mixed_resolution
  apply mixed_rejected
  intro T ht
  exact h T ((Yields.morphism_yields (Evaluation.plug_morphism closing f)).1 T ht)

private def parallelCover : Cover
    (Flattening.graph (Lax369799.DeterministicElements.parallel (fun _ : Fin 2 => repeated.val)))
    uniform.graph where
  toFun := Sigma.fst
  label := fun _ => rfl
  initial := fun _ _ => trivial
  root := fun _ h => h.elim (fun h => False.elim h) (fun h => False.elim h.1)
  edge := by
    intro v d t ht
    rcases ht with ⟨w, ⟨i, _, he⟩, _⟩ | ⟨i, hi, he⟩
    · cases he
    · have hd : d < 2 := repeated.val.graph.direction_valid v.2 d (.inr i) hi
      rcases he with ⟨w, ⟨_, he⟩, _⟩ | ⟨j, ⟨_, he⟩, rfl⟩
      · cases he
      · exact ⟨hd, he⟩
  initial_lift := fun v _ => ⟨⟨v, (0 : Fin 1)⟩, ⟨trivial, trivial⟩, rfl⟩
  root_lift := fun _ h => False.elim h
  edge_lift := by
    rintro v d t ⟨hd, rfl⟩
    exact ⟨.inr v.1, Or.inr ⟨(0 : Fin 1), ⟨⟨d, hd⟩, rfl, rfl⟩,
      Or.inr ⟨v.1, ⟨rfl, rfl⟩, rfl⟩⟩, rfl⟩

theorem parallel_accepted : Accepting language (plug closing expandedParallel) := by
  obtain ⟨f, hf⟩ := Lax369799Proofs.trim_cover _ uniform parallelCover
  have h : YieldBelow expandedParallel uniform := (Yields.morphism_yields f).1
  exact fun T ht => uniform_accepted T (YieldObservations.yield_context_congruence closing _ _ h T ht)

private def test : Lax369799.SyntacticOrder.SyntacticCarrier language 2 → Prop :=
  Quot.lift (fun S => Accepting language (plug closing S))
    (fun _ _ h => propext ⟨h.1 closing, h.2 closing⟩)

theorem distinct_classes :
    Lax369799.SyntacticOrder.syntacticMap language 2 expanded ≠
      Lax369799.SyntacticOrder.syntacticMap language 2 expandedParallel := by
  intro h
  have he := congrArg test h
  exact expanded_rejected (Eq.mpr he parallel_accepted)

/-- Original continuity and substitution-compatible evaluation cannot
both hold on this language's syntactic quotient. -/
theorem no_original_syntactic_algebra : ¬ Nonempty (Lax369799.SyntacticOrder.SyntacticAlgebra language) := by
  rintro ⟨E⟩
  let P := NonlinearSubstitutionAudit.choice repeated.val
  let Q := Lax369799.DeterministicElements.parallel (fun _ : Fin 2 => repeated.val)
  have h := NonlinearSubstitutionAudit.continuity_forces_distribution E.algebra
    (Lax369799.SyntacticOrder.syntacticMap language 1 repeated.val)
  have he : Lax369799.SyntacticOrder.syntacticMap language 2 expanded =
      Lax369799.SyntacticOrder.syntacticMap language 2 expandedParallel :=
    (E.evaluates 2 P).symm.trans (h.trans (E.evaluates 2 Q))
  exact distinct_classes he

#print axioms language_unfold
#print axioms distinct_classes
#print axioms no_original_syntactic_algebra

end OriginalContinuityBridgeAudit
