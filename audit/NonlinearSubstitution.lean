import Lax369799Proofs.AtomicFlattening
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

#print axioms distribution_fails
#print axioms mixed_is_resolution_of_repeated
#print axioms resolutions_recover_mixed
end NonlinearSubstitutionAudit
