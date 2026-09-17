import Lax369799.ProfileSubstitution
import Lax369799Proofs.OptimalResolutions
import Lax369799Proofs.ResolutionFactorization

namespace Lax369799Proofs.ProfileSubstitution
open Lax369799.RankedSystems Lax369799.Flattening Lax369799.Morphisms Lax369799.Algebras
open Lax369799.Resolutions Lax369799.ProfileSubstitution

private def relabelMorphism {A B : RankedSet} (η : RankedMap A B) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) : Morphism (relabel η S) (relabel η T) where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := fun v => congrArg (fun a : Symbol A => (⟨a.1, η a.1 a.2⟩ : Symbol B)) (f.label v)
  edge := f.edge

theorem value_morphism {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} (S T : System A n) (f : Morphism S.val T.val) :
    E.eval n (relabelSystem η S) = E.eval n (relabelSystem η T) := by
  let g := relabelMorphism η f
  exact hE n (relabelSystem η S) (relabelSystem η T) ⟨(relabelSystem η S).val,
    ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
    ⟨g, MorphismTheorems.system_morphism_locally_surjective (relabelSystem η S) (relabelSystem η T) g⟩⟩

private theorem same_evaluated_labels {A B : RankedSet} {n : ℕ} (T : System (System A) n)
    (ρ : ∀ k, System A k → B k) (f : ∀ v, System A (T.val.graph.label v).1)
    (hf : ∀ v, ρ _ (f v) = ρ _ (T.val.graph.label v).2) :
    relabel ρ (withLabels T.val f) = relabel ρ T.val := by
  have hl : (relabel ρ (withLabels T.val f)).graph.label = (relabel ρ T.val).graph.label := by
    funext v
    exact congrArg (Sigma.mk _) (hf v)
  cases T with
  | mk T hT =>
    cases T with
    | mk size G hr =>
      cases G
      dsimp only [withLabels, relabel] at hl ⊢
      congr 1
      congr 1

/--
---
conclusion: Lax369799.ProfileSubstitution.transfer_resolution
---
Factor the given resolution and make every local variable map bounded.
Choose a matching local resolution from each replacement profile, retaining
the outer deterministic graph and all variable maps. The component values
are unchanged, so associativity preserves the value of the flattening.
-/
theorem transfer_resolution {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) (P : SetSystem (SetSystem A) 0)
    (Q : ∀ v, SetSystem A (P.graph.label v).1)
    (hQ : ∀ v, Lax369799.FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Inner P v) =
      Lax369799.FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Q v))
    (R : System A 0) (hR : DirectResolution (flatten P) R) :
    ∃ U : System A 0, DirectResolution (flatten (withLabels P Q)) U ∧
      E.eval 0 (relabelSystem η R) = E.eval 0 (relabelSystem η U) := by
  classical
  let ρ := fun k R => E.eval k (relabelSystem η R)
  obtain ⟨T, V, ⟨r⟩, hV, f, hf⟩ := ResolutionFactorization.resolution_to_flatten_resolution P R hR
  obtain ⟨T', V', r', hV', hb, he⟩ :=
    OptimalResolutions.optimal_flatten_resolution E hE η P T r V hV
  have chosen (v : T'.val.Vertex) :
      ∃ W : System A (T'.val.graph.label v).1,
        IsResolution (Q (r'.vertex v)) W (r'.variableMap v) ∧
        ρ _ W = ρ _ (T'.val.graph.label v).2 := by
    let e : ProfileEntry B (P.graph.label (r'.vertex v)).1 :=
      ⟨(T'.val.graph.label v).1, ρ _ (T'.val.graph.label v).2, r'.variableMap v⟩
    have hh : e ∈ Lax369799.FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1) ρ
        (Inner P (r'.vertex v)) := ⟨⟨(T'.val.graph.label v).2, r'.resolves v, rfl⟩, hb v⟩
    rw [hQ] at hh
    exact hh.1
  let label' := fun v => Classical.choose (chosen v)
  have hr (v) := (Classical.choose_spec (chosen v)).1
  have heval (v) := (Classical.choose_spec (chosen v)).2
  let T'' : System (System A) 0 := ⟨withLabels T'.val label', T'.property⟩
  let r'' : FlattenResolution (withLabels P Q) T'' := {
    vertex := r'.vertex
    variableMap := r'.variableMap
    initial := r'.initial
    resolves := hr
    transition := r'.transition
    exit := r'.exit }
  obtain ⟨U, hU⟩ := Flattening.flatten_system T''
  refine ⟨U, Flattening.flatten_resolution_sound _ T'' r'' U hU, ?_⟩
  have hlabels : relabelSystem ρ T'' = relabelSystem ρ T' :=
    Subtype.ext (same_evaluated_labels T' ρ label' heval)
  have flat (W : System (System A) 0) (X : System A 0) (hX : SystemFlattening W X) :
      E.eval 0 (relabelSystem ρ W) = ρ 0 X := by
    let WB := relabelSystem (fun _ X => relabelSystem η X) W
    have hh : SystemFlattening WB (relabelSystem η X) := by
      change relabel η X.val = _
      rw [hX]
      rfl
    exact E.associative 0 WB (relabelSystem η X) hh
  calc
    ρ 0 R = ρ 0 V := (value_morphism E hE η V R f).symm
    _ = ρ 0 V' := he
    _ = E.eval 0 (relabelSystem ρ T') := (flat T' V' hV').symm
    _ = E.eval 0 (relabelSystem ρ T'') := congrArg (E.eval 0) hlabels.symm
    _ = ρ 0 U := flat T'' U hU

end Lax369799Proofs.ProfileSubstitution
