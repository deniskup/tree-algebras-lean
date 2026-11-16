import Lax369799.SupportedResolutions
import Lax369799Proofs.SupportedYieldComparison
import Lax369799Proofs.SupportedCompletionProperties
import Lax369799Proofs.OptimalResolutions

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedResolutions
open Lax369799
open RankedSystems FinitePresentations
open Lax369799.SupportedResolutions
open Lax369799.ResolutionCompression Lax369799.Resolutions Lax369799.OptimalResolutions
open Lax369799Proofs.OptimalResolutions
open Lax369799Proofs.Pullbacks

private def supportify {A : RankedSet} (T : System (System A) 0)
    (h : ∀ v, SupportedSystems.FullySupported (T.val.graph.label v).2) :
    SupportedSystems.System (SupportedSystems.System A) 0 :=
  ⟨⟨ProfileSubstitution.withLabels T.val (fun v => ⟨(T.val.graph.label v).2,h v⟩),
    T.property⟩,fun i => Fin.elim0 i⟩

private theorem yield_factor {A : RankedSet} {k m n : ℕ}
    (S : FiniteSystem A n) (T : SupportedSystems.System A k)
    (σ : Fin k → Fin n) (τ : Fin k → Fin m) (ht : Function.Surjective τ)
    (σ' : Fin m → Fin n) (he : ∀ i, σ' (τ i) = σ i)
    (h : SupportedYields.InitialYield S T σ) :
    SupportedYields.InitialYield S (SupportedSystems.rename τ ht T) σ' := by
  apply (SupportedYieldComparison.initial_yield _ _ _).mpr
  have hr : Renaming.renameSystem σ' (Renaming.renameSystem τ T.val) =
      Renaming.renameSystem σ T.val := by
    apply Subtype.ext
    exact (Renaming.rename_composition τ σ' T.val.val).trans
      (congrArg (fun f => Resolutions.rename f T.val.val) (funext he))
  change Morphisms.InitYield (trim S.graph) (Renaming.renameSystem σ' (Renaming.renameSystem τ T.val))
  rw [hr]
  exact (SupportedYieldComparison.initial_yield S T σ).mp h

private noncomputable def compressed {A : RankedSet}
    (T : SupportedSystems.System (SupportedSystems.System A) 0)
    (arity : T.val.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.val.graph.label v).1 → Fin (arity v))
    (s : ∀ v, Fin (arity v) → Fin (T.val.val.graph.label v).1)
    (ht : ∀ v, Function.Surjective (τ v)) :
    SupportedSystems.System (SupportedSystems.System A) 0 := by
  let T₀ := SupportedSystems.forgetPattern T
  let G := compressedPresentation T₀ arity τ s
  let U := ResolutionCompression.compressedSystem T₀ arity τ s
  exact supportify U (fun w => (SupportedSystems.rename (τ (vertex G w))
    (ht (vertex G w)) (T.val.val.graph.label (vertex G w)).2).property)

private noncomputable def compressedResolution {A : RankedSet}
    (S : FiniteSystem (FiniteSystem A) 0)
    (T : SupportedSystems.System (SupportedSystems.System A) 0) (r : Resolution S T Fin.elim0)
    (arity : T.val.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.val.graph.label v).1 → Fin (arity v))
    (s : ∀ v, Fin (arity v) → Fin (T.val.val.graph.label v).1)
    (ht : ∀ v, Function.Surjective (τ v))
    (he : ∀ v i, r.variableMap v (s v (τ v i)) = r.variableMap v i) :
    Resolution S (compressed T arity τ s ht) Fin.elim0 where
  vertex := fun v => r.vertex (vertex (compressedPresentation (SupportedSystems.forgetPattern T) arity τ s) (by exact v))
  variableMap := fun v i => r.variableMap
    (vertex (compressedPresentation (SupportedSystems.forgetPattern T) arity τ s) (by exact v))
    (s (vertex (compressedPresentation (SupportedSystems.forgetPattern T) arity τ s) (by exact v)) (by exact i))
  initial := by intro v hv; exact r.initial _ hv
  resolves := by
    intro v
    let w := vertex (compressedPresentation (SupportedSystems.forgetPattern T) arity τ s) (by exact v)
    exact yield_factor (FinitePresentations.Inner S.graph (r.vertex w))
      (T.val.val.graph.label w).2 (r.variableMap w) (τ w) (ht w)
      (r.variableMap w ∘ s w) (he w) (r.resolves w)
  transition := by
    intro v i w h
    let v' := vertex (compressedPresentation (SupportedSystems.forgetPattern T) arity τ s) (by exact v)
    let w' := vertex (compressedPresentation (SupportedSystems.forgetPattern T) arity τ s) (by exact w)
    obtain ⟨j,he,hj⟩ := h
    have he : j = (show Fin (arity v') from i) := Fin.ext he.symm
    subst j
    exact r.transition v' (s v' i) w' hj
  exit := by intro v i j; exact Fin.elim0 j

private theorem local_surjective {A : RankedSet}
    (T : System (System A) 0) (v : T.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
    (s : Fin m → Fin (T.val.graph.label v).1) (hs : ∀ j,τ (s j) = j) :
    ∀ w, Function.Surjective (localMaps T v m τ s w).2.1 := by
  intro w
  by_cases hw : w = v
  · subst w
    have hdata : localMaps T v m τ s v = ⟨m,τ,s⟩ := Function.update_self ..
    exact Eq.mpr (congrArg (fun c : Maps T v => Function.Surjective c.2.1) hdata)
      (fun j => ⟨s j,hs j⟩)
  · have hdata : localMaps T v m τ s w = identityMaps T w := Function.update_of_ne hw _ _
    exact Eq.mpr (congrArg (fun c : Maps T w => Function.Surjective c.2.1) hdata)
      Function.surjective_id

private def afterSmall {A : RankedSet} {S : FiniteSystem (FiniteSystem A) 0}
    {T : SupportedSystems.System (SupportedSystems.System A) 0} (r : Resolution S T Fin.elim0) (bound : ℕ)
    (w : T.val.val.Vertex) (c : Maps (SupportedSystems.forgetPattern T) w) : Prop :=
  BoundedMap bound (fun i => r.variableMap w (c.2.2 i))

private theorem local_factor {A : RankedSet} {S : FiniteSystem (FiniteSystem A) 0}
    (T : SupportedSystems.System (SupportedSystems.System A) 0) (r : Resolution S T Fin.elim0) (v : T.val.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.val.graph.label v).1)
    (hσ : ∀ i, r.variableMap v (sectionMap (τ i)) = r.variableMap v i) :
    ∀ w i, r.variableMap w ((localMaps (SupportedSystems.forgetPattern T) v m τ sectionMap w).2.2
      ((localMaps (SupportedSystems.forgetPattern T) v m τ sectionMap w).2.1 i)) = r.variableMap w i := by
  intro w i
  by_cases hw : w = v
  · subst w
    have hdata : localMaps (SupportedSystems.forgetPattern T) v m τ sectionMap v = ⟨m, τ, sectionMap⟩ := Function.update_self ..
    have he := congrArg (fun c : Maps (SupportedSystems.forgetPattern T) v => r.variableMap v (c.2.2 (c.2.1 i))) hdata
    exact he.trans (hσ i)
  · have hdata : localMaps (SupportedSystems.forgetPattern T) v m τ sectionMap w = identityMaps (SupportedSystems.forgetPattern T) w := Function.update_of_ne hw _ _
    exact congrArg (fun c : Maps (SupportedSystems.forgetPattern T) w => r.variableMap w (c.2.2 (c.2.1 i))) hdata

private theorem after_good {A : RankedSet} {S : FiniteSystem (FiniteSystem A) 0}
    (T : SupportedSystems.System (SupportedSystems.System A) 0) (r : Resolution S T Fin.elim0) (v : T.val.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.val.graph.label v).1) (bound : ℕ)
    (hb : BoundedMap bound (fun i => r.variableMap v (sectionMap i))) (w : T.val.val.Vertex) :
    ¬ afterSmall r bound w (localMaps (SupportedSystems.forgetPattern T) v m τ sectionMap w) →
      w ≠ v ∧ ¬ BoundedMap bound (r.variableMap w) := by
  intro hn
  by_cases hw : w = v
  · subst w
    have hdata : localMaps (SupportedSystems.forgetPattern T) v m τ sectionMap v = ⟨m, τ, sectionMap⟩ := Function.update_self ..
    exact False.elim (hn (Eq.mpr (congrArg (afterSmall r bound v) hdata) hb))
  · refine ⟨hw, ?_⟩
    intro hh
    have hdata : localMaps (SupportedSystems.forgetPattern T) v m τ sectionMap w = identityMaps (SupportedSystems.forgetPattern T) w := Function.update_of_ne hw _ _
    exact hn (Eq.mpr (congrArg (afterSmall r bound w) hdata) hh)

noncomputable def badCount {A : RankedSet} {S : FiniteSystem (FiniteSystem A) 0}
    {T : SupportedSystems.System (SupportedSystems.System A) 0} (r : Resolution S T Fin.elim0) (bound : ℕ) : ℕ :=
  Nat.card {v : T.val.val.Vertex // ¬ BoundedMap bound (r.variableMap v)}

private theorem count_decreases {A : RankedSet} {S : FiniteSystem (FiniteSystem A) 0}
    (T : SupportedSystems.System (SupportedSystems.System A) 0) (r : Resolution S T Fin.elim0)
    (v : T.val.val.Vertex) (m : ℕ) (τ : Fin (T.val.val.graph.label v).1 → Fin m)
    (s : Fin m → Fin (T.val.val.graph.label v).1) (hs : ∀ j,τ (s j) = j)
    (hσ : ∀ i,r.variableMap v (s (τ i)) = r.variableMap v i) (bound : ℕ)
    (hb : BoundedMap bound (fun i => r.variableMap v (s i)))
    (hv : ¬ BoundedMap bound (r.variableMap v)) :
    badCount (compressedResolution S T r
      (fun w => (localMaps (SupportedSystems.forgetPattern T) v m τ s w).1)
      (fun w => (localMaps (SupportedSystems.forgetPattern T) v m τ s w).2.1)
      (fun w => (localMaps (SupportedSystems.forgetPattern T) v m τ s w).2.2)
      (local_surjective (SupportedSystems.forgetPattern T) v m τ s hs)
      (local_factor T r v m τ s hσ)) bound < badCount r bound := by
  classical
  let T₀ := SupportedSystems.forgetPattern T
  let c := localMaps T₀ v m τ s
  let G := compressedPresentation T₀ (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2)
  let U := compressed T (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2)
    (local_surjective T₀ v m τ s hs)
  let r' := compressedResolution S T r
    (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2)
    (local_surjective T₀ v m τ s hs) (local_factor T r v m τ s hσ)
  let X := {w : U.val.val.Vertex // ¬ BoundedMap bound (r'.variableMap w)}
  let Y := {w : T.val.val.Vertex // ¬ BoundedMap bound (r.variableMap w)}
  have hw (w : X) : vertex G (by exact w.val) ≠ v ∧
      ¬ BoundedMap bound (r.variableMap (vertex G (by exact w.val))) :=
    after_good T r v m τ s bound hb _ w.property
  let f : X → Y := fun w => ⟨vertex G (by exact w.val),(hw w).2⟩
  have hf : Function.Injective f := by
    intro a b h
    have hval : vertex G (by exact a.val) = vertex G (by exact b.val) := congrArg (fun y : Y => y.val) h
    exact Subtype.ext (Pullbacks.vertex_injective G hval)
  have hn : (⟨v,hv⟩ : Y) ∉ Set.range f := by
    rintro ⟨w,he⟩
    exact (hw w).1 (congrArg Subtype.val he)
  have hc := Fintype.card_lt_of_injective_of_notMem f hf hn
  change Nat.card X < Nat.card Y
  simpa only [Nat.card_eq_fintype_card] using hc

private theorem optimal {A B : RankedSet} (E : Algebras.Algebra B) (hE : Algebras.UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) (S : FiniteSystem (FiniteSystem A) 0)
    (T : SupportedSystems.System (SupportedSystems.System A) 0) (r : Resolution S T Fin.elim0)
    (bound : ℕ) (hbound : Nat.card (B 1) + 1 ≤ bound) :
    ∃ U : SupportedSystems.System (SupportedSystems.System A) 0, ∃ r' : Resolution S U Fin.elim0,
      (∀ v, BoundedMap bound (r'.variableMap v)) ∧
      E.eval 0 (relabelSystem (fun k P => E.eval k (relabelSystem η P)) (SupportedSystems.forgetPattern T)) =
        E.eval 0 (relabelSystem (fun k P => E.eval k (relabelSystem η P)) (SupportedSystems.forgetPattern U)) := by
  classical
  let ρ := fun k P => E.eval k (relabelSystem η P)
  let Goal := fun T : SupportedSystems.System (SupportedSystems.System A) 0 =>
    ∃ U : SupportedSystems.System (SupportedSystems.System A) 0, ∃ r' : Resolution S U Fin.elim0,
      (∀ v, BoundedMap bound (r'.variableMap v)) ∧
        E.eval 0 (relabelSystem ρ (SupportedSystems.forgetPattern T)) =
          E.eval 0 (relabelSystem ρ (SupportedSystems.forgetPattern U))
  have main : ∀ c, ∀ T : SupportedSystems.System (SupportedSystems.System A) 0,
      ∀ r : Resolution S T Fin.elim0, badCount r bound = c → Goal T := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro T r hc
      by_cases hall : ∀ v, BoundedMap bound (r.variableMap v)
      · exact ⟨T,r,hall,rfl⟩
      obtain ⟨v,hv⟩ := not_forall.mp hall
      let T₀ := SupportedSystems.forgetPattern T
      obtain ⟨m,τ,s,hs,hσ,hb,he⟩ := value_step E hE η T₀ v (r.variableMap v)
      have hb' : BoundedMap bound (fun i => r.variableMap v (s i)) :=
        fun j => (hb j).trans hbound
      let data := localMaps T₀ v m τ s
      let U := compressed T (fun w => (data w).1) (fun w => (data w).2.1)
        (fun w => (data w).2.2) (local_surjective T₀ v m τ s hs)
      let r' := compressedResolution S T r (fun w => (data w).1) (fun w => (data w).2.1)
        (fun w => (data w).2.2) (local_surjective T₀ v m τ s hs) (local_factor T r v m τ s hσ)
      have hlt : badCount r' bound < c :=
        (count_decreases T r v m τ s hs hσ bound hb' hv).trans_eq hc
      obtain ⟨V,rV,hV,eV⟩ := ih (badCount r' bound) hlt U r' rfl
      exact ⟨V,rV,hV,he.trans eV⟩
  exact main _ T r rfl

private theorem flatten_value {A B : RankedSet} (E : Algebras.Algebra B) (η : RankedMap A B)
    {n : ℕ} (T : System (System A) n) (R : System A n)
    (hR : Lax369799.Flattening.SystemFlattening T R) :
    E.eval n (relabelSystem (fun k P => E.eval k (relabelSystem η P)) T) =
      E.eval n (relabelSystem η R) := by
  let TB := relabelSystem (fun _ P => relabelSystem η P) T
  have hB : Lax369799.Flattening.SystemFlattening TB (relabelSystem η R) := by
    change relabel η R.val = _
    rw [hR]
    rfl
  exact E.associative n TB (relabelSystem η R) hB

/--
---
conclusion: Lax369799.SupportedResolutions.small_resolution
---
Extend the original supported algebra to arbitrary output presentations.
Compress one oversized local map at a time, retaining a representative
for each continuation observation. Surjective local renaming preserves
full support, and the number of oversized vertices strictly decreases.
The completed unary sort has at most |B₀| + |B₁| elements. Associativity
and the closed-sort equivalence return the original evaluation (Lemma 82).
-/
theorem small_resolution {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B)
    (S : FiniteSystem (FiniteSystem A) 0)
    (T : SupportedSystems.System (SupportedSystems.System A) 0) (r : Resolution S T Fin.elim0)
    (R : SupportedSystems.System A 0)
    (hR : Flattening.SystemFlattening (SupportedSystems.forgetPattern T) R.val) :
    ∃ (U : SupportedSystems.System (SupportedSystems.System A) 0)
      (V : SupportedSystems.System A 0) (r' : Resolution S U Fin.elim0),
      Flattening.SystemFlattening (SupportedSystems.forgetPattern U) V.val ∧
      (∀ v,SmallMap B (r'.variableMap v)) ∧
      E.eval 0 (SupportedSystems.relabel η R) = E.eval 0 (SupportedSystems.relabel η V) := by
  obtain ⟨D,hDE,hD⟩ := SupportedCompletion.regular_completion E hE
  let : Finite (SupportEvaluation.Carrier E 1) := SupportEvaluation.finite_carrier E hB 1
  let κ : RankedMap A (SupportEvaluation.Carrier E) := fun k a => SupportedCompletion.letter E k (η k a)
  have hbound : Nat.card (SupportEvaluation.Carrier E 1) + 1 ≤ SmallBound B := by
    have hn := SupportedCompletion.unary_card_bound E hB
    unfold SmallBound
    omega
  obtain ⟨U,r',hb,he⟩ := optimal D hDE κ S T r (SmallBound B) hbound
  obtain ⟨V,hV⟩ := SupportedSystems.flatten_system U
  have he' : D.eval 0 (relabelSystem κ R.val) = D.eval 0 (relabelSystem κ V.val) :=
    (flatten_value D κ (SupportedSystems.forgetPattern T) R.val hR).symm.trans
      (he.trans (flatten_value D κ (SupportedSystems.forgetPattern U) V.val hV))
  have hc : SupportEvaluation.classMap E 0 (relabelSystem η R.val) =
      SupportEvaluation.classMap E 0 (relabelSystem η V.val) :=
    (hD 0 (relabelSystem η R.val)).symm.trans (he'.trans (hD 0 (relabelSystem η V.val)))
  obtain ⟨e,hee⟩ := SupportEvaluation.closed_carrier E
  exact ⟨U,V,r',hV,hb,(hee (relabelSystem η R.val)).symm.trans
    ((congrArg e hc).trans (hee (relabelSystem η V.val)))⟩

end Lax369799Proofs.SupportedResolutions
