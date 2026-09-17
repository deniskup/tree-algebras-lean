import Lax369799.OptimalResolutions
import Lax369799Proofs.CompressionEvaluation
import Lax369799Proofs.VertexContexts

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.OptimalResolutions
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.Renaming Lax369799.Resolutions
open Lax369799.OptimalResolutions
open Lax369799.ResolutionCompression Lax369799.SystemEvaluation Lax369799.VertexContexts
open Lax369799Proofs.Pullbacks

abbrev Maps {A : RankedSet} {n : ℕ} (T : System (System A) n) (v : T.val.Vertex) :=
  (m : ℕ) × (Fin (T.val.graph.label v).1 → Fin m) × (Fin m → Fin (T.val.graph.label v).1)

def identityMaps {A : RankedSet} {n : ℕ} (T : System (System A) n) (v : T.val.Vertex) : Maps T v :=
  ⟨(T.val.graph.label v).1, id, id⟩

noncomputable def localMaps {A : RankedSet} {n : ℕ} (T : System (System A) n) (v : T.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.graph.label v).1) : ∀ w, Maps T w := by
  classical
  exact Function.update (identityMaps T) v ⟨m, τ, sectionMap⟩

noncomputable def localBack {A : RankedSet} {n : ℕ} (T : System (System A) n) (v : T.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.graph.label v).1) :=
  backPresentation T (fun w => (localMaps T v m τ sectionMap w).1)
    (fun w => (localMaps T v m τ sectionMap w).2.1)
    (fun w => (localMaps T v m τ sectionMap w).2.2)

private theorem back_at {A : RankedSet} {n : ℕ} (T : System (System A) n) (v : T.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.graph.label v).1) :
    (localBack T v m τ sectionMap).label v =
      ⟨(T.val.graph.label v).1, renameSystem (sectionMap ∘ τ) (T.val.graph.label v).2⟩ := by
  have hdata : localMaps T v m τ sectionMap v = ⟨m, τ, sectionMap⟩ := Function.update_self ..
  exact congrArg (fun c : Maps T v => (⟨(T.val.graph.label v).1,
    renameSystem (c.2.2 ∘ c.2.1) (T.val.graph.label v).2⟩ : Symbol (System A))) hdata

private theorem back_other {A : RankedSet} {n : ℕ} (T : System (System A) n) (v w : T.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.graph.label v).1) (h : w ≠ v) :
    (localBack T v m τ sectionMap).label w = T.val.graph.label w := by
  have hdata : localMaps T v m τ sectionMap w = identityMaps T w := by
    exact Function.update_of_ne h _ _
  have hh := congrArg (fun c : Maps T w => (⟨(T.val.graph.label w).1,
    renameSystem (c.2.2 ∘ c.2.1) (T.val.graph.label w).2⟩ : Symbol (System A))) hdata
  apply hh.trans
  have he : renameSystem id (T.val.graph.label w).2 = (T.val.graph.label w).2 :=
    Subtype.ext (Renaming.rename_identity _)
  change (⟨(T.val.graph.label w).1, renameSystem id (T.val.graph.label w).2⟩ : Symbol (System A)) = _
  rw [he]

private theorem fill_at {A : RankedSet} {n : ℕ} (S : System A n) (v : S.val.Vertex)
    (b : A (S.val.graph.label v).1) :
    (relabel (fillLetter b) (atVertex S v).system).graph.label v = ⟨(S.val.graph.label v).1, b⟩ := by
  classical
  simp [relabel, atVertex, fillLetter]

private theorem fill_other {A : RankedSet} {n : ℕ} (S : System A n) (v w : S.val.Vertex)
    (b : A (S.val.graph.label v).1) (h : w ≠ v) :
    (relabel (fillLetter b) (atVertex S v).system).graph.label w = S.val.graph.label w := by
  classical
  simp [relabel, atVertex, fillLetter, h]

theorem back_comparison {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E) {n : ℕ}
    (T : System (System A) n) (v : T.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.graph.label v).1)
    (U : System (System A) n) (hU : U.val = trim (localBack T v m τ sectionMap)) :
    E.eval n (relabelSystem E.eval U) = E.eval n
      (relabelSystem (fillLetter (E.eval _ (renameSystem (sectionMap ∘ τ) (T.val.graph.label v).2)))
        ⟨(atVertex (relabelSystem E.eval T) v).system,
          VertexContexts.deterministic (relabelSystem E.eval T) v⟩) := by
  classical
  let D := relabelSystem E.eval T
  let b := E.eval _ (renameSystem (sectionMap ∘ τ) (T.val.graph.label v).2)
  let Q := relabelSystem (fillLetter b)
    ⟨(atVertex D v).system, VertexContexts.deterministic D v⟩
  let ev : Symbol (System A) → Symbol A := fun q => ⟨q.1, E.eval q.1 q.2⟩
  have hl (w : T.val.Vertex) : Q.val.graph.label w = ev ((localBack T v m τ sectionMap).label w) := by
    by_cases hw : w = v
    · subst w
      exact (fill_at D v b).trans (congrArg ev (back_at T v m τ sectionMap)).symm
    · exact (fill_other D v w b hw).trans (congrArg ev (back_other T v w m τ sectionMap hw)).symm
  have f : Lax369799.Morphisms.Morphism (relabelSystem E.eval U).val Q.val := by
    change Lax369799.Morphisms.Morphism (relabel E.eval U.val) Q.val
    rw [hU]
    exact {
      toFun := vertex (localBack T v m τ sectionMap)
      label := fun w => hl _
      initial := fun w h => h
      root := fun w h => h
      edge := fun w d t h => h }
  exact hE n (relabelSystem E.eval U) Q ⟨(relabelSystem E.eval U).val,
    ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
    ⟨f, MorphismTheorems.system_morphism_locally_surjective _ _ f⟩⟩

theorem value_step {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E) [Finite (B 1)]
    (η : RankedMap A B) (T : System (System A) 0) (v : T.val.Vertex) {n : ℕ}
    (σ : Fin (T.val.graph.label v).1 → Fin n) :
    ∃ (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
      (sectionMap : Fin m → Fin (T.val.graph.label v).1),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card (B 1) + 1) ∧
      E.eval 0 (relabelSystem (fun r S => E.eval r (relabelSystem η S)) T) =
        E.eval 0 (relabelSystem (fun r S => E.eval r (relabelSystem η S))
          (ResolutionCompression.compressedSystem T
            (fun w => (localMaps T v m τ sectionMap w).1)
            (fun w => (localMaps T v m τ sectionMap w).2.1)
            (fun w => (localMaps T v m τ sectionMap w).2.2))) := by
  let ρ := fun r S => E.eval r (relabelSystem η S)
  let D := relabelSystem ρ T
  obtain ⟨m, τ, sectionMap, hs, hσ, hb, Q, hQ, heQ⟩ := VertexContexts.smallification E hE D v σ
  let TB := relabelSystem (fun _ S => relabelSystem η S) T
  let c := localMaps T v m τ sectionMap
  obtain ⟨U, V, hU, hV, he⟩ := CompressionEvaluation.evaluation E hE TB
    (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2)
  have hc := back_comparison E hE TB v m τ sectionMap U hU
  have hfilled : relabelSystem
      (fillLetter (E.eval _ (renameSystem (sectionMap ∘ τ) (TB.val.graph.label v).2)))
      ⟨(atVertex (relabelSystem E.eval TB) v).system,
        VertexContexts.deterministic (relabelSystem E.eval TB) v⟩ = Q := by
    apply Subtype.ext
    change relabel (fillLetter (E.eval _ (renameSystem (sectionMap ∘ τ) (TB.val.graph.label v).2)))
      (atVertex (relabelSystem E.eval TB) v).system = Q.val
    rw [SystemEvaluation.rename_evaluation E hE]
    exact hQ.symm
  have hc' : E.eval 0 (relabelSystem E.eval U) = E.eval 0 Q :=
    hc.trans (congrArg (E.eval 0) hfilled)
  refine ⟨m, τ, sectionMap, hs, hσ, hb, ?_⟩
  have hv : relabelSystem ρ (ResolutionCompression.compressedSystem T
        (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2)) =
      relabelSystem E.eval V := by
    apply Subtype.ext
    change relabel ρ (trim (compressedPresentation T
      (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2))) = relabel E.eval V.val
    rw [hV]
    rfl
  change E.eval 0 D = E.eval 0 (relabelSystem ρ (ResolutionCompression.compressedSystem T
    (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2)))
  rw [hv]
  exact heQ.trans (hc'.symm.trans he)

private def afterSmall {A : RankedSet} {n : ℕ} {S : SetSystem (SetSystem A) n}
    {T : System (System A) n} (r : FlattenResolution S T) (bound : ℕ)
    (w : T.val.Vertex) (c : Maps T w) : Prop :=
  BoundedMap bound (fun i => r.variableMap w (c.2.2 i))

private theorem local_factor {A : RankedSet} {n : ℕ} {S : SetSystem (SetSystem A) n}
    (T : System (System A) n) (r : FlattenResolution S T) (v : T.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.graph.label v).1)
    (hσ : ∀ i, r.variableMap v (sectionMap (τ i)) = r.variableMap v i) :
    ∀ w i, r.variableMap w ((localMaps T v m τ sectionMap w).2.2
      ((localMaps T v m τ sectionMap w).2.1 i)) = r.variableMap w i := by
  intro w i
  by_cases hw : w = v
  · subst w
    have hdata : localMaps T v m τ sectionMap v = ⟨m, τ, sectionMap⟩ := Function.update_self ..
    have he := congrArg (fun c : Maps T v => r.variableMap v (c.2.2 (c.2.1 i))) hdata
    exact he.trans (hσ i)
  · have hdata : localMaps T v m τ sectionMap w = identityMaps T w := Function.update_of_ne hw _ _
    exact congrArg (fun c : Maps T w => r.variableMap w (c.2.2 (c.2.1 i))) hdata

private theorem after_good {A : RankedSet} {n : ℕ} {S : SetSystem (SetSystem A) n}
    (T : System (System A) n) (r : FlattenResolution S T) (v : T.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.graph.label v).1) (bound : ℕ)
    (hb : BoundedMap bound (fun i => r.variableMap v (sectionMap i))) (w : T.val.Vertex) :
    ¬ afterSmall r bound w (localMaps T v m τ sectionMap w) →
      w ≠ v ∧ ¬ BoundedMap bound (r.variableMap w) := by
  intro hn
  by_cases hw : w = v
  · subst w
    have hdata : localMaps T v m τ sectionMap v = ⟨m, τ, sectionMap⟩ := Function.update_self ..
    exact False.elim (hn (Eq.mpr (congrArg (afterSmall r bound v) hdata) hb))
  · refine ⟨hw, ?_⟩
    intro hh
    have hdata : localMaps T v m τ sectionMap w = identityMaps T w := Function.update_of_ne hw _ _
    exact hn (Eq.mpr (congrArg (afterSmall r bound w) hdata) hh)

noncomputable def badCount {A : RankedSet} {n : ℕ} {S : SetSystem (SetSystem A) n}
    {T : System (System A) n} (r : FlattenResolution S T) (bound : ℕ) : ℕ :=
  Nat.card {v : T.val.Vertex // ¬ BoundedMap bound (r.variableMap v)}

private theorem count_decreases {A : RankedSet} {n : ℕ} {S : SetSystem (SetSystem A) n}
    (T : System (System A) n) (r : FlattenResolution S T) (v : T.val.Vertex)
    (m : ℕ) (τ : Fin (T.val.graph.label v).1 → Fin m)
    (sectionMap : Fin m → Fin (T.val.graph.label v).1)
    (hσ : ∀ i, r.variableMap v (sectionMap (τ i)) = r.variableMap v i) (bound : ℕ)
    (hb : BoundedMap bound (fun i => r.variableMap v (sectionMap i)))
    (hv : ¬ BoundedMap bound (r.variableMap v)) :
    badCount (ResolutionCompression.compressedResolution S T r
      (fun w => (localMaps T v m τ sectionMap w).1)
      (fun w => (localMaps T v m τ sectionMap w).2.1)
      (fun w => (localMaps T v m τ sectionMap w).2.2)
      (local_factor T r v m τ sectionMap hσ)) bound < badCount r bound := by
  classical
  let c := localMaps T v m τ sectionMap
  let G := compressedPresentation T (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2)
  let U := ResolutionCompression.compressedSystem T
    (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2)
  let r' := ResolutionCompression.compressedResolution S T r
    (fun w => (c w).1) (fun w => (c w).2.1) (fun w => (c w).2.2)
    (local_factor T r v m τ sectionMap hσ)
  let X := {w : U.val.Vertex // ¬ BoundedMap bound (r'.variableMap w)}
  let Y := {w : T.val.Vertex // ¬ BoundedMap bound (r.variableMap w)}
  have hw (w : X) : vertex G w.val ≠ v ∧ ¬ BoundedMap bound (r.variableMap (vertex G w.val)) :=
    after_good T r v m τ sectionMap bound hb (vertex G w.val) w.property
  let f : X → Y := fun w => ⟨vertex G w.val, (hw w).2⟩
  have hf : Function.Injective f := by
    intro a b h
    have hval : vertex G a.val = vertex G b.val := congrArg (fun y : Y => y.val) h
    have hi : (index G).symm a.val = (index G).symm b.val := Subtype.ext hval
    exact Subtype.ext ((index G).symm.injective hi)
  have hn : (⟨v, hv⟩ : Y) ∉ Set.range f := by
    rintro ⟨w, he⟩
    exact (hw w).1 (congrArg Subtype.val he)
  have hc := Fintype.card_lt_of_injective_of_notMem f hf hn
  change Nat.card X < Nat.card Y
  simpa only [Nat.card_eq_fintype_card] using hc

theorem optimal {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E) [Finite (B 1)]
    (η : RankedMap A B) (S : SetSystem (SetSystem A) 0)
    (T : System (System A) 0) (r : FlattenResolution S T) :
    ∃ U : System (System A) 0, ∃ r' : FlattenResolution S U,
      (∀ v, BoundedMap (Nat.card (B 1) + 1) (r'.variableMap v)) ∧
      E.eval 0 (relabelSystem (fun k P => E.eval k (relabelSystem η P)) T) =
        E.eval 0 (relabelSystem (fun k P => E.eval k (relabelSystem η P)) U) := by
  classical
  let bound := Nat.card (B 1) + 1
  let ρ := fun k P => E.eval k (relabelSystem η P)
  let Goal := fun T : System (System A) 0 =>
    ∃ U : System (System A) 0, ∃ r' : FlattenResolution S U,
      (∀ v, BoundedMap bound (r'.variableMap v)) ∧ E.eval 0 (relabelSystem ρ T) = E.eval 0 (relabelSystem ρ U)
  have main : ∀ c, ∀ T : System (System A) 0, ∀ r : FlattenResolution S T,
      badCount r bound = c → Goal T := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro T r hc
      by_cases hall : ∀ v, BoundedMap bound (r.variableMap v)
      · exact ⟨T, r, hall, rfl⟩
      obtain ⟨v, hv⟩ := not_forall.mp hall
      obtain ⟨m, τ, sectionMap, _, hσ, hb, he⟩ := value_step E hE η T v (r.variableMap v)
      let data := localMaps T v m τ sectionMap
      let U := ResolutionCompression.compressedSystem T
        (fun w => (data w).1) (fun w => (data w).2.1) (fun w => (data w).2.2)
      let r' := ResolutionCompression.compressedResolution S T r
        (fun w => (data w).1) (fun w => (data w).2.1) (fun w => (data w).2.2)
        (local_factor T r v m τ sectionMap hσ)
      have hlt : badCount r' bound < c :=
        (count_decreases T r v m τ sectionMap hσ bound hb hv).trans_eq hc
      obtain ⟨V, rV, hV, eV⟩ := ih (badCount r' bound) hlt U r' rfl
      exact ⟨V, rV, hV, he.trans eV⟩
  exact main _ T r rfl

private theorem flatten_value {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
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
conclusion: Lax369799.OptimalResolutions.optimal_flatten_resolution
---
Compress one oversized local variable map at a time. Context smallification
preserves the outer algebra value, and the compression construction preserves
the flatten-resolution. The number of oversized vertices strictly decreases.
Associativity identifies the outer evaluations with the flattened values.
-/
theorem optimal_flatten_resolution {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) (S : SetSystem (SetSystem A) 0)
    (T : System (System A) 0) (r : FlattenResolution S T)
    (R : System A 0) (hR : Lax369799.Flattening.SystemFlattening T R) :
    ∃ (U : System (System A) 0) (V : System A 0) (r' : FlattenResolution S U),
      Lax369799.Flattening.SystemFlattening U V ∧
      (∀ v, BoundedMap (Nat.card (B 1) + 1) (r'.variableMap v)) ∧
      E.eval 0 (relabelSystem η R) = E.eval 0 (relabelSystem η V) := by
  obtain ⟨U, r', hb, he⟩ := optimal E hE η S T r
  obtain ⟨V, hV⟩ := Flattening.flatten_system U
  exact ⟨U, V, r', hV, hb, (flatten_value E η T R hR).symm.trans
    (he.trans (flatten_value E η U V hV))⟩

end Lax369799Proofs.OptimalResolutions
