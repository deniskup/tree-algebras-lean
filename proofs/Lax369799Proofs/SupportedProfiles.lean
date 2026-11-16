import Lax369799.SupportedProfiles
import Lax369799Proofs.SupportedCompletionProperties
import Lax369799Proofs.PresentationObservations
import Lax369799Proofs.Renaming
import Lax369799Proofs.ResolutionLifting
import Lax369799Proofs.BoundedProfileRefinement
import Mathlib.Data.Finite.Sum

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedProfiles
open Lax369799
open RankedSystems FinitePresentations
open SupportedMorphisms FiniteRenaming
open SupportEvaluation (Carrier classMap)

private noncomputable def finite_resolution {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (R : System A m) (σ : Fin m → Fin n)
    (r : Morphisms.Morphism (Resolutions.rename σ R.val) (trim S.graph)) :
    FiniteMorphisms.Morphism (push σ (ofSetSystem R.val)) S := by
  let f := PresentationObservations.toPresentation r
  exact ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩

private noncomputable def legacy_resolution {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (R : System A m) (σ : Fin m → Fin n)
    (f : FiniteMorphisms.Morphism (push σ (ofSetSystem R.val)) S) :
    Morphisms.Morphism (Resolutions.rename σ R.val) (trim S.graph) :=
  Pullbacks.lift ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩

private theorem filter_forward {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) (D : Algebras.Algebra (Carrier E))
    (hD : ∀ n (R : System B n),
      D.eval n (relabelSystem (SupportedCompletion.letter E) R) = classMap E n R)
    {n : ℕ} (S T : FiniteSystem A n) (C : (m : ℕ) → (Fin m → Fin n) → Prop)
    (hC : ∀ m k (σ : Fin m → Fin n) (ι : Fin k → Fin m),
      Function.Injective ι → C m σ → C k (σ ∘ ι))
    (h : ∀ e, e ∈ Lax369799.SupportedProfiles.Profile E η S → C e.1 e.2.2 →
      e ∈ Lax369799.SupportedProfiles.Profile E η T) :
    {e | e ∈ Resolutions.Profile
      (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R))
      (trim S.graph) ∧ C e.1 e.2.2} ⊆
    {e | e ∈ Resolutions.Profile
      (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R))
      (trim T.graph) ∧ C e.1 e.2.2} := by
  rintro ⟨m,b,σ⟩ ⟨⟨R,⟨r⟩,hR⟩,hc⟩
  obtain ⟨k,ι,U,hι,hU⟩ := SupportCompaction.compact_exists R
  have hcomp : Resolutions.rename (σ ∘ ι) U.val.val = Resolutions.rename σ R.val := by
    rw [←congrArg Subtype.val hU]
    exact (Renaming.rename_composition ι σ U.val.val).symm
  have ru : Morphisms.Morphism (Resolutions.rename (σ ∘ ι) U.val.val) (trim S.graph) := by
    rw [hcomp]; exact r
  let a := E.eval k (SupportedSystems.relabel η U)
  have he : (⟨k,a,σ ∘ ι⟩ : Resolutions.ProfileEntry B n) ∈
      Lax369799.SupportedProfiles.Profile E η S := ⟨U,⟨finite_resolution S U.val _ ru⟩,rfl⟩
  obtain ⟨V,⟨v⟩,hv⟩ := h _ he (hC m k σ ι hι hc)
  let R' := Renaming.renameSystem ι V.val
  have rv := legacy_resolution T V.val (σ ∘ ι) v
  have r' : Morphisms.Morphism (Resolutions.rename σ R'.val) (trim T.graph) := by
    change Morphisms.Morphism (Resolutions.rename σ (Resolutions.rename ι V.val.val)) _
    rw [Renaming.rename_composition]
    exact rv
  have huη : Renaming.renameSystem ι (SupportedSystems.relabel η U).val = relabelSystem η R := by
    apply Subtype.ext
    exact (Renaming.rename_relabel η ι U.val.val).trans
      (congrArg (RankedSystems.relabel η) (congrArg Subtype.val hU))
  have hvη : Renaming.renameSystem ι (SupportedSystems.relabel η V).val = relabelSystem η R' :=
    Subtype.ext (Renaming.rename_relabel η ι V.val.val)
  have hclass : classMap E m (relabelSystem η R') = classMap E m (relabelSystem η R) :=
    Quot.sound ((SupportEvaluation.equivalent_iff E _ _).mpr
      ⟨k,ι,hι,SupportedSystems.relabel η V,SupportedSystems.relabel η U,hvη,huη,hv⟩)
  refine ⟨⟨R',⟨r'⟩,?_⟩,hc⟩
  exact (hD m (relabelSystem η R')).trans (hclass.trans ((hD m (relabelSystem η R)).symm.trans hR))

private theorem filtered_completion {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) (D : Algebras.Algebra (Carrier E))
    (hD : ∀ n (R : System B n),
      D.eval n (relabelSystem (SupportedCompletion.letter E) R) = classMap E n R)
    {n : ℕ} (S T : FiniteSystem A n) (C : (m : ℕ) → (Fin m → Fin n) → Prop)
    (hC : ∀ m k (σ : Fin m → Fin n) (ι : Fin k → Fin m),
      Function.Injective ι → C m σ → C k (σ ∘ ι))
    (h : {e | e ∈ Lax369799.SupportedProfiles.Profile E η S ∧ C e.1 e.2.2} =
      {e | e ∈ Lax369799.SupportedProfiles.Profile E η T ∧ C e.1 e.2.2}) :
    {e | e ∈ Resolutions.Profile
      (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R))
      (trim S.graph) ∧ C e.1 e.2.2} =
    {e | e ∈ Resolutions.Profile
      (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R))
      (trim T.graph) ∧ C e.1 e.2.2} := by
  apply Set.Subset.antisymm
  · exact filter_forward E η D hD S T C hC (fun e he hc => by
      have he' : e ∈ {e | e ∈ Lax369799.SupportedProfiles.Profile E η S ∧ C e.1 e.2.2} := ⟨he,hc⟩
      rw [h] at he'; exact he'.1)
  · exact filter_forward E η D hD T S C hC (fun e he hc => by
      have he' : e ∈ {e | e ∈ Lax369799.SupportedProfiles.Profile E η T ∧ C e.1 e.2.2} := ⟨he,hc⟩
      rw [←h] at he'; exact he'.1)


private theorem profiles_cover {A B : RankedSet} (D : Algebras.Algebra B)
    (hD : Algebras.UnfoldInvariant D) (η : RankedMap A B) {n : ℕ}
    {V W : Type} [Fintype V] [Fintype W] {G : Presentation A n V} {H : Presentation A n W}
    (f : PresentationCovers.Cover G H) :
    Resolutions.Profile (fun k R => D.eval k (relabelSystem η R)) (trim G) =
      Resolutions.Profile (fun k R => D.eval k (relabelSystem η R)) (trim H) := by
  let m : Pullbacks.Map G H := ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩
  let g := Pullbacks.trimMap m
  have hg := Pullbacks.trimMap_surjective m f.initial_lift f.root_lift f.edge_lift
  have he := (Yields.morphism_yields g).2 hg
  have forward (S T : SetSystem A n) (h : Morphisms.YieldBelow S T) :
      Resolutions.Profile (fun k R => D.eval k (relabelSystem η R)) S ⊆
        Resolutions.Profile (fun k R => D.eval k (relabelSystem η R)) T := by
    rintro ⟨k,b,σ⟩ ⟨R,hr,hb⟩
    obtain ⟨U,hu,⟨u,_⟩⟩ := ResolutionLifting.transfer h R σ hr
    exact ⟨U,hu,(ProfileSubstitution.value_morphism D hD η U R u).trans hb⟩
  exact Set.Subset.antisymm
    (forward _ _ (fun R h => (he R).mp h))
    (forward _ _ (fun R h => (he R).mpr h))

private theorem root_profiles {A B : RankedSet} (D : Algebras.Algebra B)
    (hD : Algebras.UnfoldInvariant D) (η : RankedMap A B) {n : ℕ} (S : FiniteSystem A n) :
    Resolutions.Profile (fun k R => D.eval k (relabelSystem η R)) (RankedSystems.uproot (trim S.graph)) =
      Resolutions.Profile (fun k R => D.eval k (relabelSystem η R))
        (trim (SupportedYields.uproot S).graph) :=
  profiles_cover D hD η (PresentationObservations.rootedCover (FiniteAcceptance.trimProjection S.graph))

/--
---
conclusion: Lax369799.SupportedProfiles.full_completion
---
Compact each legacy resolution along its used outputs. Equal supported
profiles supply a replacement with the same original value; restoring
the unused outputs gives the same completed value. Canonical trimming
covers transfer the root profiles.
-/
theorem full_completion {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) (D : Algebras.Algebra (Carrier E)) (hDE : Algebras.UnfoldInvariant D)
    (hD : ∀ n (R : System B n),
      D.eval n (relabelSystem (SupportedCompletion.letter E) R) = classMap E n R)
    {n : ℕ} (S T : FiniteSystem A n) (h : Lax369799.SupportedProfiles.ProfileEquivalent E η S T) :
    Resolutions.ProfileEquivalent
      (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R))
      (trim S.graph) (trim T.graph) := by
  have initial {n : ℕ} (S T : FiniteSystem A n)
      (he : Lax369799.SupportedProfiles.Profile E η S = Lax369799.SupportedProfiles.Profile E η T) :
      Resolutions.Profile
        (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R))
        (trim S.graph) = Resolutions.Profile
        (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R))
        (trim T.graph) := by
    have hf := filtered_completion E η D hD S T (fun _ _ => True)
      (fun _ _ _ _ _ _ => trivial) (by simpa only [and_true,Set.ofPred_mem_eq] using he)
    simpa only [and_true,Set.ofPred_mem_eq] using hf
  refine ⟨initial S T h.1,?_⟩
  rw [root_profiles D hDE,root_profiles D hDE]
  exact initial _ _ h.2

private theorem bounded_restrict {m k n c : ℕ} (σ : Fin m → Fin n) (ι : Fin k → Fin m)
    (hι : Function.Injective ι) (h : ∀ j, Nat.card {i // σ i = j} ≤ c) :
    ∀ j, Nat.card {i // σ (ι i) = j} ≤ c := by
  classical
  intro j
  let f : {i // σ (ι i) = j} → {i // σ i = j} := fun i => ⟨ι i.val,i.property⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (hι (congrArg Subtype.val h))
  exact (Nat.card_le_card_of_injective f hf).trans (h j)

private theorem restrict_small {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) {n c : ℕ} (S T : FiniteSystem A n)
    (hc : c ≤ Resolutions.SmallBound B)
    (h : Lax369799.SupportedProfiles.SmallProfile E η S =
      Lax369799.SupportedProfiles.SmallProfile E η T) :
    {e | e ∈ Lax369799.SupportedProfiles.Profile E η S ∧ ∀ j, Nat.card {i // e.2.2 i = j} ≤ c} =
      {e | e ∈ Lax369799.SupportedProfiles.Profile E η T ∧ ∀ j, Nat.card {i // e.2.2 i = j} ≤ c} := by
  have forward (S T : FiniteSystem A n)
      (h : Lax369799.SupportedProfiles.SmallProfile E η S = Lax369799.SupportedProfiles.SmallProfile E η T) :
      {e | e ∈ Lax369799.SupportedProfiles.Profile E η S ∧ ∀ j, Nat.card {i // e.2.2 i = j} ≤ c} ⊆
        {e | e ∈ Lax369799.SupportedProfiles.Profile E η T ∧ ∀ j, Nat.card {i // e.2.2 i = j} ≤ c} := by
    rintro e ⟨he,hb⟩
    have hs : e ∈ Lax369799.SupportedProfiles.SmallProfile E η S :=
      ⟨he,fun j => (hb j).trans hc⟩
    rw [h] at hs
    exact ⟨hs.1,hb⟩
  exact Set.Subset.antisymm (forward S T h) (forward T S h.symm)

/--
---
conclusion: Lax369799.SupportedProfiles.small_completion
---
The unary completion bound makes its legacy cutoff at most the original
small-map bound. Injective support restriction only reduces fibre sizes.
Apply the filtered profile transfer to initial and root observations.
-/
theorem small_completion {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (η : RankedMap A B) (D : Algebras.Algebra (Carrier E))
    (hDE : Algebras.UnfoldInvariant D)
    (hD : ∀ n (R : System B n),
      D.eval n (relabelSystem (SupportedCompletion.letter E) R) = classMap E n R)
    {n : ℕ} (S T : FiniteSystem A n) (h : Lax369799.SupportedProfiles.SmallProfileEquivalent E η S T) :
    FiniteProfiles.BoundedProfileEquivalent (Nat.card (Carrier E 1) + 1)
      (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R)) S T := by
  have hc : Nat.card (Carrier E 1) + 1 ≤ Resolutions.SmallBound B := by
    have hn := SupportedCompletion.unary_card_bound E hB
    unfold Resolutions.SmallBound
    omega
  let C := fun m (σ : Fin m → Fin n) => ∀ j, Nat.card {i // σ i = j} ≤ Nat.card (Carrier E 1) + 1
  have hC : ∀ m k (σ : Fin m → Fin n) (ι : Fin k → Fin m),
      Function.Injective ι → C m σ → C k (σ ∘ ι) :=
    fun _ _ σ ι hi hb => bounded_restrict σ ι hi hb
  constructor
  · exact filtered_completion E η D hD S T C hC (restrict_small E η S T hc h.1)
  · change {e | e ∈ Resolutions.Profile _ (RankedSystems.uproot (trim S.graph)) ∧ C e.1 e.2.2} =
      {e | e ∈ Resolutions.Profile _ (RankedSystems.uproot (trim T.graph)) ∧ C e.1 e.2.2}
    rw [root_profiles D hDE,root_profiles D hDE]
    exact filtered_completion E η D hD _ _ C hC (restrict_small E η _ _ hc h.2)

private theorem recognizes_completion {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) (F : Set (B 0)) (L : Algebras.Language A)
    (hL : SupportedAlgebras.Recognizes E η F L) (D : Algebras.Algebra (Carrier E))
    (hD : ∀ n (R : System B n),
      D.eval n (relabelSystem (SupportedCompletion.letter E) R) = classMap E n R) :
    ∃ F' : Set (Carrier E 0), Algebras.Recognizes D
      (fun j a => SupportedCompletion.letter E j (η j a)) F' L := by
  obtain ⟨e,he⟩ := SupportEvaluation.closed_carrier E
  refine ⟨{c | e c ∈ F},?_⟩
  intro S
  have hv := hD 0 (relabelSystem η S)
  change S ∈ L ↔ e (D.eval 0 (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) S)) ∈ F
  change D.eval 0 (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) S) = _ at hv
  rw [hv,he]
  exact hL ((SupportedSystems.closedEquiv A).symm S)

/--
---
conclusion: Lax369799.SupportedProfiles.full_refines
---
Use an unfolding-invariant completion and its recognizing closed values.
Full supported profiles determine the completed bounded profiles, which
determine every unpruned closed contextual test.
-/
theorem full_refines {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E)
    (η : RankedMap A B) (F : Set (B 0)) (L : Algebras.Language A)
    (hL : SupportedAlgebras.Recognizes E η F L) {n : ℕ} (S T : FiniteSystem A n)
    (h : Lax369799.SupportedProfiles.ProfileEquivalent E η S T) :
    FiniteContextualOrder.Equivalent (FiniteAcceptance.Accepting L) S T := by
  obtain ⟨D,hDE,hD⟩ := SupportedCompletion.regular_completion E hE
  obtain ⟨F',hrec⟩ := recognizes_completion E η F L hL D hD
  let : Finite (Carrier E 1) := SupportEvaluation.finite_carrier E hB 1
  have hp := full_completion E η D hDE hD S T h
  apply BoundedProfileRefinement.refines D hDE _ F' L hrec S T
  constructor
  · unfold FiniteProfiles.BoundedProfile; rw [hp.1]
  · unfold FiniteProfiles.BoundedProfile; rw [hp.2]

/--
---
conclusion: Lax369799.SupportedProfiles.small_refines
---
Complete the supported algebra without increasing the unary cutoff
beyond |B₀| + |B₁| + 1. Equal supported small profiles therefore determine
every closed contextual test (Corollary 84).
-/
theorem small_refines {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E)
    (η : RankedMap A B) (F : Set (B 0)) (L : Algebras.Language A)
    (hL : SupportedAlgebras.Recognizes E η F L) {n : ℕ} (S T : FiniteSystem A n)
    (h : Lax369799.SupportedProfiles.SmallProfileEquivalent E η S T) :
    FiniteContextualOrder.Equivalent (FiniteAcceptance.Accepting L) S T := by
  obtain ⟨D,hDE,hD⟩ := SupportedCompletion.regular_completion E hE
  obtain ⟨F',hrec⟩ := recognizes_completion E η F L hL D hD
  let : Finite (Carrier E 1) := SupportEvaluation.finite_carrier E hB 1
  exact BoundedProfileRefinement.refines D hDE _ F' L hrec S T (small_completion E hB η D hDE hD S T h)


/--
---
conclusion: Lax369799.SupportedProfiles.yield_profile
---
A direct resolution is its own yield witness. Conversely a yield
witness has the same value as its target because supported evaluation
is invariant under unfoldings.
-/
theorem yield_profile {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B) {n : ℕ}
    (S : FiniteSystem A n) (e : Resolutions.ProfileEntry B n) :
    e ∈ Lax369799.SupportedProfiles.Profile E η S ↔
      ∃ T : SupportedSystems.System A e.1, SupportedYields.InitialYield S T e.2.2 ∧
        E.eval e.1 (SupportedSystems.relabel η T) = e.2.1 := by
  constructor
  · rintro ⟨T,⟨a⟩,hv⟩
    let i : FiniteMorphisms.Morphism (presentation T) (presentation T) := {
      toFun := id, initial := fun _ h => h, root := fun _ h => h, label := fun _ => rfl
      edge := by intro v d t h; cases t <;> exact h }
    exact ⟨T,⟨T,a,i,SupportedMorphisms.system_folding T T i⟩,hv⟩
  · rintro ⟨T,⟨U,a,b,_⟩,hv⟩
    let f : Morphisms.Morphism U.val.val T.val.val :=
      ⟨b.toFun,b.initial,b.root,b.label,b.edge⟩
    have he := hE e.1 (SupportedSystems.relabel η U) (SupportedSystems.relabel η T)
      (SystemSubstitution.relabel_unfold η ⟨U.val.val,
        ⟨MorphismTheorems.identity _,MorphismTheorems.identity_surjective _⟩,
        ⟨f,MorphismTheorems.system_morphism_locally_surjective U.val T.val f⟩⟩)
    exact ⟨U,⟨a⟩,he.trans hv⟩

/--
---
conclusion: Lax369799.SupportedProfiles.closed_small_profile
---
There are no target variables in rank zero, so every variable map
satisfies the small-fibre condition.
-/
theorem closed_small_profile {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) (S : FiniteSystem A 0) :
    Lax369799.SupportedProfiles.SmallProfile E η S = Lax369799.SupportedProfiles.Profile E η S := by
  ext e
  exact ⟨fun h => h.1,fun h => ⟨h,fun j => Fin.elim0 j⟩⟩

private def profileCode {A B : RankedSet} (E : SupportedAlgebras.Algebra B) (η : RankedMap A B)
    {n : ℕ} (S : FiniteSystem A n) : Set (BoundedProfiles.BoundedEntry B (Resolutions.SmallBound B) n) × Set (BoundedProfiles.BoundedEntry B (Resolutions.SmallBound B) n) :=
  (fun e => e.val ∈ Lax369799.SupportedProfiles.Profile E η S, fun e => e.val ∈ Lax369799.SupportedProfiles.Profile E η (SupportedYields.uproot S))

private theorem code_eq_iff {A B : RankedSet} (E : SupportedAlgebras.Algebra B) (η : RankedMap A B)
    {n : ℕ} (S T : FiniteSystem A n) :
    profileCode E η S = profileCode E η T ↔ Lax369799.SupportedProfiles.SmallProfileEquivalent E η S T := by
  have one (S T : FiniteSystem A n) :
      (fun e : BoundedProfiles.BoundedEntry B (Resolutions.SmallBound B) n => e.val ∈ Lax369799.SupportedProfiles.Profile E η S) = (fun e => e.val ∈ Lax369799.SupportedProfiles.Profile E η T) ↔
        Lax369799.SupportedProfiles.SmallProfile E η S = Lax369799.SupportedProfiles.SmallProfile E η T := by
    constructor
    · intro h
      ext e
      change (e ∈ Lax369799.SupportedProfiles.Profile E η S ∧ Resolutions.SmallMap B e.2.2) ↔ (e ∈ Lax369799.SupportedProfiles.Profile E η T ∧ Resolutions.SmallMap B e.2.2)
      constructor
      · rintro ⟨he, hs⟩
        exact ⟨(congrFun h ⟨e, hs⟩).mp he, hs⟩
      · rintro ⟨he, hs⟩
        exact ⟨(congrFun h ⟨e, hs⟩).mpr he, hs⟩
    · intro h
      funext e
      apply propext
      have hh := Set.ext_iff.mp h e.val
      change (_ ∧ Resolutions.SmallMap B e.val.2.2) ↔ (_ ∧ Resolutions.SmallMap B e.val.2.2) at hh
      have hs : Resolutions.SmallMap B e.val.2.2 := e.property
      simpa only [hs,and_true] using hh
  constructor
  · intro h
    exact ⟨(one S T).mp (congrArg Prod.fst h),
      (one (SupportedYields.uproot S) (SupportedYields.uproot T)).mp (congrArg Prod.snd h)⟩
  · rintro ⟨h, h'⟩
    exact Prod.ext ((one S T).mpr h) ((one (SupportedYields.uproot S) (SupportedYields.uproot T)).mpr h')

/--
---
conclusion: Lax369799.SupportedProfiles.small_profile_finite
---
A small map into n outputs has domain size at most n times the small
bound. Initial and root profiles therefore range over two finite
powersets of bounded entries.
-/
theorem small_profile_finite {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (η : RankedMap A B) (n : ℕ) :
    Finite (Quot (@Lax369799.SupportedProfiles.SmallProfileEquivalent A B E η n)) := by
  let : Finite (BoundedProfiles.BoundedEntry B (Resolutions.SmallBound B) n) :=
    BoundedProfiles.small_entry_finite hB (Resolutions.SmallBound B) n
  let f : Quot (@Lax369799.SupportedProfiles.SmallProfileEquivalent A B E η n) →
      Set (BoundedProfiles.BoundedEntry B (Resolutions.SmallBound B) n) ×
        Set (BoundedProfiles.BoundedEntry B (Resolutions.SmallBound B) n) :=
    Quot.lift (profileCode E η) (fun S T h => (code_eq_iff E η S T).mpr h)
  apply Finite.of_injective f
  intro x y
  induction x using Quot.inductionOn with
  | h S =>
    induction y using Quot.inductionOn with
    | h T =>
      intro h
      exact Quot.sound ((code_eq_iff E η S T).mp h)


private theorem closed_profiles_of_values {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) (D : Algebras.Algebra (Carrier E))
    (hD : ∀ n (R : System B n),
      D.eval n (relabelSystem (SupportedCompletion.letter E) R) = classMap E n R)
    (S T : FiniteSystem A 0)
    (h : PresentationObservations.values D (fun j a => SupportedCompletion.letter E j (η j a)) S.graph =
      PresentationObservations.values D (fun j a => SupportedCompletion.letter E j (η j a)) T.graph) :
    Lax369799.SupportedProfiles.Profile E η S = Lax369799.SupportedProfiles.Profile E η T := by
  obtain ⟨e,he⟩ := SupportEvaluation.closed_carrier E
  have forward (S T : FiniteSystem A 0)
      (h : PresentationObservations.values D (fun j a => SupportedCompletion.letter E j (η j a)) S.graph =
        PresentationObservations.values D (fun j a => SupportedCompletion.letter E j (η j a)) T.graph) :
      Lax369799.SupportedProfiles.Profile E η S ⊆ Lax369799.SupportedProfiles.Profile E η T := by
    rintro ⟨m,b,σ⟩ ⟨U,⟨a⟩,ha⟩
    cases m with
    | succ m => exact Fin.elim0 (σ ⟨0,Nat.zero_lt_succ _⟩)
    | zero =>
      have hσ : σ = id := funext (fun i => Fin.elim0 i)
      subst σ
      have r := legacy_resolution S U.val id a
      rw [Renaming.rename_identity] at r
      have hv : D.eval 0 (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) U.val) ∈
          PresentationObservations.values D (fun j a => SupportedCompletion.letter E j (η j a)) S.graph :=
        ⟨U.val,⟨r⟩,rfl⟩
      rw [h] at hv
      obtain ⟨R,⟨r'⟩,hv⟩ := hv
      let V := (SupportedSystems.closedEquiv A).symm R
      have r'' : Morphisms.Morphism (Resolutions.rename id R.val) (trim T.graph) := by
        rw [Renaming.rename_identity]; exact r'
      have hclass : classMap E 0 (relabelSystem η R) = classMap E 0 (relabelSystem η U.val) :=
        (hD 0 (relabelSystem η R)).symm.trans (hv.trans (hD 0 (relabelSystem η U.val)))
      refine ⟨V,⟨finite_resolution T R id r''⟩,?_⟩
      exact ((he (relabelSystem η R)).symm.trans ((congrArg e hclass).trans
        (he (relabelSystem η U.val)))).trans ha
  exact Set.Subset.antisymm (forward S T h) (forward T S h.symm)

/--
---
conclusion: Lax369799.SupportedProfiles.closed_congruence
---
Transfer the completed bounded initial and root observations in both
directions. The closed completion equivalence recovers the original
supported values, proving full profile equality (Lemma 83).
-/
theorem closed_congruence {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B)
    (P : FiniteSystem (FiniteSystem A) 0) (Q : ∀ v, FiniteSystem A (P.graph.label v).1)
    (h : ∀ v, Lax369799.SupportedProfiles.SmallProfileEquivalent E η (Inner P.graph v) (Q v)) :
    Lax369799.SupportedProfiles.ProfileEquivalent E η (flatten P) (flatten (withLabels P Q)) := by
  classical
  obtain ⟨D,hDE,hD⟩ := SupportedCompletion.regular_completion E hE
  let κ : RankedMap A (Carrier E) := fun j a => SupportedCompletion.letter E j (η j a)
  let : Finite (Carrier E 1) := SupportEvaluation.finite_carrier E hB 1
  have hp (v : P.Vertex) := small_completion E hB η D hDE hD (Inner P.graph v) (Q v) (h v)
  have hf := BoundedProfileRefinement.transfer D hDE κ P.graph Q hp
  let R := withLabels P Q
  have hr (v : P.Vertex) : FiniteProfiles.BoundedProfileEquivalent (Nat.card (Carrier E 1) + 1)
      (fun k S => D.eval k (relabelSystem κ S)) (Inner R.graph v) (Inner P.graph v) :=
    ⟨(hp v).1.symm,(hp v).2.symm⟩
  have hb := BoundedProfileRefinement.transfer D hDE κ R.graph (fun v => Inner P.graph v) hr
  have hrestore : BoundedProfileRefinement.replace R.graph (fun v => Inner P.graph v) = P.graph := by
    cases P; rfl
  rw [hrestore] at hb
  let G := flattenPresentation P.graph
  let H := flattenPresentation R.graph
  have hi : PresentationObservations.values D κ G = PresentationObservations.values D κ H :=
    Set.Subset.antisymm hf.1 hb.1
  have hroot : PresentationObservations.values D κ (RootExpansion.startAtRoots G) =
      PresentationObservations.values D κ (RootExpansion.startAtRoots H) :=
    Set.Subset.antisymm hf.2 hb.2
  let cG := FiniteCovers.isoCover (UntrimmedFlattening.reindexIso G (Fintype.equivFin _))
  let cH := FiniteCovers.isoCover (UntrimmedFlattening.reindexIso H (Fintype.equivFin _))
  constructor
  · apply closed_profiles_of_values E η D hD
    exact (PresentationObservations.values_cover D hDE κ cG).symm.trans
      (hi.trans (PresentationObservations.values_cover D hDE κ cH))
  · apply closed_profiles_of_values E η D hD
    change PresentationObservations.values D κ (RootExpansion.startAtRoots (enumerate G).graph) =
      PresentationObservations.values D κ (RootExpansion.startAtRoots (enumerate H).graph)
    exact (PresentationObservations.root_values_cover D hDE κ cG).symm.trans
      (hroot.trans (PresentationObservations.root_values_cover D hDE κ cH))

end Lax369799Proofs.SupportedProfiles
