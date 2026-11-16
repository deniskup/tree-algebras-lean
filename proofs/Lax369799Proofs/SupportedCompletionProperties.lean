import Lax369799Proofs.SupportedCompletion
import Lax369799Proofs.SupportedMorphisms
import Lax369799Proofs.PresentationCovers
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Sum

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedCompletion
open Lax369799
open RankedSystems Morphisms
open SupportEvaluation (Carrier classMap Equivalent)
open Lax369799.SupportedCompletion (letter)

private theorem output_morphism {A : RankedSet} {n : ℕ} (S T : System A n)
    (f : Morphism S.val T.val) (j : Fin n) :
    (∃ v d, S.val.graph.edge v d (.inr j)) ↔ ∃ v d, T.val.graph.edge v d (.inr j) := by
  constructor
  · rintro ⟨v,d,hd⟩; exact ⟨f.toFun v,d,f.edge v d (.inr j) hd⟩
  · rintro ⟨w,d,hd⟩
    have hf := MorphismTheorems.system_morphism_locally_surjective S T f
    let c : PresentationCovers.Cover S.val.graph T.val.graph :=
      ⟨f.toFun,f.label,f.initial,f.root,f.edge,hf.1,hf.2.1,hf.2.2⟩
    obtain ⟨v,rfl⟩ := PresentationCovers.surjective_of_reachable c T.val.reachable w
    obtain ⟨t,ht,he⟩ := hf.2.2 v d (.inr j) hd
    cases t with
    | inl u => cases he
    | inr i => cases Sum.inr.inj he; exact ⟨v,d,ht⟩

/--
---
conclusion: Lax369799.SupportedCompletion.profile_morphism
---
Compact both systems along their common output support. Reflect the
morphism through that injective renaming and apply supported unfolding
invariance to the compacted systems.
-/
theorem profile_morphism {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) {n : ℕ} (S T : System B n)
    (f : Morphism S.val T.val) : Equivalent E S T := by
  obtain ⟨m,σ,U,hσ,hU⟩ := SupportCompaction.compact_exists S
  have hs (j : Fin n) : (∃ v d, T.val.graph.edge v d (.inr j)) ↔ j ∈ Set.range σ := by
    have hi := SupportCompaction.support_image σ U j
    rw [hU] at hi
    exact (output_morphism S T f j).symm.trans hi
  obtain ⟨V,hV⟩ := SupportIsomorphism.compact_along T σ hσ hs
  have f' : Morphism (Renaming.renameSystem σ U.val).val (Renaming.renameSystem σ V.val).val := by
    rw [hU,hV]; exact f
  obtain ⟨g,_⟩ := SupportIsomorphism.reflect_morphism σ hσ U.val V.val f'
  have he := hE m U V ⟨U.val.val,
    ⟨MorphismTheorems.identity _,MorphismTheorems.identity_surjective _⟩,
    ⟨g,MorphismTheorems.system_morphism_locally_surjective U.val V.val g⟩⟩
  exact (SupportEvaluation.equivalent_iff E S T).mpr ⟨m,σ,hσ,U,V,hU,hV,he⟩

/--
---
conclusion: Lax369799.SupportedCompletion.profile_unfold
---
Select a deterministic common unfolding, then apply the two morphism
comparisons to identify the supported-evaluation profiles.
-/
theorem profile_unfold {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) {n : ℕ} (S T : System B n)
    (h : UnfoldEquivalent S.val T.val) : Equivalent E S T := by
  obtain ⟨P,⟨p,hp⟩,⟨q,_⟩⟩ := h
  obtain ⟨W,⟨w⟩,⟨ws,_⟩⟩ := Yields.lift_resolution p hp S (MorphismTheorems.identity S.val)
  exact (profile_morphism E hE W S ws).symm.trans
    (profile_morphism E hE W T (MorphismTheorems.compose w q))

/--
---
conclusion: Lax369799.SupportedCompletion.eval_letters
---
Expand every letter to its atomic system. Completion evaluation and the
inner unit identify the result with the original system class.
-/
theorem eval_letters {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (D : Algebras.Algebra (Carrier E))
    (hD : ∀ n (P : System (System B) n) (U : System B n),
      Flattening.SystemFlattening P U → D.eval n (relabelSystem (classMap E) P) = classMap E n U)
    {n : ℕ} (S : System B n) :
    D.eval n (relabelSystem (letter E) S) = classMap E n S := by
  let P := relabelSystem (fun _ b => atomicSystem b) S
  obtain ⟨U,hU⟩ := Flattening.flatten_system P
  have hi := SystemMonad.inner_unit S U hU
  exact (hD n P U hU).trans (Quot.sound (SupportIsomorphism.profile_isomorphic E U S hi))

/--
---
conclusion: Lax369799.SupportedCompletion.regular_completion
---
Choose representatives of the observation classes and flatten. A common
unfolding of the outer systems induces a common unfolding of these
flattenings, whose supported-evaluation profiles coincide.
-/
theorem regular_completion {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) :
    ∃ D : Algebras.Algebra (Carrier E), Algebras.UnfoldInvariant D ∧
      ∀ n (S : System B n), D.eval n (relabelSystem (letter E) S) = classMap E n S := by
  classical
  obtain ⟨D,hD⟩ := SupportedCompletion.algebra E
  let rep : RankedMap (Carrier E) (System B) := fun _ a => a.out
  have heval {n : ℕ} (S : System (Carrier E) n) (U : System B n)
      (hU : Flattening.SystemFlattening (relabelSystem rep S) U) : D.eval n S = classMap E n U := by
    have he : relabelSystem (classMap E) (relabelSystem rep S) = S := by
      apply Subtype.ext
      dsimp only [relabelSystem,relabel]
      congr 1
      congr 1
      funext v
      exact congrArg (Sigma.mk (S.val.graph.label v).1) (Quot.out_eq (S.val.graph.label v).2)
    rw [←he]
    exact hD n _ U hU
  refine ⟨D,?_,fun n S => eval_letters E D hD S⟩
  intro n S T h
  obtain ⟨U,hU⟩ := Flattening.flatten_system (relabelSystem rep S)
  obtain ⟨V,hV⟩ := Flattening.flatten_system (relabelSystem rep T)
  rw [heval S U hU,heval T V hV]
  exact Quot.sound (profile_unfold E hE U V
    (SystemSubstitution.outer_unfold _ _ (SystemSubstitution.relabel_unfold rep h) U V hU hV))

private theorem rename_id {B : RankedSet} {n : ℕ} (S : System B n) :
    Renaming.renameSystem id S = S := Subtype.ext (Renaming.rename_identity S.val)

/--
---
conclusion: Lax369799.SupportedCompletion.unary_card_bound
---
A unary system has either no used output or one used output. Its class
is represented by an atomic closed value or an atomic unary value, so
the disjoint union of the two original sorts surjects onto the unary sort.
-/
theorem unary_card_bound {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) : Nat.card (Carrier E 1) ≤ Nat.card (B 0) + Nat.card (B 1) := by
  let : Finite (B 0) := hB 0
  let : Finite (B 1) := hB 1
  let f : B 0 ⊕ B 1 → Carrier E 1 := Sum.elim
    (fun b => classMap E 1 (Renaming.renameSystem Fin.elim0 (atomicSystem b)))
    (fun b => classMap E 1 (atomicSystem b))
  have hf : Function.Surjective f := by
    intro a
    induction a using Quot.inductionOn with
    | h S =>
      change ∃ b, f b = classMap E 1 S
      obtain ⟨m,σ,U,hσ,hU⟩ := SupportCompaction.compact_exists S
      have hm : m ≤ 1 := by simpa using Fintype.card_le_of_injective σ hσ
      have hc : classMap E 1 (Renaming.renameSystem σ U.val) =
          classMap E 1 (Renaming.renameSystem σ (SupportedSystems.atomic (E.eval m U)).val) :=
        Quot.sound ((SupportEvaluation.equivalent_iff E _ _).mpr
          ⟨m,σ,hσ,U,SupportedSystems.atomic (E.eval m U),rfl,rfl,(E.unit m _).symm⟩)
      rw [hU] at hc
      cases m with
      | zero =>
        have hs : σ = Fin.elim0 := funext (fun i => Fin.elim0 i)
        exact ⟨.inl (E.eval 0 U),by simpa [f,hs,SupportedSystems.atomic] using hc.symm⟩
      | succ m =>
        have hm0 : m = 0 := by omega
        subst m
        have hs : σ = id := funext (fun i => Subsingleton.elim _ _)
        exact ⟨.inr (E.eval 1 U),by simpa [f,hs,SupportedSystems.atomic,rename_id] using hc.symm⟩
  have hn := Nat.card_le_card_of_surjective f hf
  simpa only [Nat.card_sum] using hn

end Lax369799Proofs.SupportedCompletion
