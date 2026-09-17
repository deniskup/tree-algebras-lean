import Lax369799.DeterministicSyntacticOrder
import Lax369799Proofs.ContextRelabelling
import Lax369799Proofs.ContextCongruence
import Lax369799Proofs.AtomicFlattening

namespace Lax369799Proofs.DeterministicSyntacticOrder
open Lax369799.RankedSystems Lax369799.Flattening Lax369799.Algebras Lax369799.Morphisms
open Lax369799.DeterministicSyntacticOrder

/--
---
conclusion: Lax369799.DeterministicSyntacticOrder.value_refines
---
Equal recognizing values remain equal in a deterministic context by
associativity. Membership then agrees by the recognizing accepting set.
-/
theorem value_refines {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (F : Set (B 0)) (L : Language A) (hL : Recognizes E η F L)
    {n : ℕ} (S T : System A n)
    (h : E.eval n (relabelSystem η S) = E.eval n (relabelSystem η T)) : Equivalent L S T := by
  have forward (S T : System A n)
      (h : E.eval n (relabelSystem η S) = E.eval n (relabelSystem η T))
      (C : Context A n 0) : Test L C S → Test L C T := by
    rintro ⟨U, hu, hl⟩
    obtain ⟨V, hv⟩ := ContextRelabelling.plug_system C.val C.property T
    refine ⟨V, hv, (hL V).mpr ?_⟩
    rw [← ContextRelabelling.evaluation_congruence E η C.val C.property S T U V hu hv h]
    exact (hL U).mp hl
  exact fun C => ⟨forward S T h C, forward T S h.symm C⟩

/--
---
conclusion: Lax369799.DeterministicSyntacticOrder.unfold_refines
---
Unfold-equivalence is preserved by context substitution. The language is
constant on that equivalence, so every deterministic contextual test agrees.
-/
theorem unfold_refines {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    {n : ℕ} (S T : System A n) (h : UnfoldEquivalent S.val T.val) : Equivalent L S T := by
  intro C
  obtain ⟨U, hu⟩ := ContextRelabelling.plug_system C.val C.property S
  obtain ⟨V, hv⟩ := ContextRelabelling.plug_system C.val C.property T
  have he := ContextCongruence.unfold_context_congruence C.val S.val T.val h
  rw [← hu, ← hv] at he
  have hl := hL U V he
  constructor
  · rintro ⟨U', hu', hl'⟩
    have hU : U' = U := Subtype.ext (hu'.trans hu.symm)
    exact ⟨V, hv, hl.mp (hU ▸ hl')⟩
  · rintro ⟨V', hv', hl'⟩
    have hV : V' = V := Subtype.ext (hv'.trans hv.symm)
    exact ⟨U, hu, hl.mpr (hV ▸ hl')⟩

private def identityContext (A : RankedSet) (n : ℕ) : Context A n n :=
  ⟨⟨atomic (A := WithHole A n) (Sum.inr ⟨rfl⟩), by
    change ∃! v : Fin 1, IsHole (⟨n, Sum.inr ⟨rfl⟩⟩ : Symbol (WithHole A n))
    refine ⟨0, ⟨⟨rfl⟩, rfl⟩, ?_⟩
    intro v _
    exact Subsingleton.elim v 0⟩, (atomicSystem (A := WithHole A n) (Sum.inr ⟨rfl⟩)).property⟩

private theorem identity_test {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    (S : System A 0) : Test L (identityContext A 0) S ↔ S ∈ L := by
  have hc : UnfoldsTo S.val (plug (identityContext A 0).val S.val) :=
    AtomicFlattening.outer_atomic_cover S.val
  have he (U : System A 0) (hu : U.val = plug (identityContext A 0).val S.val) : U ∈ L ↔ S ∈ L := by
    apply hL U S
    rw [hu]
    exact ⟨_, ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩, hc⟩
  constructor
  · rintro ⟨U, hu, hl⟩
    exact (he U hu).mp hl
  · intro hl
    obtain ⟨U, hu⟩ := ContextRelabelling.plug_system (identityContext A 0).val
      (identityContext A 0).property S
    exact ⟨U, hu, (he U hu).mpr hl⟩

/--
---
conclusion: Lax369799.DeterministicSyntacticOrder.closed_membership
---
Test the equivalence in the context consisting of a single hole. Plugging
into this context preserves unfolding, and hence language membership.
-/
theorem closed_membership {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    (S T : System A 0) (h : Equivalent L S T) : S ∈ L ↔ T ∈ L :=
  (identity_test L hL S).symm.trans ((h (identityContext A 0)).trans (identity_test L hL T))

/--
---
conclusion: Lax369799.DeterministicSyntacticOrder.accepting_class
---
Language membership is constant on the closed contextual classes.
-/
theorem accepting_class {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    (S : System A 0) : AcceptingClass L (Quot.mk _ S) ↔ S ∈ L := by
  let st : Setoid (System A 0) := {
    r := Equivalent L
    iseqv := ⟨fun _ _ => Iff.rfl, fun h C => (h C).symm, fun h h' C => (h C).trans (h' C)⟩ }
  constructor
  · rintro ⟨T, ht, hl⟩
    exact (closed_membership L hL T S (@Quotient.exact _ st _ _ ht)).mp hl
  · intro hl
    exact ⟨S, rfl, hl⟩

/--
---
conclusion: Lax369799.DeterministicSyntacticOrder.finite_carrier
---
The quotient by equality of recognizing values embeds in the finite
recognizing sort. It maps onto the deterministic contextual quotient.
-/
theorem finite_carrier {A : RankedSet} (L : Language A) (hL : Recognizable L) : RankwiseFinite (Carrier L) := by
  obtain ⟨B, E, η, F, hB, hrec⟩ := hL
  intro n
  let ρ := fun S : System A n => E.eval n (relabelSystem η S)
  let r := fun S T : System A n => ρ S = ρ T
  let : Finite (B n) := hB n
  let g : Quot r → B n := Quot.lift ρ (fun _ _ h => h)
  have hg : Function.Injective g := by
    intro x y
    induction x using Quot.inductionOn with
    | h S =>
      induction y using Quot.inductionOn with
      | h T => exact fun h => Quot.sound h
  let : Finite (Quot r) := Finite.of_injective g hg
  let f : Quot r → Carrier L n :=
    Quot.lift (fun S => Quot.mk _ S) (fun S T h => Quot.sound (value_refines E η F L hrec S T h))
  apply Finite.of_surjective f
  intro x
  induction x using Quot.inductionOn with
  | h S => exact ⟨Quot.mk _ S, rfl⟩

end Lax369799Proofs.DeterministicSyntacticOrder
