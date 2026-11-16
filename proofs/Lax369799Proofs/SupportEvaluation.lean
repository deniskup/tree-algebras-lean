import Lax369799.SupportEvaluation
import Lax369799Proofs.SupportedAlgebras
import Lax369799Proofs.SupportCompaction

namespace Lax369799Proofs.SupportEvaluation
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet RankwiseFinite)
open SupportedSystems SupportedAlgebras Lax369799.SupportEvaluation

/--
---
conclusion: Lax369799.SupportEvaluation.profile_nonempty
---
-/
theorem profile_nonempty {B : RankedSet} (E : Algebra B) {n : ℕ}
    (S : RankedSystems.System B n) : (profile E S).Nonempty := by
  obtain ⟨m, σ, T, hσ, hT⟩ := SupportCompaction.compact_exists S
  have hm : m ≤ n := by simpa using Fintype.card_le_of_injective σ hσ
  exact ⟨⟨⟨m, by omega⟩, ⟨σ, hσ⟩, E.eval m T⟩, T, hT, rfl⟩

/--
---
conclusion: Lax369799.SupportEvaluation.finite_observations
---
-/
theorem finite_observations {B : RankedSet} (hB : RankwiseFinite B) (n : ℕ) :
    Finite (Observation B n) := by
  let : ∀ i : Fin (n+1), Finite (B i.val) := fun i => hB i.val
  let f : Observation B n → (i : Fin (n+1)) × ((Fin i.val ↪ Fin n) × B i.val) :=
    fun o => ⟨o.arity, o.ports, o.value⟩
  apply Finite.of_injective f
  intro a b h
  cases a
  cases b
  cases h
  rfl

/--
---
conclusion: Lax369799.SupportEvaluation.finite_carrier
---
-/
theorem finite_carrier {B : RankedSet} (E : Algebra B) (hB : RankwiseFinite B) :
    RankwiseFinite (Carrier E) := by
  intro n
  let := finite_observations hB n
  let f : Carrier E n → Set (Observation B n) := Quot.lift (profile E) (fun _ _ h => h)
  apply Finite.of_injective f
  intro a b
  refine Quot.inductionOn a (fun S => Quot.inductionOn b (fun T => ?_))
  intro h
  exact Quot.sound h

private theorem rename_comp {B : RankedSet} {m k n : ℕ}
    (σ : Fin m → Fin k) (τ : Fin k → Fin n) (S : RankedSystems.System B m) :
    Renaming.renameSystem τ (Renaming.renameSystem σ S) =
      Renaming.renameSystem (τ ∘ σ) S := by
  apply Subtype.ext
  exact Renaming.rename_composition σ τ S.val

private theorem transfer {B : RankedSet} (E : Algebra B)
    {m n : ℕ} (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    (U V : System B m) (hUV : E.eval m U = E.eval m V)
    (o : Observation B n)
    (ho : o ∈ profile E (Renaming.renameSystem σ U.val)) :
    o ∈ profile E (Renaming.renameSystem σ V.val) := by
  obtain ⟨T, hT, he⟩ := ho
  obtain ⟨e, hep, hete⟩ := SupportCompaction.compact_unique σ o.ports hσ o.ports.injective
    U T hT.symm
  let W : System B o.arity.val := rename e e.surjective V
  have heports : (o.ports : Fin o.arity.val → Fin n) ∘ e = σ := funext hep
  have hW : Renaming.renameSystem o.ports W.val = Renaming.renameSystem σ V.val := by
    change Renaming.renameSystem o.ports (Renaming.renameSystem e V.val) = _
    rw [rename_comp, heports]
  refine ⟨W, hW, ?_⟩
  have hU : rename e e.surjective U = T := Subtype.ext hete
  rw [← hU] at he
  change E.eval _ (rename e e.surjective V) = o.value
  rw [SupportedAlgebras.rename_evaluation E e e.surjective V, ← hUV,
    ← SupportedAlgebras.rename_evaluation E e e.surjective U]
  exact he

/--
---
conclusion: Lax369799.SupportEvaluation.equivalent_iff
---
-/
theorem equivalent_iff {B : RankedSet} (E : Algebra B)
    {n : ℕ} (S T : RankedSystems.System B n) :
    Equivalent E S T ↔ ∃ (m : ℕ) (σ : Fin m → Fin n), Function.Injective σ ∧
      ∃ U V : System B m, Renaming.renameSystem σ U.val = S ∧
        Renaming.renameSystem σ V.val = T ∧ E.eval m U = E.eval m V := by
  constructor
  · intro h
    obtain ⟨o, U, hU, heU⟩ := profile_nonempty E S
    have hmem : o ∈ profile E T := h ▸ (show o ∈ profile E S from ⟨U, hU, heU⟩)
    obtain ⟨V, hV, heV⟩ := hmem
    exact ⟨o.arity.val, o.ports, o.ports.injective, U, V, hU, hV, heU.trans heV.symm⟩
  · rintro ⟨m, σ, hσ, U, V, rfl, rfl, hUV⟩
    ext o
    exact ⟨transfer E σ hσ U V hUV o, transfer E σ hσ V U hUV.symm o⟩

private def closed {B : RankedSet} (S : RankedSystems.System B 0) : System B 0 :=
  (closedEquiv B).symm S

private def closedObservation {B : RankedSet} (b : B 0) : Observation B 0 :=
  ⟨0, ⟨id, Function.injective_id⟩, b⟩

private theorem rename_zero {B : RankedSet} (S : RankedSystems.System B 0) :
    Renaming.renameSystem id S = S := by
  apply Subtype.ext
  exact Renaming.rename_identity S.val

private theorem closed_observation {B : RankedSet} (E : Algebra B)
    (S : RankedSystems.System B 0) (b : B 0) :
    closedObservation b ∈ profile E S ↔ E.eval 0 (closed S) = b := by
  constructor
  · rintro ⟨T, hT, he⟩
    change Renaming.renameSystem id T.val = S at hT
    rw [rename_zero] at hT
    have hclosed : T = closed S := Subtype.ext hT
    exact hclosed ▸ he
  · intro he
    exact ⟨closed S, rename_zero S, he⟩

/--
---
conclusion: Lax369799.SupportEvaluation.closed_equivalent_iff
---
-/
theorem closed_equivalent_iff {B : RankedSet} (E : Algebra B)
    (S T : RankedSystems.System B 0) :
    Equivalent E S T ↔ E.eval 0 (closedEquiv B |>.symm S) =
      E.eval 0 (closedEquiv B |>.symm T) := by
  constructor
  · intro h
    have hmem : closedObservation (E.eval 0 (closed S)) ∈ profile E S :=
      (closed_observation E S _).mpr rfl
    rw [show profile E S = profile E T from h] at hmem
    exact ((closed_observation E T _).mp hmem).symm
  · intro he
    ext o
    have ha : o.arity = (0 : Fin 1) := Fin.ext (by have := o.arity.isLt; omega)
    cases o with | mk a p b =>
      dsimp at ha
      subst a
      have hp : p = (⟨id, Function.injective_id⟩ : Fin 0 ↪ Fin 0) := by
        ext i
        exact Fin.elim0 i
      subst p
      change closedObservation b ∈ profile E S ↔ closedObservation b ∈ profile E T
      change E.eval 0 (closed S) = E.eval 0 (closed T) at he
      rw [closed_observation, closed_observation, he]

/--
---
conclusion: Lax369799.SupportEvaluation.closed_carrier
---
-/
theorem closed_carrier {B : RankedSet} (E : Algebra B) :
    ∃ e : Carrier E 0 ≃ B 0, ∀ S : RankedSystems.System B 0,
      e (classMap E 0 S) = E.eval 0 ((closedEquiv B).symm S) := by
  let f : Carrier E 0 → B 0 := Quot.lift
    (fun S => E.eval 0 ((closedEquiv B).symm S))
    (fun S T h => (closed_equivalent_iff E S T).mp h)
  have hinj : Function.Injective f := by
    intro a b
    refine Quot.inductionOn a (fun S => Quot.inductionOn b (fun T => ?_))
    intro he
    exact Quot.sound ((closed_equivalent_iff E S T).mpr he)
  have hsurj : Function.Surjective f := by
    intro b
    exact ⟨classMap E 0 (RankedSystems.atomicSystem b), E.unit 0 b⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

end Lax369799Proofs.SupportEvaluation
