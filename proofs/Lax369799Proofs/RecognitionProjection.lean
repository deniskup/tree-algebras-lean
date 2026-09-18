import Lax369799.RecognitionProjection
import Lax369799Proofs.NonemptyPowersets

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.RecognitionProjection
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.PolynomialContexts
open Lax369799.NonemptyPowersets Lax369799.RecognitionProjection

/--
---
conclusion: Lax369799.RecognitionProjection.recognizable
---
The new letter interpretation is the nonempty set of all interpretations
of its lifts. Membership in the accepting subset is existential.
-/
theorem recognizable {A B : RankedSet} (η : RankedMap A B)
    (hη : ∀ n, Function.Surjective (η n)) (L : Language A) (hL : Recognizable L) :
    Recognizable (Projected η L) := by
  classical
  obtain ⟨C, E, μ, F, hC, hL⟩ := hL
  obtain ⟨E', he⟩ := NonemptyPowersets.algebra E
  let ν : RankedMap B (Carrier C) := fun n b =>
    ⟨{c | ∃ a, η n a = b ∧ μ n a = c}, by
      obtain ⟨a, ha⟩ := hη n b
      exact ⟨μ n a, a, ha, rfl⟩⟩
  refine ⟨Carrier C, E', ν, {X | ∃ c ∈ X.val, c ∈ F}, NonemptyPowersets.finite_carrier hC, ?_⟩
  intro S
  change (∃ q, (∀ v, η _ (q v) = (S.val.graph.label v).2) ∧ withLabels S q ∈ L) ↔ _
  change _ ↔ ∃ c ∈ (E'.eval 0 (relabelSystem ν S)).val, c ∈ F
  rw [he]
  constructor
  · rintro ⟨q, hq, hl⟩
    refine ⟨E.eval 0 (relabelSystem μ (withLabels S q)), ?_, (hL _).mp hl⟩
    exact ⟨fun v => μ _ (q v), fun v => ⟨q v, hq v, rfl⟩, rfl⟩
  · rintro ⟨c, ⟨q, hq, hv⟩, hc⟩
    change ∀ v, ∃ a, η _ a = (S.val.graph.label v).2 ∧ μ _ a = q v at hq
    choose p hp hμ using hq
    refine ⟨p, hp, (hL _).mpr ?_⟩
    have ht : relabelSystem μ (withLabels S p) = withLabels (relabelSystem ν S) q := by
      change withLabels S (fun v => μ _ (p v)) = _
      simp only [hμ]
      rfl
    rw [ht, hv]
    exact hc

end Lax369799Proofs.RecognitionProjection
