import Lax369799.RecognitionClosure
import Lax369799Proofs.SystemSubstitution
import Mathlib.Data.Finite.Prod

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.RecognitionClosure
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.Morphisms Lax369799.Flattening

private def product {B C : RankedSet} (E : Algebra B) (F : Algebra C) : Algebra (fun n => B n × C n) where
  eval := fun n S => (E.eval n (relabelSystem (fun _ => Prod.fst) S),
    F.eval n (relabelSystem (fun _ => Prod.snd) S))
  isomorphic := by
    rintro n S T ⟨f, hf, hc⟩
    apply Prod.ext
    · exact E.isomorphic n _ _ ⟨SystemSubstitution.relabelMorphism (fun _ => Prod.fst) f, hf, hc⟩
    · exact F.isomorphic n _ _ ⟨SystemSubstitution.relabelMorphism (fun _ => Prod.snd) f, hf, hc⟩
  unit := fun n a => Prod.ext (E.unit n a.1) (F.unit n a.2)
  associative := by
    intro n S T ht
    have projection {D : RankedSet} (π : RankedMap (fun n => B n × C n) D) :
        SystemFlattening (relabelSystem (fun _ U => relabelSystem π U) S) (relabelSystem π T) := by
      change relabel π T.val = _
      rw [ht]
      rfl
    exact Prod.ext
      (E.associative n _ _ (projection (fun _ => Prod.fst)))
      (F.associative n _ _ (projection (fun _ => Prod.snd)))

private theorem product_finite {B C : RankedSet} (hB : RankwiseFinite B) (hC : RankwiseFinite C) :
    RankwiseFinite (fun n => B n × C n) := by
  intro n
  let : Finite (B n) := hB n
  let : Finite (C n) := hC n
  infer_instance

/--
---
conclusion: Lax369799.RecognitionClosure.complement
---
Keep the algebra and letter map, and complement the accepting subset.
-/
theorem complement {A : RankedSet} (L : Language A) (h : Recognizable L) : Recognizable Lᶜ := by
  obtain ⟨B, E, η, F, hB, hrec⟩ := h
  exact ⟨B, E, η, Fᶜ, hB, fun S => not_congr (hrec S)⟩

/--
---
conclusion: Lax369799.RecognitionClosure.intersection
---
The product algebra evaluates coordinatewise and accepts exactly when
both recognizing coordinates accept.
-/
theorem intersection {A : RankedSet} (L K : Language A)
    (hL : Recognizable L) (hK : Recognizable K) : Recognizable (L ∩ K) := by
  obtain ⟨B, E, η, F, hB, hL⟩ := hL
  obtain ⟨C, G, μ, H, hC, hK⟩ := hK
  refine ⟨(fun n => B n × C n), product E G, (fun n a => (η n a, μ n a)),
    {b | b.1 ∈ F ∧ b.2 ∈ H}, product_finite hB hC, ?_⟩
  exact fun S => and_congr (hL S) (hK S)

/--
---
conclusion: Lax369799.RecognitionClosure.union
---
Use the same product algebra, accepting when at least one coordinate
belongs to its accepting subset.
-/
theorem union {A : RankedSet} (L K : Language A)
    (hL : Recognizable L) (hK : Recognizable K) : Recognizable (L ∪ K) := by
  obtain ⟨B, E, η, F, hB, hL⟩ := hL
  obtain ⟨C, G, μ, H, hC, hK⟩ := hK
  refine ⟨(fun n => B n × C n), product E G, (fun n a => (η n a, μ n a)),
    {b | b.1 ∈ F ∨ b.2 ∈ H}, product_finite hB hC, ?_⟩
  exact fun S => or_congr (hL S) (hK S)

/--
---
conclusion: Lax369799.RecognitionClosure.inverse_relabel
---
Compose the recognizing letter map with the given alphabet map.
-/
theorem inverse_relabel {A B : RankedSet} (η : RankedMap A B) (L : Language B)
    (hL : Recognizable L) : Recognizable {S | relabelSystem η S ∈ L} := by
  obtain ⟨C, E, μ, F, hC, hrec⟩ := hL
  exact ⟨C, E, (fun n a => μ n (η n a)), F, hC, fun S => hrec (relabelSystem η S)⟩

end Lax369799Proofs.RecognitionClosure
