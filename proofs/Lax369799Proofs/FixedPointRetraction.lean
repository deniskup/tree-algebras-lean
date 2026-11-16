import Lax369799.FixedPointRetraction

namespace Lax369799Proofs.FixedPointRetraction
variable {α β : Type} [CompleteLattice α] [CompleteLattice β]

open Lax369799.FixedPointRetraction

/--
---
conclusion: Lax369799.FixedPointRetraction.least
---
Project the extremal fixed point and lift the reduced extremal fixed
point. Both satisfy their respective fixed-point equations.
-/
theorem least (F : α →o α) (p : α →o β) (l : β →o α)
    (hp : ∀ x, p (l x) = x) (hF : ∀ x, l (p (F x)) = F x) :
    p F.lfp = (reduced F p l).lfp := by
  let H := reduced F p l
  have hl : F (l H.lfp) = l H.lfp := by
    rw [← hF (l H.lfp)]
    change l (H H.lfp) = l H.lfp
    rw [H.map_lfp]
  have hr : l (p F.lfp) = F.lfp := by
    simpa only [F.map_lfp] using hF F.lfp
  have hf : H (p F.lfp) = p F.lfp := by
    change p (F (l (p F.lfp))) = p F.lfp
    rw [hr, F.map_lfp]
  apply le_antisymm
  · have h := p.monotone (F.lfp_le hl.le)
    rwa [hp] at h
  · exact H.lfp_le hf.le

/--
---
conclusion: Lax369799.FixedPointRetraction.greatest
---
Project the extremal fixed point and lift the reduced extremal fixed
point. Both satisfy their respective fixed-point equations.
-/
theorem greatest (F : α →o α) (p : α →o β) (l : β →o α)
    (hp : ∀ x, p (l x) = x) (hF : ∀ x, l (p (F x)) = F x) :
    p F.gfp = (reduced F p l).gfp := by
  let H := reduced F p l
  have hl : F (l H.gfp) = l H.gfp := by
    rw [← hF (l H.gfp)]
    change l (H H.gfp) = l H.gfp
    rw [H.map_gfp]
  have hr : l (p F.gfp) = F.gfp := by
    simpa only [F.map_gfp] using hF F.gfp
  have hf : H (p F.gfp) = p F.gfp := by
    change p (F (l (p F.gfp))) = p F.gfp
    rw [hr, F.map_gfp]
  apply le_antisymm
  · exact H.le_gfp hf.ge
  · have h := p.monotone (F.le_gfp hl.ge)
    rwa [hp] at h

end Lax369799Proofs.FixedPointRetraction
