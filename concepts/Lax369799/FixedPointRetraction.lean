import Mathlib.Order.FixedPoints

/-!
---
title: Fixed points through a monotone retraction
type: theorem
---
If every value of a monotone operator lies in the image of a monotone
section, projection to that image preserves its least and greatest fixed
points. This removes auxiliary coordinates whose values are determined
by the retained coordinates.
-/
namespace Lax369799.FixedPointRetraction
variable {α β : Type} [CompleteLattice α] [CompleteLattice β]

def reduced (F : α →o α) (p : α →o β) (l : β →o α) : β →o β := p.comp (F.comp l)

axiom least (F : α →o α) (p : α →o β) (l : β →o α)
    (hp : ∀ x, p (l x) = x) (hF : ∀ x, l (p (F x)) = F x) :
    p F.lfp = (reduced F p l).lfp

axiom greatest (F : α →o α) (p : α →o β) (l : β →o α)
    (hp : ∀ x, p (l x) = x) (hF : ∀ x, l (p (F x)) = F x) :
    p F.gfp = (reduced F p l).gfp

end Lax369799.FixedPointRetraction
