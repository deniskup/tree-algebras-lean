import Mathlib.Order.FixedPoints

/-!
---
title: Elimination of simultaneous fixed points
type: theorem
---
Bekić's identity expresses a simultaneous least or greatest fixed point
on a product as two nested fixed points. Iterating the identity eliminates
finite vectors of modal fixed-point variables.
-/
namespace Lax369799.FixedPointElimination

variable {α β : Type} [CompleteLattice α] [CompleteLattice β]

def sectionMap (F : α × β →o α × β) (a : α) : β →o β where
  toFun := fun b => (F (a, b)).2
  monotone' := fun b c h => (F.monotone (show (a, b) ≤ (a, c) from ⟨le_rfl, h⟩)).2

def leastSection (F : α × β →o α × β) : α →o β where
  toFun := fun a => (sectionMap F a).lfp
  monotone' := fun a b h => OrderHom.lfp.monotone
    (fun c => (F.monotone (show (a, c) ≤ (b, c) from ⟨h, le_rfl⟩)).2)

def greatestSection (F : α × β →o α × β) : α →o β where
  toFun := fun a => (sectionMap F a).gfp
  monotone' := fun a b h => OrderHom.gfp.monotone
    (fun c => (F.monotone (show (a, c) ≤ (b, c) from ⟨h, le_rfl⟩)).2)

def firstMap (F : α × β →o α × β) (s : α →o β) : α →o α where
  toFun := fun a => (F (a, s a)).1
  monotone' := fun _ _ h => (F.monotone ⟨h, s.monotone h⟩).1

axiom least (F : α × β →o α × β) :
    F.lfp = ((firstMap F (leastSection F)).lfp,
      leastSection F (firstMap F (leastSection F)).lfp)

axiom greatest (F : α × β →o α × β) :
    F.gfp = ((firstMap F (greatestSection F)).gfp,
      greatestSection F (firstMap F (greatestSection F)).gfp)

end Lax369799.FixedPointElimination
