import Lax369799.FixedPointElimination

namespace Lax369799Proofs.FixedPointElimination
open Lax369799.FixedPointElimination
variable {α β : Type} [CompleteLattice α] [CompleteLattice β]

/--
---
conclusion: Lax369799.FixedPointElimination.least
---
The nested solution is a fixed point of the pair map. Every pre-fixed
pair bounds its second section, then its first solution, and hence the
entire nested solution.
-/
theorem least (F : α × β →o α × β) :
    F.lfp = ((firstMap F (leastSection F)).lfp,
      leastSection F (firstMap F (leastSection F)).lfp) := by
  let s := leastSection F
  let f := firstMap F s
  apply le_antisymm
  · apply F.lfp_le
    exact ⟨f.map_lfp.le, (sectionMap F f.lfp).map_lfp.le⟩
  · have hs : s F.lfp.1 ≤ F.lfp.2 :=
      (sectionMap F F.lfp.1).lfp_le (congrArg Prod.snd F.map_lfp).le
    have hf : f F.lfp.1 ≤ F.lfp.1 :=
      ((F.monotone (show (F.lfp.1, s F.lfp.1) ≤ F.lfp from ⟨le_rfl, hs⟩)).1).trans (congrArg Prod.fst F.map_lfp).le
    have ha := f.lfp_le hf
    exact ⟨ha, (s.monotone ha).trans hs⟩

/--
---
conclusion: Lax369799.FixedPointElimination.greatest
---
The dual argument compares post-fixed pairs with the nested greatest
solution.
-/
theorem greatest (F : α × β →o α × β) :
    F.gfp = ((firstMap F (greatestSection F)).gfp,
      greatestSection F (firstMap F (greatestSection F)).gfp) := by
  let s := greatestSection F
  let f := firstMap F s
  apply le_antisymm
  · have hs : F.gfp.2 ≤ s F.gfp.1 :=
      (sectionMap F F.gfp.1).le_gfp (congrArg Prod.snd F.map_gfp).ge
    have hf : F.gfp.1 ≤ f F.gfp.1 :=
      (congrArg Prod.fst F.map_gfp).ge.trans (F.monotone (show F.gfp ≤ (F.gfp.1, s F.gfp.1) from ⟨le_rfl, hs⟩)).1
    have ha := f.le_gfp hf
    exact ⟨ha, hs.trans (s.monotone ha)⟩
  · apply F.le_gfp
    exact ⟨f.map_gfp.ge, (sectionMap F f.gfp).map_gfp.ge⟩

end Lax369799Proofs.FixedPointElimination
