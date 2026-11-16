import Lax369799.SupportedAlgebras
import Lax369799Proofs.SupportedSystems
import Lax369799Proofs.SystemIsomorphisms

namespace Lax369799Proofs.SupportedAlgebras
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet RankedMap)
open SupportedSystems Morphisms Flattening
open Lax369799.SupportedAlgebras
open Lax369799Proofs.Pullbacks

/--
---
conclusion: Lax369799.SupportedAlgebras.restrict_invariant
---
-/
theorem restrict_invariant {A : RankedSet} (E : Algebras.Algebra A)
    (hE : Algebras.UnfoldInvariant E) : UnfoldInvariant (restrict E) :=
  fun n S T h => hE n S.val T.val h

/--
---
conclusion: Lax369799.SupportedAlgebras.legacy_recognizable
---
-/
theorem legacy_recognizable {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.Recognizable L) : Recognizable L := by
  obtain ⟨B, E, η, F, hB, hrec⟩ := hL
  exact ⟨B, restrict E, η, F, hB, fun T => hrec T.val⟩

/--
---
conclusion: Lax369799.SupportedAlgebras.rename_evaluation
---
The renamed atomic substitution is isomorphic to the renamed inner
system. Isomorphism invariance and associativity give the equality.
-/
theorem rename_evaluation {A : RankedSet} (E : Algebra A)
    {m n : ℕ} (σ : Fin m → Fin n) (hσ : Function.Surjective σ) (S : System A m) :
    E.eval n (rename σ hσ S) =
      E.eval n (rename σ hσ (atomic (E.eval m S))) := by
  let O := rename σ hσ (atomic S)
  obtain ⟨U,hU⟩ := Lax369799Proofs.SupportedSystems.flatten_system O
  have hI := SystemIsomorphisms.renamed_iso σ S.val U.val hU
  have he := E.isomorphic n U (rename σ hσ S) hI
  exact he.symm.trans (E.associative n O U hU).symm

end Lax369799Proofs.SupportedAlgebras
