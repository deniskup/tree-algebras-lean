import Lax369799.SupportPorts

/-!
---
title: Isomorphisms of deterministic substitutions
type: theorem
---
Isomorphisms between deterministic presentations, their reachable
restrictions, and their flattenings. Output renaming commutes with
flattening up to presentation isomorphism.
-/

namespace Lax369799.SystemIsomorphisms
open RankedSystems Morphisms Renaming FinitePresentations

axiom injective_isomorphic {A : RankedSet} {n : ℕ} (S T : System A n)
    (f : Morphism S.val T.val) (hf : Function.Injective f.toFun) : Isomorphic S.val T.val

axiom iso_symm {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (h : Isomorphic S T) : Isomorphic T S

axiom iso_trans {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (hST : Isomorphic S T) (hTU : Isomorphic T U) : Isomorphic S U

axiom trim_isomorphic {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : PresentationIso G H)
    (hG : (trim G).Deterministic) (hH : (trim H).Deterministic) :
    Isomorphic (trim G) (trim H)

axiom flatten_output_rename {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (P : System (System A) m) (U : System A m) (W : System A n)
    (hU : Flattening.SystemFlattening P U)
    (hW : Flattening.SystemFlattening (Renaming.renameSystem σ P) W) :
    Isomorphic (Renaming.renameSystem σ U).val W.val

axiom flatten_from_trim {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation (System A) n V) (r : V) (hi : G.initial = {r}) (hr : G.root = ∅)
    (ht : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t)
    (P : System (System A) n) (hP : P.val = trim G)
    (U : System A n) (hU : Flattening.SystemFlattening P U) :
    Isomorphic U.val (trim (SupportPorts.flattened G))

end Lax369799.SystemIsomorphisms
