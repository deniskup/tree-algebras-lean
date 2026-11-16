import Lax369799.SupportedYields
import Lax369799.SupportedSystems
import Lax369799.SupportedCompletion
import Lax369799.Resolutions

/-!
---
title: Flatten-resolutions with supported systems and explicit output maps
type: theorem
---
The four conditions of Lemma 46 specify an outer vertex map, local
variable maps and yields, preservation of initial vertices and transitions,
and preservation of output edges through the prescribed global map.
Both levels of the resolving system are fully supported.
-/

namespace Lax369799.SupportedResolutions
open RankedSystems (RankedSet)
open FinitePresentations SupportedMorphisms

structure Resolution {A : RankedSet} {m n : ℕ} (S : FiniteSystem (FiniteSystem A) n)
    (T : SupportedSystems.System (SupportedSystems.System A) m) (τ : Fin m → Fin n) where
  vertex : T.val.val.Vertex → S.Vertex
  variableMap : ∀ v, Fin (T.val.val.graph.label v).1 → Fin (S.graph.label (vertex v)).1
  initial : ∀ v,T.val.val.graph.initial v → S.graph.initial (vertex v)
  resolves : ∀ v, SupportedYields.InitialYield (Inner S.graph (vertex v))
    (T.val.val.graph.label v).2 (variableMap v)
  transition : ∀ v (i : Fin (T.val.val.graph.label v).1) w,
    T.val.val.graph.edge v i.val (.inl w) → S.graph.edge (vertex v) (variableMap v i).val (.inl (vertex w))
  exit : ∀ v (i : Fin (T.val.val.graph.label v).1) j,
    T.val.val.graph.edge v i.val (.inr j) → S.graph.edge (vertex v) (variableMap v i).val (.inr (τ j))

open SupportedYields

axiom sound {A : RankedSet} {m n : ℕ} (S : FiniteSystem (FiniteSystem A) n)
    (T : SupportedSystems.System (SupportedSystems.System A) m) (τ : Fin m → Fin n)
    (r : Resolution S T τ) (V : SupportedSystems.System A m)
    (hV : Flattening.SystemFlattening (SupportedSystems.forgetPattern T) V.val) :
    InitialYield (flatten S) V τ

open RankedSystems (RankwiseFinite RankedMap)
open Resolutions

axiom small_resolution {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B)
    (S : FiniteSystem (FiniteSystem A) 0)
    (T : SupportedSystems.System (SupportedSystems.System A) 0) (r : Resolution S T Fin.elim0)
    (R : SupportedSystems.System A 0)
    (hR : Flattening.SystemFlattening (SupportedSystems.forgetPattern T) R.val) :
    ∃ (U : SupportedSystems.System (SupportedSystems.System A) 0)
      (V : SupportedSystems.System A 0) (r' : Resolution S U Fin.elim0),
      Flattening.SystemFlattening (SupportedSystems.forgetPattern U) V.val ∧
      (∀ v,SmallMap B (r'.variableMap v)) ∧
      E.eval 0 (SupportedSystems.relabel η R) = E.eval 0 (SupportedSystems.relabel η V)

end Lax369799.SupportedResolutions
