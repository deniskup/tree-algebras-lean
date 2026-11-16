import Lax369799.PolynomialContexts

/-!
---
title: Unit and associativity for deterministic substitution
type: theorem
---
Root-free deterministic substitution obeys the two unit laws and
associativity up to presentation isomorphism. Flattening also preserves
isomorphisms of the outer system.
-/

namespace Lax369799.SystemMonad
open RankedSystems Morphisms

axiom outer_unit {A : RankedSet} {n : ℕ} (S : System A n) (U : System A n)
    (hU : Flattening.SystemFlattening (atomicSystem S) U) : Isomorphic U.val S.val

axiom inner_unit {A : RankedSet} {n : ℕ} (S : System A n) (U : System A n)
    (hU : Flattening.SystemFlattening (relabelSystem (fun _ a => atomicSystem a) S) U) :
    Isomorphic U.val S.val

axiom associative {A : RankedSet} {n : ℕ} (P : System (System (System A)) n)
    (Q : System (System A) n) (U : System A n)
    (t : ∀ v : P.val.Vertex, System A (P.val.graph.label v).1) (W : System A n)
    (hQ : Flattening.SystemFlattening P Q)
    (hU : Flattening.SystemFlattening Q U)
    (ht : ∀ v, Flattening.SystemFlattening (P.val.graph.label v).2 (t v))
    (hW : Flattening.SystemFlattening (PolynomialContexts.withLabels P t) W) :
    Isomorphic U.val W.val

axiom flatten_isomorphic {A : RankedSet} {n : ℕ}
    (P Q : System (System A) n) (U W : System A n)
    (hP : Flattening.SystemFlattening P U) (hQ : Flattening.SystemFlattening Q W)
    (h : Isomorphic P.val Q.val) : Isomorphic U.val W.val

end Lax369799.SystemMonad
