import Lax369799.FinitePresentations
import Lax369799.Flattening

/-!
---
title: Contexts over finite presentations
type: definition
---
A context has one distinguished hole vertex, with no restriction on its
marks, incident edges, or reachability. Composition and substitution retain
all vertices, so an unreachable hole remains available for a later
substitution that contributes roots.
-/

namespace Lax369799.FiniteContexts
open RankedSystems FinitePresentations
open Flattening (WithHole IsHole)

structure Context (A : RankedSet) (k n : ℕ) where
  system : FiniteSystem (WithHole A k) n
  one_hole : ∃! v, IsHole (system.graph.label v)

def substitution {A : RankedSet} {k : ℕ} (S : FiniteSystem A k) :
    RankedMap (WithHole A k) (FiniteSystem A) :=
  fun _ a => match a with
    | .inl a => FinitePresentations.atomic a
    | .inr ⟨h⟩ => h ▸ S

noncomputable def plug {A : RankedSet} {k n : ℕ} (C : Context A k n)
    (S : FiniteSystem A k) : FiniteSystem A n :=
  flatten (FinitePresentations.relabel (substitution S) C.system)

def insertion {A : RankedSet} {k n : ℕ} (C : Context A k n) :
    RankedMap (WithHole A n) (FiniteSystem (WithHole A k)) :=
  fun _ a => match a with
    | .inl a => FinitePresentations.atomic (Sum.inl a)
    | .inr ⟨h⟩ => h ▸ C.system

noncomputable def compositionSystem {A : RankedSet} {k n m : ℕ}
    (D : Context A n m) (C : Context A k n) : FiniteSystem (WithHole A k) m :=
  flatten (FinitePresentations.relabel (insertion C) D.system)

def interpretation {A B : RankedSet} {k : ℕ}
    (f : RankedMap B (FiniteSystem A)) (S : FiniteSystem A k) :
    RankedMap (WithHole B k) (FiniteSystem A) :=
  fun _ a => match a with
    | .inl b => f _ b
    | .inr ⟨h⟩ => h ▸ S

/-- Replace each ordinary label by its assigned finite presentation. -/
axiom extension {A B : RankedSet} (f : RankedMap B (FiniteSystem A))
    {k n : ℕ} (C : Context B k n) :
    ∃ D : Context A k n, ∀ S,
      Isomorphic (plug D S) (flatten (FinitePresentations.relabel (interpretation f S) C.system))

axiom composition {A : RankedSet} {k n m : ℕ}
    (D : Context A n m) (C : Context A k n) :
    ∃ E : Context A k m, E.system = compositionSystem D C ∧
      ∀ S, FinitePresentations.Isomorphic (plug E S) (plug D (plug C S))

end Lax369799.FiniteContexts
