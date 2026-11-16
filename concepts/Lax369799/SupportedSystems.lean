import Lax369799.FinitePresentations
import Lax369799.FlatteningTheorems
import Lax369799.Renaming

/-!
---
title: Systems with all output variables reachable
type: theorem
---
Definition 6 requires every vertex and every output variable to be
reachable from the unique initial vertex. The earlier deterministic
presentation interface already requires vertex reachability; full support
adds occurrence of every variable edge. Relabelling and surjective
renaming preserve this condition. Flattening fully supported systems
retains all vertices and all output variables (Lemma 33). In rank zero,
the support condition is vacuous.
-/

namespace Lax369799.SupportedSystems
open RankedSystems (RankedSet RankedMap)
open FinitePresentations

def FullySupported {A : RankedSet} {n : ℕ} (S : RankedSystems.System A n) : Prop :=
  ∀ i : Fin n, ∃ v d, S.val.graph.edge v d (.inr i)

abbrev System (A : RankedSet) (n : ℕ) := {S : RankedSystems.System A n // FullySupported S}

def forget {A : RankedSet} : RankedMap (System A) (RankedSystems.System A) := fun _ S => S.val

def relabel {A B : RankedSet} (f : RankedMap A B) {n : ℕ} (S : System A n) : System B n :=
  ⟨RankedSystems.relabelSystem f S.val, S.property⟩

def atomic {A : RankedSet} {n : ℕ} (a : A n) : System A n :=
  ⟨RankedSystems.atomicSystem a, fun i => ⟨(0 : Fin 1), i.val, i, rfl, rfl⟩⟩

def closedEquiv (A : RankedSet) : System A 0 ≃ RankedSystems.System A 0 where
  toFun := Subtype.val
  invFun := fun S => ⟨S, fun i => Fin.elim0 i⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def rename {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Surjective σ) (S : System A m) : System A n :=
  ⟨Renaming.renameSystem σ S.val, fun j => by
    obtain ⟨i, rfl⟩ := hσ j
    obtain ⟨v, d, hd⟩ := S.property i
    exact ⟨v, d, .inr i, hd, rfl⟩⟩

def pattern {A : RankedSet} {n : ℕ} (S : System (System A) n) :
    FiniteSystem (FiniteSystem A) n :=
  FinitePresentations.relabel (fun _ T => ofSetSystem T.val.val) (ofSetSystem S.val.val)

def forgetPattern {A : RankedSet} {n : ℕ} (S : System (System A) n) :
    RankedSystems.System (RankedSystems.System A) n :=
  RankedSystems.relabelSystem forget S.val

axiom flatten_reachable {A : RankedSet} {n : ℕ} (S : System (System A) n) :
    ∀ v, (flattenPresentation (pattern S).graph).Reachable v

axiom flatten_system {A : RankedSet} {n : ℕ} (S : System (System A) n) :
    ∃ T : System A n, Flattening.SystemFlattening (forgetPattern S) T.val

end Lax369799.SupportedSystems
