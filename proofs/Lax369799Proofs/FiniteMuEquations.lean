import Lax369799.FiniteMuEquations
import Lax369799Proofs.MuSubstitution
import Lax369799Proofs.MuCalculus
import Lax369799Proofs.FixedPointElimination
import Mathlib.Data.Fin.Tuple.Basic

namespace Lax369799Proofs.FiniteMuEquations
set_option backward.isDefEq.respectTransparency false
open Lax369799
open ModalMuCalculus TransitionSystems MuSubstitution FixedPointElimination

open Lax369799.FiniteMuEquations

private def fixed {α : Type} [CompleteLattice α] : Binder → (α →o α) → α
  | .least, f => f.lfp
  | .greatest, f => f.gfp

private def equationMap {P : Type} (S : TransitionSystem P) {n m : ℕ}
    (φ : Fin n → Formula P (n + m)) (ρ : Fin m → Set S.Vertex) :
    (Fin n → Set S.Vertex) →o (Fin n → Set S.Vertex) where
  toFun := fun X i => (φ i).eval S (Fin.addCases X ρ)
  monotone' := by
    intro X Y h i
    apply MuCalculus.eval_monotone
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i; simpa using h i
    · intro i; simp

private theorem fixed_mono {α : Type} [CompleteLattice α] (b : Binder)
    {f g : α →o α} (h : f ≤ g) : fixed b f ≤ fixed b g := by
  cases b
  · exact OrderHom.lfp.monotone h
  · exact OrderHom.gfp.monotone h

private def sectionFixed {α β : Type} [CompleteLattice α] [CompleteLattice β]
    (b : Binder) (F : α × β →o α × β) : α →o β where
  toFun := fun a => fixed b (sectionMap F a)
  monotone' := fun a a' h => fixed_mono b
    (fun y => (F.monotone (show (a, y) ≤ (a', y) from ⟨h, le_rfl⟩)).2)

private theorem pair_fixed {α β : Type} [CompleteLattice α] [CompleteLattice β]
    (b : Binder) (F : α × β →o α × β) :
    fixed b F = (fixed b (firstMap F (sectionFixed b F)),
      sectionFixed b F (fixed b (firstMap F (sectionFixed b F)))) := by
  cases b
  · exact FixedPointElimination.least F
  · exact FixedPointElimination.greatest F

private def splitMap {α : Type} [CompleteLattice α] {n : ℕ}
    (F : (Fin (n + 1) → α) →o (Fin (n + 1) → α)) :
    α × (Fin n → α) →o α × (Fin n → α) where
  toFun := fun x => (F (Fin.cases x.1 x.2) 0, fun i => F (Fin.cases x.1 x.2) i.succ)
  monotone' := by
    intro x y h
    have hxy : (fun i : Fin (n + 1) => (Fin.cases x.1 x.2 i : α)) ≤
        (fun i : Fin (n + 1) => (Fin.cases y.1 y.2 i : α)) := by
      intro i
      exact Fin.cases h.1 (fun j => h.2 j) i
    have hh := F.monotone hxy
    exact ⟨hh 0, fun i => hh i.succ⟩

private theorem split_fixed {α : Type} [CompleteLattice α] {n : ℕ} (b : Binder)
    (F : (Fin (n + 1) → α) →o (Fin (n + 1) → α)) :
    fixed b F = Fin.cases (fixed b (splitMap F)).1 (fixed b (splitMap F)).2 := by
  have hc (X : Fin (n + 1) → α) : Fin.cases (X 0) (fun i => X i.succ) = X := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  cases b with
  | least =>
    apply le_antisymm
    · apply F.lfp_le
      have h := (splitMap F).map_lfp
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (congrArg Prod.fst h).le
      · exact (congrFun (congrArg Prod.snd h) j).le
    · have h : (splitMap F) (F.lfp 0, fun i => F.lfp i.succ) = (F.lfp 0, fun i => F.lfp i.succ) := by
        simp only [splitMap, OrderHom.coe_mk, hc, F.map_lfp]
      have hh := (splitMap F).lfp_le h.le
      intro i
      exact Fin.cases hh.1 (fun j => hh.2 j) i
  | greatest =>
    apply le_antisymm
    · have h : (splitMap F) (F.gfp 0, fun i => F.gfp i.succ) = (F.gfp 0, fun i => F.gfp i.succ) := by
        simp only [splitMap, OrderHom.coe_mk, hc, F.map_gfp]
      have hh := (splitMap F).le_gfp h.ge
      intro i
      exact Fin.cases hh.1 (fun j => hh.2 j) i
    · apply F.le_gfp
      have h := (splitMap F).map_gfp
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (congrArg Prod.fst h).ge
      · exact (congrFun (congrArg Prod.snd h) j).ge

private theorem move_environment {n m : ℕ} {α : Type}
    (X : Fin n → α) (a : α) (ρ : Fin m → α) :
    Fin.addCases X (Fin.cases a ρ) ∘ move n m = Fin.addCases (Fin.cases a X) ρ := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [move]
  · intro j
    simp [move]

private def bodyMap {P : Type} (S : TransitionSystem P) {m : ℕ}
    (φ : Formula P (m + 1)) (ρ : Fin m → Set S.Vertex) : Set S.Vertex →o Set S.Vertex where
  toFun := fun X => φ.eval S (Fin.cases X ρ)
  monotone' := by
    intro X Y h
    apply MuCalculus.eval_monotone
    intro i
    exact Fin.cases h (fun _ => Set.Subset.rfl) i

private theorem eval_bind {P : Type} (b : Binder) (S : TransitionSystem P) {m : ℕ}
    (φ : Formula P (m + 1)) (ρ : Fin m → Set S.Vertex) :
    (bind b φ).eval S ρ = fixed b (bodyMap S φ ρ) := by cases b <;> rfl

private theorem head_environment {P : Type} (S : TransitionSystem P) {n m : ℕ}
    (g : Fin n → Formula P (m + 1)) (a : Set S.Vertex) (ρ : Fin m → Set S.Vertex) :
    (fun i => (headSubstitution g i).eval S
      (Fin.cases a ρ)) = Fin.addCases (Fin.cases a (fun i => (g i).eval S (Fin.cases a ρ))) ρ := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [headSubstitution, Formula.eval]
  · intro j
    simp [headSubstitution, Formula.eval]

private theorem eval_head_substitution {P : Type} (S : TransitionSystem P) {m : ℕ}
    (φ : Formula P (m + 1)) (a : Formula P m) (ρ : Fin m → Set S.Vertex) :
    (substitute (Fin.cases a Formula.variable) φ).eval S ρ = φ.eval S (Fin.cases (a.eval S ρ) ρ) := by
  rw [MuSubstitution.eval_substitute]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem solve_fixed {P : Type} (b : Binder) (S : TransitionSystem P) {n m : ℕ}
    (φ : Fin n → Formula P (n + m)) (ρ : Fin m → Set S.Vertex) :
    (fun i => (solve b φ i).eval S ρ) = fixed b (equationMap S φ ρ) := by
  induction n generalizing m with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    let ψ := fun i : Fin n => rename (move n m) (φ i.succ)
    let g := solve b ψ
    let θ : Fin ((n + 1) + m) → Formula P (m + 1) :=
      Fin.addCases (Fin.cases (.variable 0) g) (fun j => .variable j.succ)
    let head := bind b (substitute θ (φ 0))
    let F := equationMap S φ ρ
    let K := splitMap F
    let s := sectionFixed b K
    let f := firstMap K s
    have ht (X : Set S.Vertex) : (fun i => (g i).eval S (Fin.cases X ρ)) = s X := by
      have h := ih ψ (Fin.cases X ρ)
      have hm : equationMap S ψ (Fin.cases X ρ) = sectionMap K X := by
        apply OrderHom.ext
        funext Y i
        change (rename (move n m) (φ i.succ)).eval S (Fin.addCases Y (Fin.cases X ρ)) =
          (φ i.succ).eval S (Fin.addCases (Fin.cases X Y) ρ)
        rw [MuSubstitution.eval_rename, move_environment]
      rw [hm] at h
      exact h
    have hh : head.eval S ρ = fixed b f := by
      rw [eval_bind]
      congr 1
      apply OrderHom.ext
      funext X
      change (substitute θ (φ 0)).eval S (Fin.cases X ρ) =
        (φ 0).eval S (Fin.addCases (Fin.cases X (s X)) ρ)
      rw [MuSubstitution.eval_substitute]
      change (φ 0).eval S
        (fun i => (headSubstitution g i).eval S
          (Fin.cases X ρ)) = _
      rw [head_environment, ht]
    have hf := (split_fixed b F).trans
      (congrArg (fun x : Set S.Vertex × (Fin n → Set S.Vertex) =>
        fun i : Fin (n + 1) => (Fin.cases x.1 x.2 i : Set S.Vertex)) (pair_fixed b K))
    apply Eq.trans ?_ hf.symm
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change head.eval S ρ = fixed b f
      exact hh
    · change (substitute (Fin.cases head Formula.variable) (g j)).eval S ρ = s (fixed b f) j
      rw [eval_head_substitution, hh]
      exact congrFun (ht (fixed b f)) j

/--
---
conclusion: Lax369799.FiniteMuEquations.solve_correct
---
Induct on the number of equations. Bekić's identity separates the head
from the tail. Renaming makes the head a parameter of the tail, and
capture-avoiding substitution inserts the resulting scalar solutions.
-/
theorem solve_correct {P : Type} (b : Binder) (S : TransitionSystem P) {n m : ℕ}
    (φ : Fin n → Formula P (n + m)) (ρ : Fin m → Set S.Vertex) :
    (fun i => (solve b φ i).eval S ρ) = value b S φ ρ := by
  cases b <;> exact solve_fixed _ S φ ρ

end Lax369799Proofs.FiniteMuEquations
