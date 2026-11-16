import Lax369799.UnaryGraphEvaluation
import Lax369799Proofs.UnaryChains
import Lax369799Proofs.AlgebraicOmegaWords
import Lax369799Proofs.UnaryFactorization
import Lax369799Proofs.SetSystemAlgebras
import Lax369799Proofs.PresentationCovers

namespace Lax369799Proofs.UnaryGraphEvaluation
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet Presentation)
open FinitePresentations FiniteSyntacticAlgebra UnaryFactorization UnaryChains
open Lax369799.UnaryGraphEvaluation

private theorem singleton_apply {T : Type} (a b : T) : ({a} : Set T) b ↔ b = a := Iff.rfl

private theorem last_ne_cast {n : ℕ} (i : Fin n) : Fin.last n ≠ i.castSucc := i.castSucc_lt_last.ne'

private abbrev LoopVertex (m k : ℕ) := Fin (m + 1) ⊕ Fin (k + 1)

private def loopNext {m k : ℕ} : LoopVertex m k → LoopVertex m k :=
  Sum.elim (Fin.lastCases (.inr 0) (fun i => .inl i.succ))
    (Fin.lastCases (.inr 0) (fun i => .inr i.succ))

private def model {A : RankedSet} (w : ℕ → A 1) (m k : ℕ) :
    Presentation A 0 (LoopVertex m k) where
  label := Sum.elim (fun i => ⟨1, w i.val⟩) (fun i => ⟨1, w (m + 1 + i.val)⟩)
  initial := {.inl 0}
  root := ∅
  edge := fun v d t => d = 0 ∧ t = .inl (loopNext v)
  direction_valid := by
    rintro (v | v) d t ⟨rfl, _⟩ <;> exact Nat.zero_lt_one

private def pattern {A : RankedSet} (w : ℕ → A 1) (m k : ℕ) :
    FiniteSystem (FiniteSystem A) 0 := lasso (word w 0 m) (word w (m + 1) k)

private abbrev Raw {A : RankedSet} (w : ℕ → A 1) (m k : ℕ) :=
  (v : (pattern w m k).Vertex) × (Inner (pattern w m k).graph v).Vertex

private def rawEquiv {A : RankedSet} (w : ℕ → A 1) (m k : ℕ) :
    Raw w m k ≃ LoopVertex m k where
  toFun := fun v => Fin.cases (fun u => .inl u) (fun _ u => .inr u) v.1 v.2
  invFun := Sum.elim (fun u => ⟨(0 : Fin 2), u⟩) (fun u => ⟨(1 : Fin 2), u⟩)
  left_inv := by rintro ⟨v, u⟩; fin_cases v <;> rfl
  right_inv := by rintro (v | v) <;> rfl

private def rawIso {A : RankedSet} (w : ℕ → A 1) (m k : ℕ) :
    PresentationIso (flattenPresentation (pattern w m k).graph) (model w m k) where
  vertex := rawEquiv w m k
  label := by
    rintro ⟨v, u⟩
    fin_cases v
    · change (⟨1, w u.val⟩ : RankedSystems.Symbol A) = (word w 0 m).graph.label u
      simpa using (UnaryChains.word_label w 0 m u).symm
    · change (⟨1, w (m + 1 + u.val)⟩ : RankedSystems.Symbol A) =
        (word w (m + 1) k).graph.label u
      exact (UnaryChains.word_label w (m + 1) k u).symm
  initial := by
    rintro ⟨v, u⟩
    fin_cases v
    · change (Sum.inl u : LoopVertex m k) = .inl 0 ↔ (0 : Fin 2) = 0 ∧ u = (0 : Fin (m + 1))
      simp
    · change (Sum.inr u : LoopVertex m k) = .inl 0 ↔ (1 : Fin 2) = 0 ∧ u = (0 : Fin (k + 1))
      simp
  root := by
    rintro ⟨v, u⟩
    fin_cases v <;> exact ⟨False.elim, fun h => h.elim id (fun h => h.1)⟩
  edge := by
    rintro ⟨v, u⟩ d t
    cases t with
    | inr j => exact Fin.elim0 j
    | inl z =>
      obtain ⟨q, z⟩ := z
      fin_cases v <;> fin_cases q
      all_goals cases u using Fin.lastCases
      all_goals
        simp [model, loopNext, rawEquiv, pattern, flattenPresentation, Inner, lasso, word, path,
          Fin.exists_fin_one, Fin.exists_fin_two, Sigma.exists,
          Lax369799Proofs.UnaryComposition.cases_one, singleton_apply,
          Fin.val_inj, last_ne_cast]


private def loopMap {V : Type} (next : V → V) (start : V) (m k : ℕ) : LoopVertex m k → V :=
  Sum.elim (fun i => trace next start i.val) (fun i => trace next start (m + 1 + i.val))

private theorem loopMap_next {V : Type} (next : V → V) (start : V) (m k : ℕ)
    (hclose : trace next start (m + k + 2) = trace next start (m + 1)) (v : LoopVertex m k) :
    loopMap next start m k (loopNext v) = next (loopMap next start m k v) := by
  cases v with
  | inl u =>
    cases u using Fin.lastCases with
    | last => simp [loopMap, loopNext, trace]
    | cast i => simp [loopMap, loopNext, trace]
  | inr u =>
    cases u using Fin.lastCases with
    | last =>
      simp only [loopMap, loopNext, Sum.elim_inr, Fin.lastCases_last, Fin.val_last, Fin.val_zero]
      change trace next start (m + 1 + 0) = trace next start (m + 1 + k + 1)
      convert hclose.symm using 1 <;> congr 1 <;> omega
    | cast i => simp [loopMap, loopNext, trace, Nat.add_assoc]

private def cycleCover {A : RankedSet} {V : Type} (next : V → V) (start : V) (b : V → A 1)
    (m k : ℕ) (hclose : trace next start (m + k + 2) = trace next start (m + 1)) :
    Lax369799.PresentationCovers.Cover (model (b ∘ trace next start) m k) (graph next start b) where
  toFun := loopMap next start m k
  label := by rintro (v | v) <;> rfl
  initial := by intro v hv; change v = .inl 0 at hv; subst v; rfl
  root := by intro _ h; exact h.elim
  edge := by
    rintro v d t ⟨rfl, rfl⟩
    exact ⟨rfl, congrArg Sum.inl (loopMap_next next start m k hclose v)⟩
  initial_lift := by intro v hv; change v = start at hv; subst v; exact ⟨.inl 0, rfl, rfl⟩
  root_lift := by intro _ h; exact h.elim
  edge_lift := by
    rintro v d t ⟨rfl, rfl⟩
    exact ⟨.inl (loopNext v), ⟨rfl, rfl⟩, congrArg Sum.inl (loopMap_next next start m k hclose v)⟩

private theorem graph_reachable {A : RankedSet} {V : Type} (next : V → V) (start : V)
    (b : V → A 1) (hreach : ∀ v, ∃ n, trace next start n = v) :
    ∀ v, (graph next start b).Reachable v := by
  have htrace (n : ℕ) : (graph next start b).Reachable (trace next start n) := by
    induction n with
    | zero => exact ⟨start, Or.inl rfl, .refl⟩
    | succ n ih =>
      obtain ⟨r, hr, hp⟩ := ih
      exact ⟨r, hr, hp.tail ⟨0, rfl, rfl⟩⟩
  intro v
  obtain ⟨n, rfl⟩ := hreach v
  exact htrace n

private theorem model_evaluation {A : RankedSet} (E : Algebra A) (w : ℕ → A 1) (m k : ℕ) :
    E.eval 0 (enumerate (model w m k)) = E.eval 0 (lasso
      (UnaryFactorization.block E w 0 (m + 1))
      (UnaryFactorization.block E w (m + 1) (m + k + 2))) := by
  have hi : Isomorphic (flatten (pattern w m k)) (enumerate (model w m k)) :=
    ⟨UntrimmedFlattening.isoTrans
      (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))
      (UntrimmedFlattening.isoTrans (rawIso w m k)
        (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))⟩
  have hp : relabel E.eval (pattern w m k) = lasso (E.eval 1 (word w 0 m))
      (E.eval 1 (word w (m + 1) k)) := by
    dsimp only [pattern, relabel, lasso]
    congr 1
    congr 1
    funext v
    fin_cases v <;> rfl
  rw [← E.isomorphic 0 _ _ hi, ← E.associative, hp, UnaryChains.word_evaluation,
    UnaryChains.word_evaluation]
  congr 2 <;> congr 1 <;> omega

/--
---
conclusion: Lax369799.UnaryGraphEvaluation.cycle_folding
---
Expand the prefix and loop values into their word chains. Their flattening
covers the original graph; reachability makes the covering map globally
surjective. Associativity evaluates the two chains before the lasso.
-/
theorem cycle_folding {A : RankedSet} (E : Lax369799.SetSystemAlgebras.SetAlgebra A)
    {V : Type} [Fintype V] (next : V → V) (start : V) (b : V → A 1)
    (hreach : ∀ v, ∃ n, trace next start n = v) (m k : ℕ)
    (hclose : trace next start (m + k + 2) = trace next start (m + 1)) :
    E.eval 0 (enumerate (graph next start b)) = E.eval 0 (lasso
      (UnaryFactorization.block E.toAlgebra (b ∘ trace next start) 0 (m + 1))
      (UnaryFactorization.block E.toAlgebra (b ∘ trace next start) (m + 1) (m + k + 2))) := by
  have hf := PresentationCovers.surjective_of_reachable (cycleCover next start b m k hclose)
    (graph_reachable next start b hreach)
  exact (SetSystemAlgebras.raw_cover E (cycleCover next start b m k hclose) hf).symm.trans
    (model_evaluation E.toAlgebra (b ∘ trace next start) m k)


private theorem at_cuts {A : RankedSet} (E : Lax369799.SetSystemAlgebras.SetAlgebra A)
    {V : Type} [Fintype V] (next : V → V) (start : V) (b : V → A 1)
    (hreach : ∀ v, ∃ n, trace next start n = v) {p q : ℕ} (hp : 0 < p) (hpq : p < q)
    (hclose : trace next start q = trace next start p) :
    E.eval 0 (enumerate (graph next start b)) = E.eval 0 (lasso
      (UnaryFactorization.block E.toAlgebra (b ∘ trace next start) 0 p)
      (UnaryFactorization.block E.toAlgebra (b ∘ trace next start) p q)) := by
  have h1 : p - 1 + 1 = p := by omega
  have h2 : p - 1 + (q - p - 1) + 2 = q := by omega
  have h := cycle_folding E next start b hreach (p - 1) (q - p - 1) (by rwa [h1, h2])
  simpa only [h1, h2] using h

/--
---
conclusion: Lax369799.UnaryGraphEvaluation.agreement
---
Stable semigroup factorization yields an accepting linked pair from graph
evaluation. Conversely, thin an accepting factorization to a recurrent
vertex and fold its prefix and loop back to the graph.
-/
theorem agreement {A : RankedSet} (E : Lax369799.SetSystemAlgebras.SetAlgebra A)
    (F : Set (A 0)) [Finite (A 1)] {V : Type} [Fintype V]
    (next : V → V) (start : V) (b : V → A 1) (hreach : ∀ v, ∃ n, trace next start n = v) :
    E.eval 0 (enumerate (graph next start b)) ∈ F ↔
      AlgebraicOmegaWords.Accepts E.toAlgebra F (b ∘ trace next start) := by
  constructor
  · intro hacc
    obtain ⟨c, a, e, r, hc, hpos, hee, hae, hvr, hp, hb⟩ :=
      UnaryFactorization.stable_factorization E.toAlgebra (b ∘ trace next start) (trace next start)
    have hfold := at_cuts E next start b hreach hpos (hc (by decide : 0 < 1))
      ((hvr 1).trans (hvr 0).symm)
    rw [hp 0, hb 0 1 (by decide)] at hfold
    exact ⟨a, e, c, hfold ▸ hacc, hee, hae, hc, hpos, hp 0,
      fun i => hb i (i + 1) (Nat.lt_succ_self _)⟩
  · intro h
    obtain ⟨a, e, c, r, hacc, _, _, hc, hpos, hvr, hp, hb⟩ :=
      AlgebraicOmegaWords.recurrent_factorization E.toAlgebra F (b ∘ trace next start) (trace next start) h
    have hfold := at_cuts E next start b hreach hpos (hc (by decide : 0 < 1))
      ((hvr 1).trans (hvr 0).symm)
    rw [hp 0, hb 0 1 (by decide)] at hfold
    exact hfold.symm ▸ hacc

end Lax369799Proofs.UnaryGraphEvaluation
