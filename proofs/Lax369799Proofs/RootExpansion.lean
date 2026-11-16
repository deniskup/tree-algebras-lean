import Lax369799.RootExpansion

namespace Lax369799Proofs.RootExpansion
open Lax369799.RankedSystems Lax369799.FinitePresentations Lax369799.PresentationCovers
open Lax369799.RootExpansion

noncomputable def expansionCover {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FiniteSystem A) n V) :
    Cover (flattenPresentation (pattern P)) (startAtRoots (flattenPresentation P)) where
  toFun := fun v => ⟨v.1.2, v.2⟩
  label := fun _ => rfl
  initial := by
    rintro ⟨⟨b, v⟩, w⟩ ⟨hv, hw⟩
    cases b with
    | false => exact Or.inr ⟨hv, hw⟩
    | true => exact Or.inl hw
  root := by
    intro v hv
    rcases hv with hv | ⟨hv, _⟩
    · exact False.elim hv
    · exact False.elim hv
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · exact Or.inl ⟨w, hw, rfl⟩
    · refine Or.inr ⟨i, hi, ?_⟩
      rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
      · obtain ⟨s, hs, he⟩ := hw
        cases s with
        | inr j => cases he
        | inl x =>
          have he : w.1 = (false, x) := Sum.inl.inj he
          obtain ⟨⟨b, y⟩, z⟩ := w
          cases he
          exact Or.inl ⟨⟨x, z⟩, hs, hw', rfl⟩
      · obtain ⟨s, hs, he⟩ := hj
        cases s with
        | inl w => cases he
        | inr a => cases Sum.inr.inj he; exact Or.inr ⟨a, hs, rfl⟩
  initial_lift := by
    rintro ⟨v, w⟩ (hw | ⟨hv, hw⟩)
    · exact ⟨⟨(true, v), w⟩, ⟨True.intro, hw⟩, rfl⟩
    · exact ⟨⟨(false, v), w⟩, ⟨hv, hw⟩, rfl⟩
  root_lift := by intro v hv; exact False.elim hv
  edge_lift := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · exact ⟨.inl ⟨v.1, w⟩, Or.inl ⟨w, hw, rfl⟩, rfl⟩
    · rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
      · exact ⟨.inl ⟨(false, w.1), w.2⟩,
          Or.inr ⟨i, hi, Or.inl ⟨⟨(false, w.1), w.2⟩,
            ⟨.inl w.1, hw, rfl⟩, hw', rfl⟩⟩, rfl⟩
      · exact ⟨.inr j, Or.inr ⟨i, hi, Or.inr ⟨j, ⟨.inr j, hj, rfl⟩, rfl⟩⟩, rfl⟩

/--
---
conclusion: Lax369799.RootExpansion.expansion_cover
---
Forget whether a vertex belongs to a starting or an ordinary copy.
Internal edges stay in that copy; substituted outer edges enter an ordinary
copy. Inner and outer roots have the two specified initial preimages.
-/
theorem expansion_cover {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FiniteSystem A) n V) :
    Nonempty (Cover (flattenPresentation (pattern P))
      (startAtRoots (flattenPresentation P))) := ⟨expansionCover P⟩

/--
---
conclusion: Lax369799.RootExpansion.expansion_folding
---
Every target vertex has its ordinary-copy preimage, whether reachable or
unreachable. Thus the root-expansion cover is a folding (Lemma 38).
-/
theorem expansion_folding {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FiniteSystem A) n V) :
    ∃ f : Cover (flattenPresentation (pattern P))
      (startAtRoots (flattenPresentation P)), Function.Surjective f.toFun :=
  ⟨expansionCover P,fun w => ⟨⟨(false,w.1),w.2⟩,rfl⟩⟩

end Lax369799Proofs.RootExpansion
