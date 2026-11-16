import Lax369799.SubstitutionProfiles
import Lax369799Proofs.SupportIsomorphism
import Lax369799Proofs.SystemIsomorphisms
import Lax369799.PolynomialContexts

namespace Lax369799Proofs.SubstitutionProfiles
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems Morphisms
open SupportedAlgebras
open SupportEvaluation (Equivalent profile)
open Lax369799Proofs.Pullbacks Lax369799Proofs.DeterministicNormalForms
open Lax369799Proofs.SystemIsomorphisms

private def Tag {V : Type} (m : V → ℕ) : RankedSet := fun k => {v : V // m v = k}

private def tagged {A : RankedSet} {n : ℕ} {V : Type} (G : Presentation A n V)
    (m : V → ℕ) (σ : ∀ v, Fin (m v) → Fin (G.label v).1) : Presentation (Tag m) n V where
  label := fun v => ⟨m v,⟨v,rfl⟩⟩
  initial := G.initial
  root := G.root
  edge := fun v d t => ∃ i : Fin (m v), d = i.val ∧ G.edge v (σ v i).val t
  direction_valid := by rintro v d t ⟨i,rfl,_⟩; exact i.isLt

private def assign {B : RankedSet} {V : Type} {m : V → ℕ}
    (q : ∀ v, SupportedSystems.System B (m v)) : RankedMap (Tag m) (SupportedSystems.System B) :=
  fun _ t => t.property ▸ q t.val

private def forgetAssign {B : RankedSet} {V : Type} {m : V → ℕ}
    (q : ∀ v, SupportedSystems.System B (m v)) : RankedMap (Tag m) (System B) :=
  fun k t => (assign q k t).val

private theorem restricted_total {A : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation A n V) (m : V → ℕ) (σ : ∀ v, Fin (m v) → Fin (G.label v).1)
    (ht : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t) :
    ∀ v d, d < m v → ∃! t, (tagged G m σ).edge v d t := by
  intro v d hd
  let i : Fin (m v) := ⟨d,hd⟩
  obtain ⟨t,hvt,hu⟩ := ht v (σ v i).val (σ v i).isLt
  refine ⟨t,⟨i,rfl,hvt⟩,?_⟩
  rintro u ⟨j,hj,he⟩
  have hji : j = i := Fin.ext hj.symm
  subst j
  exact hu u he

private theorem normalize {A B : RankedSet} {n k : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (m : V → ℕ) (σ : ∀ v, Fin (m v) → Fin (G.label v).1)
    (r : V) (hi : G.initial = {r}) (hr : G.root = ∅)
    (ht : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t)
    (R : System (Tag m) n) (hR : R.val = trim (tagged G m σ))
    (T : SupportedSystems.System (Tag m) k) (τ : Fin k → Fin n)
    (hT : Renaming.renameSystem τ T.val = R)
    (q : ∀ v, SupportedSystems.System B (m v))
    (F : System B n)
    (hF : F.val = trim (rawFlatten (SupportPorts.expanded G m σ (fun v => (q v).val)))) :
    ∃ W : SupportedSystems.System B k,
      Isomorphic F.val (Renaming.renameSystem τ W.val).val ∧
      ∀ E : Algebra B, E.eval k W = E.eval k
        (SupportedSystems.relabel (fun j t => E.eval j (assign q j t)) T) := by
  classical
  let O := SupportedSystems.relabel (assign q) T
  obtain ⟨W,hW⟩ := SupportedSystems.flatten_system O
  refine ⟨W,?_,fun E => ?_⟩
  · let f := forgetAssign q
    let H := SupportPorts.restricted G m σ (fun v => (q v).val)
    have hHtotal : ∀ v d, d < (H.label v).1 → ∃! t, H.edge v d t :=
      restricted_total G m σ ht
    have hP : (relabelSystem f R).val = trim H := by
      change relabel f R.val = _
      rw [hR]
      rfl
    have hOuter : Renaming.renameSystem τ (SupportedSystems.forgetPattern O) =
        relabelSystem f R := by
      apply Subtype.ext
      change Resolutions.rename τ (relabel f T.val.val) = relabel f R.val
      rw [Renaming.rename_relabel]
      exact congrArg (fun U : System (Tag m) n => (relabelSystem f U).val) hT
    obtain ⟨Z,hZ⟩ := Flattening.flatten_system (relabelSystem f R)
    have hZ' : Lax369799.Flattening.SystemFlattening
        (Renaming.renameSystem τ (SupportedSystems.forgetPattern O)) Z := by
      rw [hOuter]
      exact hZ
    have hisoRen := flatten_output_rename τ (SupportedSystems.forgetPattern O) W.val Z hW hZ'
    have hisoRaw := flatten_from_trim H r hi hr hHtotal (relabelSystem f R) hP Z hZ
    have hFRaw : Isomorphic F.val (trim (SupportPorts.flattened H)) := by
      rw [hF]
      obtain ⟨I⟩ := SupportPorts.flatten_iso G m σ (fun v => (q v).val)
      have hdet : (trim (SupportPorts.flattened
        (SupportPorts.expanded G m σ (fun v => (q v).val)))).Deterministic := hF ▸ F.property
      exact trim_isomorphic I hdet (RawSystemFlattening.deterministic H r hi hr hHtotal)
    exact iso_trans hFRaw (iso_symm (iso_trans hisoRen hisoRaw))
  · exact (E.associative k O W hW).symm

/--
---
conclusion: Lax369799.SubstitutionProfiles.pointwise_congruence
---
Factor the restricted outer template through one supported system.
Associativity evaluates its two labellings equally, while port restriction,
trimming, and output renaming identify the original flattened profiles.
-/
theorem pointwise_congruence {A B : RankedSet} (E : Algebra B) {n : ℕ}
    (P : System A n) (q s : ∀ v, System B (P.val.graph.label v).1)
    (hqs : ∀ v, Equivalent E (q v) (s v))
    (F H : System B n)
    (hF : Lax369799.Flattening.SystemFlattening (PolynomialContexts.withLabels P q) F)
    (hH : Lax369799.Flattening.SystemFlattening (PolynomialContexts.withLabels P s) H) :
    Equivalent E F H := by
  classical
  have hex := fun v => (SupportEvaluation.equivalent_iff E (q v) (s v)).mp (hqs v)
  choose m σ hσ U W hU hW he using hex
  obtain ⟨r,hi⟩ := P.property.1
  let G := P.val.graph
  have ht := restricted_total G m σ P.property.2.2
  let R : System (Tag m) n := ⟨trim (tagged G m σ),Yields.trim_deterministic
    (tagged G m σ) r hi P.property.2.1 ht⟩
  obtain ⟨k,τ,T,hτ,hT⟩ := SupportCompaction.compact_exists R
  have hq : q = fun v => Renaming.renameSystem (σ v) (U v).val := funext (fun v => (hU v).symm)
  have hs : s = fun v => Renaming.renameSystem (σ v) (W v).val := funext (fun v => (hW v).symm)
  rw [hq] at hF
  rw [hs] at hH
  obtain ⟨UF,hIF,hEF⟩ := normalize G m σ r hi P.property.2.1 P.property.2.2 R rfl T τ hT U F hF
  obtain ⟨WH,hIH,hEH⟩ := normalize G m σ r hi P.property.2.1 P.property.2.2 R rfl T τ hT W H hH
  have hval : E.eval k UF = E.eval k WH := by
    rw [hEF E,hEH E]
    have heq : (fun j t => E.eval j (assign U j t)) = (fun j t => E.eval j (assign W j t)) := by
      funext j t
      obtain ⟨v,hv⟩ := t
      cases hv
      exact he v
    rw [heq]
  have hCore := (SupportEvaluation.equivalent_iff E _ _).mpr
    ⟨k,τ,hτ,UF,WH,rfl,rfl,hval⟩
  have hFE := SupportIsomorphism.profile_isomorphic E F _ hIF
  have hHE := SupportIsomorphism.profile_isomorphic E H _ hIH
  exact hFE.trans (hCore.trans hHE.symm)

end Lax369799Proofs.SubstitutionProfiles
