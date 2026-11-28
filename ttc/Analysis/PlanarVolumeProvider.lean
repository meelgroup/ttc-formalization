/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.CommunityCV18VolumeProvider
import ttc.Analysis.PlanarAreaLaw

/-! The planar reference law satisfies TTC's component volume contract. -/

set_option autoImplicit false

noncomputable section

namespace ttc.Planar

open MeasureTheory

/-- The reference law for the planar component call, with the same accuracy
allocation, success tag and rescaling as the higher-dimensional call. -/
def taggedLaw (P : PolytopeData 2) (eta delta : ℝ) : Measure VolumeOutcome :=
  taggedVolumeLaw (areaLaw P (eta / 2) (delta / 2)) (CommunityCV18.successSet P eta) Real.toNNReal

theorem taggedLaw_spec (P : PolytopeData 2) (eta delta : ℝ)
    (h : CommunityCV18.AdmissibleCV18Request eta delta) :
    IsProbabilityMeasure (taggedLaw P eta delta) ∧
      (taggedLaw P eta delta).real {o | o.1 = false} ≤ delta ∧
      ∀ᵐ o ∂taggedLaw P eta delta, o.1 = true →
        (o.2 : ℝ) ∈ Arlib.relErr eta (volume P.cv18Body).toReal := by
  have hs := areaLaw_accuracy P (eps := eta / 2) (delta := delta / 2)
    (by linarith [h.1]) (by linarith [h.2.1])
    (by linarith [h.2.2.1]) (by linarith [h.2.2.2])
  have hsucc : 1 - delta ≤ (areaLaw P (eta / 2) (delta / 2)).real
      (CommunityCV18.successSet P eta) := by
    change 1 - delta ≤ (areaLaw P (eta / 2) (delta / 2)).real
      (Arlib.relErr (eta / 2) (volume P.cv18Body).toReal)
    linarith [h.2.2.1]
  have ha (x : ℝ) (hx : x ∈ CommunityCV18.successSet P eta) :
      (Real.toNNReal x : ℝ) ∈ Arlib.relErr eta (volume P.cv18Body).toReal := by
    change x ∈ Arlib.relErr (eta / 2) (volume P.cv18Body).toReal at hx
    have he : 0 ≤ (1 - eta / 2 : ℝ) := by linarith [h.2.1]
    have h0 : 0 ≤ x := (mul_nonneg he ENNReal.toReal_nonneg).trans (Arlib.relErr.lower hx)
    rw [Real.coe_toNNReal x h0]
    exact Arlib.relErr_subset_of_le ENNReal.toReal_nonneg (by linarith [h.1]) hx
  exact taggedVolumeLaw_spec _ measurableSet_Icc measurable_real_toNNReal hsucc ha

/-- Rescaling the planar estimate gives the volume contract needed by TTC. -/
theorem rescaledLaw_spec (P : PolytopeData 2) (eta delta : ℝ)
    (h : CommunityCV18.AdmissibleCV18Request eta delta) :
    IsProbabilityMeasure (P.rescaleCV18Law (taggedLaw P eta delta)) ∧
      (P.rescaleCV18Law (taggedLaw P eta delta)).real {o | o.1 = false} ≤ delta ∧
      ∀ᵐ o ∂P.rescaleCV18Law (taggedLaw P eta delta), o.1 = true →
        (o.2 : ℝ) ∈ Arlib.relErr eta (volume P.carrier).toReal := by
  obtain ⟨hp, hf, ha⟩ := taggedLaw_spec P eta delta h
  exact P.rescaleCV18Law_spec _ hf ha

/-- Install the planar volume law in the normalized component interface. -/
def provider : NormalizedCV18VolumeProvider 2 :=
  NormalizedCV18VolumeProvider.ofAdmissible
    (fun P eta delta _ => taggedLaw P eta delta)
    (fun P eta delta h => (taggedLaw_spec P eta delta h).1)
    (fun P eta delta h => (taggedLaw_spec P eta delta h).2.1)
    (fun P eta delta h => (taggedLaw_spec P eta delta h).2.2)

end ttc.Planar

namespace ttc

/-- Dimension two uses direct area sampling. Dimensions three and up use CV18. -/
def normalizedComponentVolumeProvider (n : ℕ) (hn : 2 ≤ n) :
    NormalizedCV18VolumeProvider n := by
  by_cases h : n = 2
  · subst n
    exact Planar.provider
  · exact CommunityCV18.provider n (by omega)

end ttc
