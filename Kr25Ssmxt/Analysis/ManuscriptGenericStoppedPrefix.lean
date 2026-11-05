import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ManuscriptStoppedPrefixSource

/-! A stopped-prefix/fresh-tail lemma for any almost surely prefix-adapted
round, independent of the manuscript's particular first-exit formula. -/

namespace Kr25Ssmxt

open MeasureTheory Function

theorem fairCoinStreamLaw_generic_stoppedPrefix_shift_law
    (stop : (Nat × Nat → Bool) → Nat)
    (hstop : Measurable stop)
    (event : Nat → Set (Nat × Nat → Bool))
    (hevent : ∀ r, MeasurableSet (event r))
    (hprefix : ∀ r, (coinPrefix r) ⁻¹' (event r) = event r)
    (hae : ∀ r, ∀ᵐ coins ∂fairCoinStreamLaw,
      (stop coins = r ↔ coins ∈ event r)) :
    fairCoinStreamLaw.map
      (fun coins =>
        (coinPrefix (stop coins) coins,
          shiftCoins (stop coins) coins)) =
    (fairCoinStreamLaw.map (fun coins => coinPrefix (stop coins) coins)).prod
      fairCoinStreamLaw := by
  classical
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let observed : (Nat × Nat → Bool) → Nat × Nat → Bool :=
    fun coins => coinPrefix (stop coins) coins
  let output : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun coins => (observed coins, shiftCoins (stop coins) coins)
  have hobserved : Measurable observed := by
    have hprefixJoint : Measurable
        (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
      apply measurable_from_prod_countable_right
      intro rounds
      exact measurable_coinPrefix rounds
    exact hprefixJoint.comp (hstop.prodMk measurable_id)
  have houtput : Measurable output :=
    hobserved.prodMk ((measurable_stoppedCoinPair stop hstop).snd)
  letI : IsProbabilityMeasure (fairCoinStreamLaw.map output) :=
    Measure.isProbabilityMeasure_map houtput.aemeasurable
  apply Measure.ext_prod
  intro A B hA hB
  let fiber (r : Nat) : Set (Nat × Nat → Bool) :=
    {coins | stop coins = r}
  let F (r : Nat) : Set (Nat × Nat → Bool) :=
    fiber r ∩ (coinPrefix r) ⁻¹' A
  let E (r : Nat) : Set (Nat × Nat → Bool) :=
    F r ∩ (shiftCoins r) ⁻¹' B
  have hfiber (r : Nat) : MeasurableSet (fiber r) :=
    (measurableSet_singleton r).preimage hstop
  have hF (r : Nat) : MeasurableSet (F r) :=
    (hfiber r).inter (hA.preimage (measurable_coinPrefix r))
  have hE (r : Nat) : MeasurableSet (E r) :=
    (hF r).inter (hB.preimage
      (Measurable.of_eval (fun index =>
        measurable_pi_apply (index.1 + r, index.2))))
  have hdisjF : Pairwise (Disjoint on F) := by
    intro r q hrq
    apply Set.disjoint_left.mpr
    intro coins hr hq
    exact hrq (hr.1.symm.trans hq.1)
  have hdisjE : Pairwise (Disjoint on E) := by
    intro r q hrq
    exact (hdisjF hrq).mono (Set.inter_subset_left) (Set.inter_subset_left)
  have hF_union : (⋃ r, F r) = observed ⁻¹' A := by
    ext coins
    simp only [Set.mem_iUnion, Set.mem_preimage, F, fiber,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, hr, hApre⟩
      simpa [observed, hr] using hApre
    · intro hApre
      exact ⟨stop coins, rfl, hApre⟩
  have hE_union : (⋃ r, E r) = output ⁻¹' (A ×ˢ B) := by
    ext coins
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_prod,
      E, F, fiber, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, ⟨hr, ha⟩, hb⟩
      simpa [output, observed, hr] using
        (show coinPrefix r coins ∈ A ∧ shiftCoins r coins ∈ B from ⟨ha, hb⟩)
    · rintro ⟨ha, hb⟩
      exact ⟨stop coins, ⟨rfl, ha⟩, hb⟩
  have hterm (r : Nat) :
      fairCoinStreamLaw (E r) =
        fairCoinStreamLaw (F r) * fairCoinStreamLaw B := by
    let G : Set (Nat × Nat → Bool) :=
      event r ∩ (coinPrefix r) ⁻¹' A
    have hG : MeasurableSet G :=
      (hevent r).inter (hA.preimage (measurable_coinPrefix r))
    have hprefixG : (coinPrefix r) ⁻¹' G = G := by
      ext coins
      simp only [Set.mem_preimage, G, Set.mem_inter_iff]
      have hEvent : coinPrefix r coins ∈ event r ↔ coins ∈ event r :=
        Set.ext_iff.mp (hprefix r) coins
      have hprefixId : coinPrefix r (coinPrefix r coins) =
          coinPrefix r coins := by
        funext index
        simp [coinPrefix]
      simpa only [hprefixId] using and_congr hEvent Iff.rfl
    have hF_eq : fairCoinStreamLaw (F r) = fairCoinStreamLaw G := by
      apply measure_congr
      filter_upwards [hae r] with coins hc
      exact propext (and_congr hc Iff.rfl)
    have hE_eq : fairCoinStreamLaw (E r) =
        fairCoinStreamLaw (G ∩ (shiftCoins r) ⁻¹' B) := by
      apply measure_congr
      filter_upwards [hae r] with coins hc
      exact propext (and_congr (and_congr hc Iff.rfl) Iff.rfl)
    rw [hE_eq, ← hprefixG]
    rw [fairCoinStreamLaw_prefix_shift_indep r G B hG hB]
    rw [hprefixG, ← hF_eq]
  have hF_measure : fairCoinStreamLaw (observed ⁻¹' A) =
      ∑' r, fairCoinStreamLaw (F r) := by
    rw [← hF_union]
    exact measure_iUnion hdisjF hF
  have hE_measure : fairCoinStreamLaw (output ⁻¹' (A ×ˢ B)) =
      ∑' r, fairCoinStreamLaw (E r) := by
    rw [← hE_union]
    exact measure_iUnion hdisjE hE
  rw [Measure.map_apply houtput (hA.prod hB), hE_measure]
  rw [Measure.prod_prod, Measure.map_apply hobserved hA, hF_measure]
  simp_rw [hterm]
  simp only [mul_comm (fairCoinStreamLaw (F _)) (fairCoinStreamLaw B)]
  rw [ENNReal.tsum_mul_left, mul_comm]

/-- The complete future component source is independent of the observed
prefix at any almost surely prefix-adapted stopping round. -/
theorem fairCoinStreamLaw_generic_stoppedPrefix_globalFuture_law
    (stop : (Nat × Nat → Bool) → Nat)
    (hstop : Measurable stop)
    (event : Nat → Set (Nat × Nat → Bool))
    (hevent : ∀ r, MeasurableSet (event r))
    (hprefix : ∀ r, (coinPrefix r) ⁻¹' (event r) = event r)
    (hae : ∀ r, ∀ᵐ coins ∂fairCoinStreamLaw,
      (stop coins = r ↔ coins ∈ event r)) :
    fairCoinStreamLaw.map
      (fun coins =>
        (coinPrefix (stop coins) coins,
          manuscriptGlobalCoinRead (shiftCoins (stop coins) coins))) =
    (fairCoinStreamLaw.map
      (fun coins => coinPrefix (stop coins) coins)).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let observed : (Nat × Nat → Bool) → Nat × Nat → Bool :=
    fun coins => coinPrefix (stop coins) coins
  let split : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun coins => (observed coins, shiftCoins (stop coins) coins)
  let reindex : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) :=
    Prod.map id manuscriptGlobalCoinRead
  have hsplit : Measurable split := by
    have hprefixJoint : Measurable
        (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
      apply measurable_from_prod_countable_right
      intro rounds
      exact measurable_coinPrefix rounds
    exact (hprefixJoint.comp (hstop.prodMk measurable_id)).prodMk
      ((measurable_stoppedCoinPair stop hstop).snd)
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk
      (measurable_manuscriptGlobalCoinRead.comp measurable_snd)
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          (observed coins,
            manuscriptGlobalCoinRead (shiftCoins (stop coins) coins))) =
      (fairCoinStreamLaw.map split).map reindex := by
        rw [Measure.map_map hreindex hsplit]
        rfl
    _ = ((fairCoinStreamLaw.map observed).prod fairCoinStreamLaw).map
          reindex := by
        rw [fairCoinStreamLaw_generic_stoppedPrefix_shift_law stop hstop
          event hevent hprefix hae]
    _ = ((fairCoinStreamLaw.map observed).map id).prod
          (fairCoinStreamLaw.map manuscriptGlobalCoinRead) := by
        exact (Measure.map_prod_map _ fairCoinStreamLaw measurable_id
          measurable_manuscriptGlobalCoinRead).symm
    _ = _ := by
      rw [Measure.map_id, fairCoinStreamLaw_globalCoinRead]

/-- Prefix adaptation of the first-exit event survives any read of a larger
source that respects the time coordinate. This is the deterministic part of
applying the strong Markov lemma to a joint source encoding. -/
theorem firstExitPrefixEvent_preimage_of_prefix_local_read
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (read : (Nat × Nat → Bool) → Nat × Nat → Bool)
    (hlocal : ∀ r coins,
      coinPrefix r (read (coinPrefix r coins)) =
        coinPrefix r (read coins)) (r : Nat) :
    (coinPrefix r) ⁻¹'
        (read ⁻¹' firstExitPrefixEvent s pending threshold r) =
      read ⁻¹' firstExitPrefixEvent s pending threshold r := by
  ext coins
  change read (coinPrefix r coins) ∈
      firstExitPrefixEvent s pending threshold r ↔
    read coins ∈ firstExitPrefixEvent s pending threshold r
  have hp := firstExitPrefixEvent_preimage s pending threshold r
  have hleft : read (coinPrefix r coins) ∈
      firstExitPrefixEvent s pending threshold r ↔
      coinPrefix r (read (coinPrefix r coins)) ∈
        firstExitPrefixEvent s pending threshold r := by
    exact (Set.ext_iff.mp hp _).symm
  have hright : read coins ∈
      firstExitPrefixEvent s pending threshold r ↔
      coinPrefix r (read coins) ∈
        firstExitPrefixEvent s pending threshold r := by
    exact (Set.ext_iff.mp hp _).symm
  rw [hleft, hlocal r coins, ← hright]

/-- A fair, time-local read of a larger fair source inherits the first-exit
stopped-prefix independence law. The read may relabel or filter coordinates
provided its output is fair and preserves each round's prefix. -/
theorem fairCoinStreamLaw_firstExit_localRead_stoppedPrefix_shift_law
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (read : (Nat × Nat → Bool) → Nat × Nat → Bool)
    (hread : Measurable read)
    (hfair : fairCoinStreamLaw.map read = fairCoinStreamLaw)
    (hlocal : ∀ r coins,
      coinPrefix r (read (coinPrefix r coins)) =
        coinPrefix r (read coins)) :
    let stop := fun coins => firstExitRound s pending threshold (read coins)
    fairCoinStreamLaw.map
      (fun coins =>
        (coinPrefix (stop coins) coins, shiftCoins (stop coins) coins)) =
    (fairCoinStreamLaw.map
      (fun coins => coinPrefix (stop coins) coins)).prod
      fairCoinStreamLaw := by
  let stop := fun coins => firstExitRound s pending threshold (read coins)
  let event := fun r => read ⁻¹' firstExitPrefixEvent s pending threshold r
  have hstop : Measurable stop :=
    (measurable_firstExitRound s pending threshold).comp hread
  have hevent (r : Nat) : MeasurableSet (event r) :=
    (measurableSet_firstExitPrefixEvent s pending threshold r).preimage
      hread
  have hprefix (r : Nat) :
      (coinPrefix r) ⁻¹' event r = event r :=
    firstExitPrefixEvent_preimage_of_prefix_local_read s pending
      threshold read hlocal r
  have hae (r : Nat) : ∀ᵐ coins ∂fairCoinStreamLaw,
      (stop coins = r ↔ coins ∈ event r) := by
    have hbase := firstExitRound_eq_prefix_event_ae s pending threshold
      hthreshold r
    rw [← hfair] at hbase
    exact ae_of_ae_map hread.aemeasurable hbase
  exact fairCoinStreamLaw_generic_stoppedPrefix_shift_law
    stop hstop event hevent hprefix hae

end Kr25Ssmxt
