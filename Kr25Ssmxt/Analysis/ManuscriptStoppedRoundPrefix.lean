import Kr25Ssmxt.Analysis.ManuscriptGenericStoppedPrefix

/-! Strong Markov independence with both the stopping round and its
observed prefix retained. -/

namespace Kr25Ssmxt

open MeasureTheory Function

theorem fairCoinStreamLaw_generic_stoppedRoundPrefix_shift_law
    (stop : (Nat × Nat → Bool) → Nat)
    (hstop : Measurable stop)
    (event : Nat → Set (Nat × Nat → Bool))
    (hevent : ∀ r, MeasurableSet (event r))
    (hprefix : ∀ r, (coinPrefix r) ⁻¹' (event r) = event r)
    (hae : ∀ r, ∀ᵐ coins ∂fairCoinStreamLaw,
      (stop coins = r ↔ coins ∈ event r)) :
    fairCoinStreamLaw.map
      (fun coins =>
        ((stop coins, coinPrefix (stop coins) coins),
          shiftCoins (stop coins) coins)) =
    (fairCoinStreamLaw.map
      (fun coins => (stop coins, coinPrefix (stop coins) coins))).prod
      fairCoinStreamLaw := by
  classical
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let observed : (Nat × Nat → Bool) →
      Nat × (Nat × Nat → Bool) :=
    fun coins => (stop coins, coinPrefix (stop coins) coins)
  let output : (Nat × Nat → Bool) →
      (Nat × (Nat × Nat → Bool)) × (Nat × Nat → Bool) :=
    fun coins => (observed coins, shiftCoins (stop coins) coins)
  have hprefixJoint : Measurable
      (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_coinPrefix rounds
  have hobserved : Measurable observed :=
    hstop.prodMk (hprefixJoint.comp (hstop.prodMk measurable_id))
  have houtput : Measurable output :=
    hobserved.prodMk ((measurable_stoppedCoinPair stop hstop).snd)
  letI : IsProbabilityMeasure (fairCoinStreamLaw.map output) :=
    Measure.isProbabilityMeasure_map houtput.aemeasurable
  apply Measure.ext_prod
  intro A B hA hB
  let slice (r : Nat) : Set (Nat × Nat → Bool) :=
    {pre | (r, pre) ∈ A}
  let fiber (r : Nat) : Set (Nat × Nat → Bool) :=
    {coins | stop coins = r}
  let F (r : Nat) : Set (Nat × Nat → Bool) :=
    fiber r ∩ (coinPrefix r) ⁻¹' slice r
  let E (r : Nat) : Set (Nat × Nat → Bool) :=
    F r ∩ (shiftCoins r) ⁻¹' B
  have hsection (r : Nat) : MeasurableSet (slice r) :=
    hA.preimage (measurable_const.prodMk measurable_id)
  have hfiber (r : Nat) : MeasurableSet (fiber r) :=
    (measurableSet_singleton r).preimage hstop
  have hF (r : Nat) : MeasurableSet (F r) :=
    (hfiber r).inter ((hsection r).preimage (measurable_coinPrefix r))
  have hE (r : Nat) : MeasurableSet (E r) :=
    (hF r).inter (hB.preimage
      (measurable_pi_lambda _ (fun index =>
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
    simp only [Set.mem_iUnion, Set.mem_preimage, F, fiber, slice,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, hr, hApre⟩
      simpa [observed, hr] using hApre
    · intro hApre
      exact ⟨stop coins, rfl, hApre⟩
  have hE_union : (⋃ r, E r) = output ⁻¹' (A ×ˢ B) := by
    ext coins
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_prod,
      E, F, fiber, slice, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, ⟨hr, ha⟩, hb⟩
      simpa [output, observed, hr] using
        (show (r, coinPrefix r coins) ∈ A ∧ shiftCoins r coins ∈ B
          from ⟨ha, hb⟩)
    · rintro ⟨ha, hb⟩
      exact ⟨stop coins, ⟨rfl, ha⟩, hb⟩
  have hterm (r : Nat) :
      fairCoinStreamLaw (E r) =
        fairCoinStreamLaw (F r) * fairCoinStreamLaw B := by
    let G : Set (Nat × Nat → Bool) :=
      event r ∩ (coinPrefix r) ⁻¹' slice r
    have hG : MeasurableSet G :=
      (hevent r).inter ((hsection r).preimage (measurable_coinPrefix r))
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

theorem fairCoinStreamLaw_firstExit_localRead_stoppedRoundPrefix_shift_law
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
        ((stop coins, coinPrefix (stop coins) coins),
          shiftCoins (stop coins) coins)) =
    (fairCoinStreamLaw.map
      (fun coins => (stop coins, coinPrefix (stop coins) coins))).prod
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
  exact fairCoinStreamLaw_generic_stoppedRoundPrefix_shift_law
    stop hstop event hevent hprefix hae

/-- At a fixed first-exit round, the second-loop result reads only the
coins in its stopped prefix. -/
theorem thinningResult_congr_of_stoppedRoundPrefix
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (coins coins' : Nat × Nat → Bool)
    (hround : firstExitRound s pending threshold coins =
      firstExitRound s pending threshold coins')
    (hprefix : coinPrefix (firstExitRound s pending threshold coins)
        coins =
      coinPrefix (firstExitRound s pending threshold coins) coins') :
    thinningResult s pending threshold coins =
      thinningResult s pending threshold coins' := by
  let r := firstExitRound s pending threshold coins
  have hsamples : samplesAfter coins r s.samples =
      samplesAfter coins' r s.samples := by
    calc
      samplesAfter coins r s.samples =
        samplesAfter (coinPrefix r coins) r s.samples :=
          (samplesAfter_coinPrefix s r r (le_refl r) coins).symm
      _ = samplesAfter (coinPrefix r coins') r s.samples := by rw [hprefix]
      _ = samplesAfter coins' r s.samples :=
        samplesAfter_coinPrefix s r r (le_refl r) coins'
  have hpending : pendingAfter coins r s.nextLabel pending =
      pendingAfter coins' r s.nextLabel pending := by
    calc
      pendingAfter coins r s.nextLabel pending =
        pendingAfter (coinPrefix r coins) r s.nextLabel pending :=
          (pendingAfter_coinPrefix r r s.nextLabel pending
            (le_refl r) coins).symm
      _ = pendingAfter (coinPrefix r coins') r s.nextLabel pending := by
        rw [hprefix]
      _ = pendingAfter coins' r s.nextLabel pending :=
        pendingAfter_coinPrefix r r s.nextLabel pending
          (le_refl r) coins'
  simp only [thinningResult]
  rw [← hround, hsamples, hpending]

/-- Reconstruct the thinning output from a stopped round and a prefix of
the underlying source, after a time-local read of that source. -/
noncomputable def thinningResultAtObserved {n : Nat} (s : TTCState n) (pending : Nat)
    (read : (Nat × Nat → Bool) → Nat × Nat → Bool)
    (observation : Nat × (Nat × Nat → Bool)) : TTCState n × Nat :=
  ({ rate := s.rate / (2 : NNReal) ^ observation.1
     samples := samplesAfter (read observation.2) observation.1 s.samples
     nextLabel := s.nextLabel },
   pendingAfter (read observation.2) observation.1 s.nextLabel pending)

theorem measurable_thinningResultAtObserved
    {n : Nat} (s : TTCState n) (pending : Nat)
    (read : (Nat × Nat → Bool) → Nat × Nat → Bool)
    (hread : Measurable read) :
    Measurable (thinningResultAtObserved s pending read) := by
  apply measurable_from_prod_countable_right
  intro rounds
  have hsamples : Measurable (fun coins : Nat × Nat → Bool =>
      samplesAfter (read coins) rounds s.samples) :=
    (measurable_samplesAfter_fixed rounds s.samples).comp hread
  have hpending : Measurable (fun coins : Nat × Nat → Bool =>
      pendingAfter (read coins) rounds s.nextLabel pending) :=
    (measurable_pendingAfter_fixed rounds s.nextLabel pending).comp hread
  have hstate : Measurable (fun coins : Nat × Nat → Bool =>
      { rate := s.rate / (2 : NNReal) ^ rounds
        samples := samplesAfter (read coins) rounds s.samples
        nextLabel := s.nextLabel : TTCState n }) := by
    rw [measurable_comap_iff]
    exact measurable_const.prodMk (hsamples.prodMk measurable_const)
  exact hstate.prodMk hpending

theorem thinningResult_eq_atObserved
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (read : (Nat × Nat → Bool) → Nat × Nat → Bool)
    (hlocal : ∀ r coins,
      coinPrefix r (read (coinPrefix r coins)) =
        coinPrefix r (read coins))
    (coins : Nat × Nat → Bool) :
    let r := firstExitRound s pending threshold (read coins)
    thinningResult s pending threshold (read coins) =
      thinningResultAtObserved s pending read
        (r, coinPrefix r coins) := by
  let r := firstExitRound s pending threshold (read coins)
  have hprefix := hlocal r coins
  have hsamples : samplesAfter (read coins) r s.samples =
      samplesAfter (read (coinPrefix r coins)) r s.samples := by
    calc
      samplesAfter (read coins) r s.samples =
        samplesAfter (coinPrefix r (read coins)) r s.samples :=
          (samplesAfter_coinPrefix s r r (le_refl r) (read coins)).symm
      _ = samplesAfter (coinPrefix r
          (read (coinPrefix r coins))) r s.samples := by rw [hprefix]
      _ = samplesAfter (read (coinPrefix r coins)) r s.samples :=
        samplesAfter_coinPrefix s r r (le_refl r)
          (read (coinPrefix r coins))
  have hpending : pendingAfter (read coins) r s.nextLabel pending =
      pendingAfter (read (coinPrefix r coins)) r s.nextLabel pending := by
    calc
      pendingAfter (read coins) r s.nextLabel pending =
        pendingAfter (coinPrefix r (read coins)) r s.nextLabel pending :=
          (pendingAfter_coinPrefix r r s.nextLabel pending
            (le_refl r) (read coins)).symm
      _ = pendingAfter (coinPrefix r
          (read (coinPrefix r coins))) r s.nextLabel pending := by
          rw [hprefix]
      _ = pendingAfter (read (coinPrefix r coins)) r s.nextLabel pending :=
        pendingAfter_coinPrefix r r s.nextLabel pending
          (le_refl r) (read (coinPrefix r coins))
  simp only [thinningResult, thinningResultAtObserved]
  rw [hsamples, hpending]

end Kr25Ssmxt
