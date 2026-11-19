import ttc.Analysis.StatePointCounts

/-! A deterministic splice of the independent coin blocks used by successive
paper thinning loops. This identifies consecutive rounds with one
absolute dyadic-level coin stream. -/

namespace ttc

def spliceCoins (first second : Nat × Nat → Bool) (firstRounds : Nat) :
    Nat × Nat → Bool :=
  fun pair => if pair.1 < firstRounds then first pair
    else second (pair.1 - firstRounds, pair.2)

theorem survives_spliceCoins (first second : Nat × Nat → Bool)
    (firstRounds secondRounds label : Nat) :
    survives (spliceCoins first second firstRounds)
      (firstRounds + secondRounds) label ↔
      survives first firstRounds label ∧
        survives second secondRounds label := by
  constructor
  · intro h
    constructor
    · intro r hr
      have hcoin := h r (by omega)
      simpa [spliceCoins, hr] using hcoin
    · intro r hr
      have hcoin := h (firstRounds + r) (by omega)
      simpa [spliceCoins] using hcoin
  · rintro ⟨hfirst, hsecond⟩ r hr
    by_cases hbefore : r < firstRounds
    · simpa [spliceCoins, hbefore] using hfirst r hbefore
    · have hafter : r - firstRounds < secondRounds := by omega
      simpa [spliceCoins, hbefore] using hsecond (r - firstRounds) hafter

/-- Thinning a stored population in two successive coin blocks is precisely
thinning it once at the sum of the rounds with the spliced stream. -/
theorem samplesAfter_spliceCoins {n : Nat}
    (first second : Nat × Nat → Bool)
    (firstRounds secondRounds : Nat)
    (samples : Finset (SampleCopy n)) :
    samplesAfter second secondRounds
      (samplesAfter first firstRounds samples) =
    samplesAfter (spliceCoins first second firstRounds)
      (firstRounds + secondRounds) samples := by
  classical
  ext copy
  simp only [samplesAfter, Finset.mem_filter]
  rw [survives_spliceCoins]
  tauto

/-- The two while-loops of one component consume consecutive absolute
dyadic-level coin blocks on all stored copies. -/
theorem two_loops_samples_splice {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (pending : Nat) (first second : Nat × Nat → Bool) :
    (ttcPseudocode.secondLoopResult
      (ttcReference.firstLoopResult s intensity threshold first)
      pending threshold second).1.X =
    samplesAfter (spliceCoins first second
      (ttcReference.firstLoopExit s intensity threshold))
      (ttcReference.firstLoopExit s intensity threshold +
        ttcPseudocode.secondLoopExitRound
          (ttcReference.firstLoopResult s intensity threshold first)
          pending threshold second) s.X := by
  exact samplesAfter_spliceCoins first second
    (ttcReference.firstLoopExit s intensity threshold)
    (ttcPseudocode.secondLoopExitRound
      (ttcReference.firstLoopResult s intensity threshold first)
      pending threshold second) s.X

theorem two_loops_rate_add {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (pending : Nat) (first second : Nat × Nat → Bool) :
    (ttcPseudocode.secondLoopResult
      (ttcReference.firstLoopResult s intensity threshold first)
      pending threshold second).1.p =
    s.p / (2 : NNReal) ^
      (ttcReference.firstLoopExit s intensity threshold +
        ttcPseudocode.secondLoopExitRound
          (ttcReference.firstLoopResult s intensity threshold first)
          pending threshold second) := by
  change (ttcReference.firstLoopResult s intensity threshold first).p /
      (2 : NNReal) ^ ttcPseudocode.secondLoopExitRound
        (ttcReference.firstLoopResult s intensity threshold first)
        pending threshold second = _
  rw [pow_add, ← div_div]
  rfl

/-- For one component, the actual stored point count after both thinning
loops and batch append is the count obtained by one cumulative coin block,
plus the appended point count. -/
theorem two_loops_addBatch_pointCount {n : Nat}
    (s : TTCState n) (P : PolytopeData n)
    (intensity : NNReal) (threshold : Real) (pending : Nat)
    (first second : Nat × Nat → Bool)
    {count : Nat} (batch : Fin count → LatticePoint n)
    (x : LatticePoint n) (hfresh : s.LabelsFresh) :
    let deleted := s.removeComponent P
    let firstState := ttcReference.firstLoopResult deleted intensity threshold first
    let secondState := (ttcPseudocode.secondLoopResult firstState pending threshold second).1
    (secondState.addBatch batch).pointCount x =
      ((samplesAfter (spliceCoins first second
        (ttcReference.firstLoopExit deleted intensity threshold))
        (ttcReference.firstLoopExit deleted intensity threshold +
          ttcPseudocode.secondLoopExitRound firstState pending threshold second)
        deleted.X).filter (fun copy => copy.2 = x)).card +
        Arlib.Probability.colourCount batch x := by
  classical
  dsimp only
  let deleted := s.removeComponent P
  let firstState := ttcReference.firstLoopResult deleted intensity threshold first
  let secondState := (ttcPseudocode.secondLoopResult firstState pending threshold second).1
  have hdeleted : deleted.LabelsFresh :=
    s.labelsFresh_removeComponent P hfresh
  have hfirst : firstState.LabelsFresh :=
    rateThinningResult_labelsFresh deleted intensity threshold
      first hdeleted
  have hsecond : secondState.LabelsFresh :=
    thinningResult_labelsFresh firstState pending threshold second hfirst
  rw [TTCState.pointCount_addBatch secondState batch x hsecond]
  have hsamples := two_loops_samples_splice deleted intensity
    threshold pending first second
  change (secondState.X.filter (fun copy => copy.2 = x)).card +
    Arlib.Probability.colourCount batch x = _
  rw [hsamples]

end ttc
