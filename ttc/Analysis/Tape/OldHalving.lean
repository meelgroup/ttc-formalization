/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.CV18Sim
import ttc.Analysis.CoinSpliceLaw
import ttc.Analysis.IIDIndexedSelection
import ttc.Analysis.LabelFreshness
import ttc.Analysis.BernoulliCount
import ttc.Analysis.CoinRelabelLaw

/-!
# The old halving loop, one round at a time

The old model's second loop (`ttcPseudocode.secondLoop`) reads one fair coin stream indexed
by round and copy label, and exits at the first round where the surviving stored and pending
copies are at most `Thresh`.  This file shows that, stopped after at most `f` rounds
(`oldTrunc`), it is the same process as the sealed program's halving loop: if the population
is at most `Thresh` it stops; otherwise each stored copy is kept by a fair coin, the pending
count becomes `Binomial(N, 1/2)`, and the loop goes on with fresh coins.

The round is split off the stream (`spliceCoins … 1`): what follows round `0` is a loop on
the survivors, reading the shifted stream with the surviving pending copies relabelled to
contiguous labels (`relab`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace ttc.Tape

open ttc (TTCState samplesAfter pendingAfter survives fairCoinStreamLaw fairCoinLaw
  spliceCoins pendingSurvivorIndices ttcPseudocode)

variable {n : ℕ}

/-! ## Rounds of the stream -/

theorem survives_splice_succ (A B : ℕ × ℕ → Bool) (r ℓ : ℕ) :
    survives (spliceCoins A B 1) (r + 1) ℓ ↔ A (0, ℓ) = true ∧ survives B r ℓ := by
  constructor
  · intro h
    refine ⟨by simpa [spliceCoins] using h 0 (Nat.succ_pos r), fun r' hr' => ?_⟩
    simpa [spliceCoins] using h (r' + 1) (by omega)
  · rintro ⟨h0, h⟩ r' hr'
    rcases r' with _ | r'
    · simpa [spliceCoins] using h0
    · simpa [spliceCoins] using h r' (by omega)

theorem survives_one (A : ℕ × ℕ → Bool) (ℓ : ℕ) : survives A 1 ℓ ↔ A (0, ℓ) = true := by
  constructor
  · intro h; exact h 0 Nat.one_pos
  · intro h r' hr'; rwa [show r' = 0 by omega]

theorem survives_splice_one (A B : ℕ × ℕ → Bool) (ℓ : ℕ) :
    survives (spliceCoins A B 1) 1 ℓ ↔ survives A 1 ℓ := by
  rw [survives_one, survives_one]
  simp [spliceCoins]

theorem survives_zero (c : ℕ × ℕ → Bool) (ℓ : ℕ) : survives c 0 ℓ :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem samplesAfter_zero (c : ℕ × ℕ → Bool) (X : Finset (ttc.SampleCopy n)) :
    samplesAfter c 0 X = X := by
  classical
  ext copy
  simp [samplesAfter, survives_zero]

theorem pendingAfter_zero (c : ℕ × ℕ → Bool) (nl N : ℕ) : pendingAfter c 0 nl N = N := by
  classical
  simp [pendingAfter, survives_zero]

/-! ## Relabelling the surviving pending copies -/

section Relabel

variable (A : ℕ × ℕ → Bool) (nl N : ℕ)

/-- The pending copies surviving round `0`, by their index. -/
abbrev survS : Finset ℕ := pendingSurvivorIndices A 1 nl N

/-- Their number. -/
abbrev survN : ℕ := (survS A nl N).card

/-- The `j`-th surviving pending index, in order. -/
def survIdx (j : ℕ) : ℕ :=
  if h : j < survN A nl N then ((survS A nl N).orderIsoOfFin rfl ⟨j, h⟩ : ℕ) else 0

/-- **The relabelling**: stored labels stay, the `j`-th surviving pending copy takes the
label `nl + j`, every other label moves out of the way. -/
def relab (ℓ : ℕ) : ℕ :=
  if ℓ < nl then ℓ else if ℓ - nl < survN A nl N then nl + survIdx A nl N (ℓ - nl) else ℓ + N

theorem survIdx_mem {j : ℕ} (hj : j < survN A nl N) : survIdx A nl N j ∈ survS A nl N := by
  simp only [survIdx, hj, dite_true]
  exact ((survS A nl N).orderIsoOfFin rfl ⟨j, hj⟩).2

theorem survIdx_lt {j : ℕ} (hj : j < survN A nl N) : survIdx A nl N j < N := by
  have h := survIdx_mem A nl N hj
  simp only [pendingSurvivorIndices, Finset.mem_filter, Finset.mem_range] at h
  exact h.1

theorem survIdx_injOn {i j : ℕ} (hi : i < survN A nl N) (hj : j < survN A nl N)
    (h : survIdx A nl N i = survIdx A nl N j) : i = j := by
  simp only [survIdx, hi, hj, dite_true] at h
  have := ((survS A nl N).orderIsoOfFin rfl).injective (Subtype.ext h)
  exact congrArg Fin.val this

theorem relab_injective : Function.Injective (relab A nl N) := by
  intro a b h
  unfold relab at h
  by_cases ha : a < nl <;> by_cases hb : b < nl
  · simpa [ha, hb] using h
  · by_cases hb' : b - nl < survN A nl N
    · simp only [ha, hb, hb', ite_true, ite_false] at h
      omega
    · simp only [ha, hb, hb', ite_true, ite_false] at h
      omega
  · by_cases ha' : a - nl < survN A nl N
    · simp only [ha, hb, ha', ite_true, ite_false] at h
      omega
    · simp only [ha, hb, ha', ite_true, ite_false] at h
      omega
  · by_cases ha' : a - nl < survN A nl N <;> by_cases hb' : b - nl < survN A nl N
    · simp only [ha, hb, ha', hb', ite_true, ite_false] at h
      have := survIdx_injOn A nl N ha' hb' (by omega)
      omega
    · simp only [ha, hb, ha', hb', ite_true, ite_false] at h
      have := survIdx_lt A nl N ha'
      omega
    · simp only [ha, hb, ha', hb', ite_true, ite_false] at h
      have := survIdx_lt A nl N hb'
      omega
    · simp only [ha, hb, ha', hb', ite_true, ite_false] at h
      omega

/-- The shifted stream, relabelled. -/
def relabCoins (B : ℕ × ℕ → Bool) : ℕ × ℕ → Bool := fun p => B (p.1, relab A nl N p.2)

theorem survives_relabCoins (B : ℕ × ℕ → Bool) (r ℓ : ℕ) :
    survives (relabCoins A nl N B) r ℓ ↔ survives B r (relab A nl N ℓ) := Iff.rfl

theorem relab_lt {ℓ : ℕ} (h : ℓ < nl) : relab A nl N ℓ = ℓ := by simp [relab, h]

theorem relab_pending {j : ℕ} (hj : j < survN A nl N) :
    relab A nl N (nl + j) = nl + survIdx A nl N j := by
  simp [relab, hj]

/-- **The surviving pending copies, after round `0`, are the relabelled pending copies.** -/
theorem pendingAfter_splice_succ (B : ℕ × ℕ → Bool) (r : ℕ) :
    pendingAfter (spliceCoins A B 1) (r + 1) nl N =
      pendingAfter (relabCoins A nl N B) r nl (survN A nl N) := by
  classical
  simp only [pendingAfter, survives_splice_succ, survives_relabCoins]
  symm
  refine Finset.card_bij (fun j _ => survIdx A nl N j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    have hmem := survIdx_mem A nl N hj.1
    simp only [pendingSurvivorIndices, Finset.mem_filter, Finset.mem_range, survives_one] at hmem
    refine ⟨hmem.1, hmem.2, ?_⟩
    rw [relab_pending A nl N hj.1] at hj
    exact hj.2
  · intro i hi j hj h
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    exact survIdx_injOn A nl N hi.1 hj.1 h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hS : i ∈ survS A nl N := by
      simp only [pendingSurvivorIndices, Finset.mem_filter, Finset.mem_range, survives_one]
      exact ⟨hi.1, hi.2.1⟩
    let k := ((survS A nl N).orderIsoOfFin rfl).symm ⟨i, hS⟩
    have hk : survIdx A nl N k.val = i := by
      simp only [survIdx, k.isLt, dite_true, Fin.eta]
      show (((survS A nl N).orderIsoOfFin rfl) (((survS A nl N).orderIsoOfFin rfl).symm ⟨i, hS⟩) : ℕ) = i
      rw [OrderIso.apply_symm_apply]
    refine ⟨k.val, ?_, hk⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨k.isLt, ?_⟩
    rw [relab_pending A nl N k.isLt, hk]
    exact hi.2.2

end Relabel


/-! ## Stored copies -/

/-- The stored copies' labels are all below `nl`. -/
def StoredBelow (X : Finset (ttc.SampleCopy n)) (nl : ℕ) : Prop := ∀ c ∈ X, c.1 < nl

theorem samplesAfter_splice_succ (A B : ℕ × ℕ → Bool) (nl N : ℕ) (X : Finset (ttc.SampleCopy n))
    (hX : StoredBelow X nl) (r : ℕ) :
    samplesAfter (spliceCoins A B 1) (r + 1) X =
      samplesAfter (relabCoins A nl N B) r (samplesAfter A 1 X) := by
  classical
  ext copy
  simp only [samplesAfter, Finset.mem_filter, survives_splice_succ, survives_relabCoins,
    survives_one]
  constructor
  · rintro ⟨hc, h0, hr⟩
    exact ⟨⟨hc, h0⟩, by rwa [relab_lt A nl N (hX copy hc)]⟩
  · rintro ⟨⟨hc, h0⟩, hr⟩
    exact ⟨hc, h0, by rwa [relab_lt A nl N (hX copy hc)] at hr⟩

/-! ## The loop, stopped after at most `f` rounds -/

open Classical in
/-- **The old second loop, given at most `f` rounds**: its result if it exits within them,
`none` otherwise. -/
def oldTrunc (Th : ℝ) (f : ℕ) (s : TTCState n) (N : ℕ) (c : ℕ × ℕ → Bool) :
    Option (TTCState n × ℕ) :=
  if ∃ r < f, ttcPseudocode.secondLoopExit s N Th c r then
    some (ttcPseudocode.secondLoopResult s N Th c)
  else none

/-- The state after round `0`: the stored copies that survived it, and `p / 2`. -/
def afterRound (A : ℕ × ℕ → Bool) (s : TTCState n) : TTCState n :=
  ⟨s.p / 2, samplesAfter A 1 s.X, s.nextLabel⟩

theorem exit_zero (s : TTCState n) (N : ℕ) (Th : ℝ) (c : ℕ × ℕ → Bool) :
    ttcPseudocode.secondLoopExit s N Th c 0 ↔ ((s.X.card + N : ℕ) : ℝ) ≤ Th := by
  simp only [ttcPseudocode.secondLoopExit, samplesAfter_zero, pendingAfter_zero, Nat.cast_add]

theorem exit_splice_succ (s : TTCState n) (N : ℕ) (Th : ℝ) (A B : ℕ × ℕ → Bool)
    (hX : StoredBelow s.X s.nextLabel) (r : ℕ) :
    ttcPseudocode.secondLoopExit s N Th (spliceCoins A B 1) (r + 1) ↔
      ttcPseudocode.secondLoopExit (afterRound A s) (survN A s.nextLabel N) Th
        (relabCoins A s.nextLabel N B) r := by
  simp only [ttcPseudocode.secondLoopExit, afterRound,
    samplesAfter_splice_succ A B s.nextLabel N s.X hX, pendingAfter_splice_succ]

/-- **One round of the old loop, pointwise**: either it exits before any round, or it is the
loop on the survivors, reading the shifted stream relabelled. -/
theorem oldTrunc_splice_succ (Th : ℝ) (f : ℕ) (s : TTCState n) (N : ℕ) (A B : ℕ × ℕ → Bool)
    (hX : StoredBelow s.X s.nextLabel) :
    oldTrunc Th (f + 1) s N (spliceCoins A B 1) =
      if ((s.X.card + N : ℕ) : ℝ) ≤ Th then some (s, N)
      else oldTrunc Th f (afterRound A s) (survN A s.nextLabel N)
        (relabCoins A s.nextLabel N B) := by
  classical
  set c := spliceCoins A B 1
  set c' := relabCoins A s.nextLabel N B
  have hP : ∀ r, ttcPseudocode.secondLoopExit s N Th c (r + 1) ↔
      ttcPseudocode.secondLoopExit (afterRound A s) (survN A s.nextLabel N) Th c' r :=
    exit_splice_succ s N Th A B hX
  split_ifs with h0
  · have hz : ttcPseudocode.secondLoopExit s N Th c 0 := (exit_zero s N Th c).2 h0
    have hR : ttcPseudocode.secondLoopExitRound s N Th c = 0 :=
      Nat.sInf_eq_zero.mpr (Or.inl hz)
    simp only [oldTrunc]
    rw [if_pos ⟨0, Nat.succ_pos f, hz⟩]
    simp only [ttcPseudocode.secondLoopResult, hR, pow_zero, div_one, samplesAfter_zero,
      pendingAfter_zero]
  · have hz : ¬ ttcPseudocode.secondLoopExit s N Th c 0 := fun h => h0 ((exit_zero s N Th c).1 h)
    have hex : (∃ r < f + 1, ttcPseudocode.secondLoopExit s N Th c r) ↔
        ∃ r < f, ttcPseudocode.secondLoopExit (afterRound A s) (survN A s.nextLabel N) Th c' r := by
      constructor
      · rintro ⟨r, hr, h⟩
        rcases r with _ | r
        · exact absurd h hz
        · exact ⟨r, by omega, (hP r).1 h⟩
      · rintro ⟨r, hr, h⟩
        exact ⟨r + 1, by omega, (hP r).2 h⟩
    simp only [oldTrunc]
    by_cases hq : ∃ r < f, ttcPseudocode.secondLoopExit (afterRound A s) (survN A s.nextLabel N) Th c' r
    · rw [if_pos (hex.2 hq), if_pos hq]
      have hne : ({r | ttcPseudocode.secondLoopExit s N Th c r} : Set ℕ).Nonempty := by
        obtain ⟨r, _, h⟩ := hex.2 hq
        exact ⟨r, h⟩
      have hpos : 1 ≤ ttcPseudocode.secondLoopExitRound s N Th c := by
        by_contra hlt
        have h0' : ttcPseudocode.secondLoopExitRound s N Th c = 0 := by omega
        rcases Nat.sInf_eq_zero.mp h0' with h | h
        · exact hz h
        · exact hne.ne_empty h
      have hR : ttcPseudocode.secondLoopExitRound s N Th c =
          ttcPseudocode.secondLoopExitRound (afterRound A s) (survN A s.nextLabel N) Th c' + 1 := by
        unfold ttcPseudocode.secondLoopExitRound
        rw [← Nat.sInf_add hpos]
        congr 2
        ext r
        exact hP r
      simp only [ttcPseudocode.secondLoopResult, hR, c, c']
      rw [samplesAfter_splice_succ A B s.nextLabel N s.X hX, pendingAfter_splice_succ]
      simp only [afterRound, pow_succ, div_div, mul_comm]
    · rw [if_neg (fun h => hq (hex.1 h)), if_neg hq]


/-! ## The law of one round -/

section Law

variable (Th : ℝ)

theorem measurable_oldTrunc (f : ℕ) (s : TTCState n) (N : ℕ) :
    Measurable (oldTrunc Th f s N) := by
  classical
  have hset : MeasurableSet {c : ℕ × ℕ → Bool | ∃ r < f, ttcPseudocode.secondLoopExit s N Th c r} := by
    have : {c : ℕ × ℕ → Bool | ∃ r < f, ttcPseudocode.secondLoopExit s N Th c r} =
        ⋃ r ∈ Finset.range f, {c | ttcPseudocode.secondLoopExit s N Th c r} := by
      ext c; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun r _ => ttc.measurableSet_thinningExit s N Th r
  exact Measurable.ite hset (ArlibCommunity.Algorithms.CV18.measurable_some.comp
    (ttc.measurable_thinningResult s N Th)) measurable_const

/-- **The old loop given at most `f` rounds**, as a law. -/
def oldLaw (f : ℕ) (s : TTCState n) (N : ℕ) : Measure (Option (TTCState n × ℕ)) :=
  fairCoinStreamLaw.map (oldTrunc Th f s N)

theorem oldLaw_zero (s : TTCState n) (N : ℕ) : oldLaw Th 0 s N = Measure.dirac none := by
  letI := ttc.fairCoinStreamLaw_isProbabilityMeasure
  have : oldTrunc Th 0 s N = fun _ => none := by
    funext c; simp [oldTrunc]
  rw [oldLaw, this, Measure.map_const, measure_univ, one_smul]

theorem relabCoins_law (A : ℕ × ℕ → Bool) (nl N : ℕ) :
    fairCoinStreamLaw.map (relabCoins A nl N) = fairCoinStreamLaw :=
  ttc.fairCoinStreamLaw_reindex_labels (relab A nl N) (relab_injective A nl N)

theorem measurable_relabCoins (A : ℕ × ℕ → Bool) (nl N : ℕ) :
    Measurable (relabCoins A nl N) :=
  measurable_pi_iff.mpr fun p => measurable_pi_apply (p.1, relab A nl N p.2)

theorem measurable_samplesAfter_one (X : Finset (ttc.SampleCopy n)) :
    Measurable fun A : ℕ × ℕ → Bool => samplesAfter A 1 X := by
  classical
  rw [measurable_finset_iff]
  intro copy
  apply measurable_to_prop
  by_cases hc : copy ∈ X
  · have : (fun A : ℕ × ℕ → Bool => copy ∈ samplesAfter A 1 X) ⁻¹' {True} =
        {A | survives A 1 copy.1} := by
      ext A; simp [samplesAfter, hc]
    rw [this]
    exact ttc.measurableSet_survives 1 copy.1
  · have : (fun A : ℕ × ℕ → Bool => copy ∈ samplesAfter A 1 X) ⁻¹' {True} = ∅ := by
      ext A; simp [samplesAfter, hc]
    rw [this]
    exact MeasurableSet.empty

theorem measurable_survN (nl N : ℕ) : Measurable fun A : ℕ × ℕ → Bool => survN A nl N := by
  have := ttc.measurable_pendingSurvivorIndices_fixed 1 nl N
  exact (measurable_of_countable (fun T : Finset ℕ => T.card)).comp this

/-- What follows round `0`, as a function of the copies it left. -/
def oldCont (f : ℕ) (s : TTCState n) (q : Finset (ttc.SampleCopy n) × ℕ) :
    Measure (Option (TTCState n × ℕ)) :=
  oldLaw Th f ⟨s.p / 2, q.1, s.nextLabel⟩ q.2

/-- **One round of the old loop, as a law**: either it exits before any round, or it is
the loop on what round `0` left, with fresh coins. -/
theorem oldLaw_succ (f : ℕ) (s : TTCState n) (N : ℕ) (hX : StoredBelow s.X s.nextLabel) :
    oldLaw Th (f + 1) s N =
      if ((s.X.card + N : ℕ) : ℝ) ≤ Th then Measure.dirac (some (s, N))
      else (fairCoinStreamLaw.map fun A => (samplesAfter A 1 s.X, survN A s.nextLabel N)).bind
        (oldCont Th f s) := by
  classical
  have := ttc.fairCoinStreamLaw_isProbabilityMeasure
  have hsplice := ttc.fairCoinStreamLaw_splice 1
  have hF : Measurable fun AB : (ℕ × ℕ → Bool) × (ℕ × ℕ → Bool) =>
      oldTrunc Th (f + 1) s N (spliceCoins AB.1 AB.2 1) :=
    (measurable_oldTrunc Th (f + 1) s N).comp (ttc.measurable_spliceCoins_pair 1)
  have hL : oldLaw Th (f + 1) s N = (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun AB => oldTrunc Th (f + 1) s N (spliceCoins AB.1 AB.2 1)) := by
    conv_lhs => rw [oldLaw, ← hsplice]
    rw [Measure.map_map (measurable_oldTrunc Th (f + 1) s N) (ttc.measurable_spliceCoins_pair 1)]
    rfl
  rw [hL]
  simp_rw [oldTrunc_splice_succ Th f s N _ _ hX]
  split_ifs with h0
  · rw [Measure.map_const, measure_univ, one_smul]
  · have hφ : Measurable fun A : ℕ × ℕ → Bool => (samplesAfter A 1 s.X, survN A s.nextLabel N) :=
      (measurable_samplesAfter_one s.X).prodMk (measurable_survN s.nextLabel N)
    have hK : Measurable (oldCont Th f s) := measurable_of_countable _
    ext S hS
    rw [Measure.bind_apply hS hK.aemeasurable,
      lintegral_map (f := fun q => oldCont Th f s q S) (Measure.measurable_coe hS |>.comp hK) hφ]
    have hG : Measurable fun AB : (ℕ × ℕ → Bool) × (ℕ × ℕ → Bool) =>
        oldTrunc Th f (afterRound AB.1 s) (survN AB.1 s.nextLabel N)
          (relabCoins AB.1 s.nextLabel N AB.2) := by
      have : (fun AB : (ℕ × ℕ → Bool) × (ℕ × ℕ → Bool) =>
          oldTrunc Th f (afterRound AB.1 s) (survN AB.1 s.nextLabel N)
            (relabCoins AB.1 s.nextLabel N AB.2)) =
          fun AB => oldTrunc Th (f + 1) s N (spliceCoins AB.1 AB.2 1) := by
        funext AB
        rw [oldTrunc_splice_succ Th f s N _ _ hX, if_neg h0]
      rw [this]
      exact hF
    rw [Measure.map_apply hG hS, Measure.prod_apply (hG hS)]
    refine lintegral_congr fun A => ?_
    show fairCoinStreamLaw {B | oldTrunc Th f (afterRound A s) (survN A s.nextLabel N)
      (relabCoins A s.nextLabel N B) ∈ S} = _
    rw [oldCont, oldLaw, Measure.map_apply (measurable_oldTrunc Th f _ _) hS]
    conv_rhs => rw [← relabCoins_law A s.nextLabel N]
    rw [Measure.map_apply (measurable_relabCoins A _ _) (measurable_oldTrunc Th f _ _ hS)]
    rfl

end Law

end ttc.Tape
