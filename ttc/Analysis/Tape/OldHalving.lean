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

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
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


/-! ## What round `0` leaves -/

section Round0

theorem mem_selectBy {α : Type} : ∀ (l : List α) (c : Fin l.length → Bool) (x : α),
    x ∈ selectBy l c ↔ ∃ i, l.get i = x ∧ c i = true
  | [], c, x => by simp [selectBy]
  | y :: l, c, x => by
      have ih := mem_selectBy l (Fin.tail c) x
      change x ∈ selectBy (y :: l) c ↔ ∃ i : Fin (l.length + 1), (y :: l).get i = x ∧ c i = true
      rw [Fin.exists_fin_succ]
      unfold selectBy
      split_ifs with h
      · simp only [List.mem_cons, ih, Fin.tail, List.get_eq_getElem, Fin.val_zero,
          List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, h, and_true]
        constructor
        · rintro (rfl | h'); exacts [Or.inl rfl, Or.inr h']
        · rintro (h' | h'); exacts [Or.inl h'.symm, Or.inr h']
      · simp only [ih, Fin.tail, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
          Fin.val_succ, List.getElem_cons_succ, h]
        simp

variable (Ls : List (ttc.SampleCopy n))

/-- The copies of `Ls` that the flags `κ` keep. -/
def keepSet (κ : Fin Ls.length → Bool) : Finset (ttc.SampleCopy n) := (selectBy Ls κ).toFinset

theorem samplesAfter_one_eq_keepSet (X : Finset (ttc.SampleCopy n)) (hX : Ls.toFinset = X)
    (A : ℕ × ℕ → Bool) :
    samplesAfter A 1 X = keepSet Ls (fun i => A (0, (Ls.get i).1)) := by
  classical
  ext copy
  simp only [samplesAfter, Finset.mem_filter, keepSet, List.mem_toFinset, mem_selectBy, survives_one,
    ← hX]
  constructor
  · rintro ⟨hc, h0⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hc
    exact ⟨i, hi, by rw [hi]; exact h0⟩
  · rintro ⟨i, hi, h0⟩
    exact ⟨List.mem_iff_get.mpr ⟨i, hi⟩, by rw [← hi]; exact h0⟩

theorem survN_eq_count (A : ℕ × ℕ → Bool) (nl N : ℕ) :
    survN A nl N = (Finset.univ.filter fun j : Fin N => A (0, nl + j) = true).card := by
  classical
  simp only [survN, survS, pendingSurvivorIndices, survives_one]
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hi, h⟩; exact ⟨⟨i, hi⟩, h, rfl⟩
  · rintro ⟨j, h, rfl⟩; exact ⟨j.isLt, h⟩

/-- **The round-0 coins of the stored copies and of the pending copies are independent fair
coins**, when the stored labels are distinct and below the pending ones. -/
theorem round0_coins_law (nl N : ℕ) (hlab : (Ls.map (·.1)).Nodup) (hbelow : ∀ c ∈ Ls, c.1 < nl) :
    fairCoinStreamLaw.map (fun A => ((fun i : Fin Ls.length => A (0, (Ls.get i).1)),
      (fun j : Fin N => A (0, nl + j)))) =
      (Measure.pi fun _ : Fin Ls.length => fairCoinLaw).prod (Measure.pi fun _ : Fin N => fairCoinLaw) := by
  have hP : ∀ _ : ℕ × ℕ, IsProbabilityMeasure fairCoinLaw := fun _ => ttc.fairCoinLaw_isProbabilityMeasure
  let ι : Fin Ls.length ⊕ Fin N → ℕ × ℕ := Sum.elim (fun i => (0, (Ls.get i).1)) (fun j => (0, nl + j))
  have hι : Function.Injective ι := by
    rintro (i | j) (i' | j') h
    · simp only [ι, Sum.elim_inl, Prod.mk.injEq, true_and] at h
      have hinj := List.nodup_iff_injective_get.mp hlab
      have := hinj (a₁ := ⟨i, by simp⟩) (a₂ := ⟨i', by simp⟩) (by simpa using h)
      congr 1
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · simp only [ι, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq, true_and] at h
      have := hbelow (Ls.get i) (List.get_mem Ls i)
      omega
    · simp only [ι, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq, true_and] at h
      have := hbelow (Ls.get i') (List.get_mem Ls i')
      omega
    · simp only [ι, Sum.elim_inr, Prod.mk.injEq, true_and] at h
      congr 1
      exact Fin.ext (by omega)
  have h1 : fairCoinStreamLaw.map (fun A t => A (ι t)) =
      Measure.pi fun _ : Fin Ls.length ⊕ Fin N => fairCoinLaw := by
    rw [ttc.fairCoinStreamLaw, Measure.map_infinitePi_infinitePi_of_inj hι]
    exact Measure.infinitePi_eq_pi _
  have hm : Measurable fun A : ℕ × ℕ → Bool => fun t => A (ι t) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply _
  have hfun : (fun A : ℕ × ℕ → Bool => ((fun i : Fin Ls.length => A (0, (Ls.get i).1)),
      (fun j : Fin N => A (0, nl + j)))) =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin Ls.length ⊕ Fin N => Bool)) ∘
        fun A t => A (ι t) := by
    funext A
    rfl
  rw [hfun, ← Measure.map_map (MeasurableEquiv.measurable _) hm, h1]
  exact (measurePreserving_sumPiEquivProdPi (fun _ : Fin Ls.length ⊕ Fin N => fairCoinLaw)).map_eq

end Round0


section Round0Law

variable (Th : ℝ) (Ls : List (ttc.SampleCopy n))

/-- **What round `0` leaves**: the stored copies, each kept by a fair coin, and a
`Binomial(N, 1/2)` number of pending copies, independent. -/
theorem round0_law (s : TTCState n) (N : ℕ) (hX : Ls.toFinset = s.X) (hlab : (Ls.map (·.1)).Nodup)
    (hbelow : ∀ c ∈ Ls, c.1 < s.nextLabel) :
    fairCoinStreamLaw.map (fun A => (samplesAfter A 1 s.X, survN A s.nextLabel N)) =
      ((Measure.pi fun _ : Fin Ls.length => fairCoinLaw).prod (binomial N ttc.fairProbability)).map
        fun q => (keepSet Ls q.1, q.2) := by
  classical
  let cnt : (Fin N → Bool) → ℕ := fun bits => (Finset.univ.filter fun j => bits j = true).card
  have hfun : (fun A : ℕ × ℕ → Bool => (samplesAfter A 1 s.X, survN A s.nextLabel N)) =
      (fun q : (Fin Ls.length → Bool) × (Fin N → Bool) => (keepSet Ls q.1, cnt q.2)) ∘
        fun A => ((fun i : Fin Ls.length => A (0, (Ls.get i).1)),
          (fun j : Fin N => A (0, s.nextLabel + j))) := by
    funext A
    simp only [Function.comp_apply, samplesAfter_one_eq_keepSet Ls s.X hX A, survN_eq_count, cnt]
  have hm : Measurable fun A : ℕ × ℕ → Bool => ((fun i : Fin Ls.length => A (0, (Ls.get i).1)),
      (fun j : Fin N => A (0, s.nextLabel + j))) :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply _).prodMk
      (measurable_pi_iff.mpr fun j => measurable_pi_apply _)
  have hcnt : (Measure.pi fun _ : Fin N => fairCoinLaw).map cnt = binomial N ttc.fairProbability := by
    have := ttc.finite_bernoulli_count_law (Fin N) ttc.fairProbability
    rw [Fintype.card_fin] at this
    exact this
  rw [hfun, ← Measure.map_map (measurable_of_countable _) hm, round0_coins_law Ls s.nextLabel N hlab hbelow,
    show (fun q : (Fin Ls.length → Bool) × (Fin N → Bool) => (keepSet Ls q.1, cnt q.2)) =
      (fun q => (keepSet Ls q.1, q.2)) ∘ Prod.map id cnt from rfl,
    ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    ← Measure.map_prod_map _ _ measurable_id (measurable_of_countable _), Measure.map_id, hcnt]

/-- **One round of the old loop**: stop, or keep each stored copy by a fair coin, draw the
pending count from `Binomial(N, 1/2)`, halve `p`, and go on with fresh coins. -/
theorem oldLaw_succ' (f : ℕ) (s : TTCState n) (N : ℕ) (hX : Ls.toFinset = s.X)
    (hlab : (Ls.map (·.1)).Nodup) (hbelow : ∀ c ∈ Ls, c.1 < s.nextLabel) :
    oldLaw Th (f + 1) s N =
      if ((s.X.card + N : ℕ) : ℝ) ≤ Th then Measure.dirac (some (s, N))
      else ((Measure.pi fun _ : Fin Ls.length => fairCoinLaw).prod
        (binomial N ttc.fairProbability)).bind fun q => oldCont Th f s (keepSet Ls q.1, q.2) := by
  have hX' : StoredBelow s.X s.nextLabel := by
    intro c hc
    rw [← hX, List.mem_toFinset] at hc
    exact hbelow c hc
  rw [oldLaw_succ Th f s N hX', round0_law Ls s N hX hlab hbelow,
    Measure.bind_map (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]

end Round0Law


/-! ## The sealed halving loop is the old one -/

section Match

open ttc.Program
open ttc.Tape.Tree

theorem selectBy_sublist {α : Type} : ∀ (l : List α) (c : Fin l.length → Bool), (selectBy l c).Sublist l
  | [], _ => List.Sublist.slnil
  | x :: l, c => by
      unfold selectBy
      split_ifs
      · exact (selectBy_sublist l (Fin.tail c)).cons₂ x
      · exact (selectBy_sublist l (Fin.tail c)).cons x

theorem selectBy_map_rel {α β γ : Type} (f : α → γ) (g : β → γ) :
    ∀ (l₁ : List α) (l₂ : List β) (hlen : l₁.length = l₂.length) (_ : l₁.map f = l₂.map g)
      (c : Fin l₁.length → Bool),
      (selectBy l₁ c).map f = (selectBy l₂ (c ∘ Fin.cast hlen.symm)).map g
  | [], [], _, _, c => rfl
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | x :: l₁, y :: l₂, hlen, h, c => by
      simp only [List.map_cons, List.cons.injEq] at h
      have hlen' : l₁.length = l₂.length := by simpa using hlen
      have ih := selectBy_map_rel f g l₁ l₂ hlen' h.2 (Fin.tail c)
      have htail : Fin.tail (c ∘ Fin.cast hlen.symm) = Fin.tail c ∘ Fin.cast hlen'.symm := by
        funext i
        exact congrArg c (Fin.ext rfl)
      have h0 : (c ∘ Fin.cast hlen.symm) 0 = c 0 := congrArg c (Fin.ext rfl)
      unfold selectBy
      rw [h0, htail]
      by_cases hc : c 0 = true
      · simp only [hc, ite_true, List.map_cons, h.1, ih]
      · simp only [hc, Bool.false_eq_true, ite_false]
        exact ih

theorem pi_bind_cast {γ : Type} [MeasurableSpace γ] {a b : ℕ} (h : a = b) (μ : Measure Bool)
    (F : (Fin b → Bool) → Measure γ) :
    (Measure.pi fun _ : Fin b => μ).bind F =
      (Measure.pi fun _ : Fin a => μ).bind fun c => F (c ∘ Fin.cast h.symm) := by
  subst h
  rfl

theorem prod_bind_countable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    (F : α × β → Measure γ) :
    (μ.prod ν).bind F = μ.bind fun a => ν.bind fun b => F (a, b) := by
  ext S hS
  rw [Measure.bind_apply hS (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hS (measurable_of_countable _).aemeasurable,
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [Measure.bind_apply hS (measurable_of_countable _).aemeasurable]

theorem half_eq_fairProbability : half = ttc.fairProbability := by
  apply Subtype.ext
  simp [ttc.fairProbability, half, Set.projIcc]
  norm_num

instance : Countable (Num ℤ) := Function.Injective.countable Num.get_injective

instance : MeasurableSingletonClass (Num ℤ) := ⟨fun x => by
  have h := (Num.measurable_get (α := ℤ)) (measurableSet_singleton x.get)
  convert h using 1
  ext y
  simp [Num.get_injective.eq_iff]⟩

/-- A multiset of lattice points, by a fixed injective numbering. -/
def encMS : Multiset (Fin n → ℤ) → ℕ := (Countable.exists_injective_nat _).choose

/-- The old loop's result, as `p`, the multiset of its copies' points, and the pending count. -/
def viewOld : Option (TTCState n × ℕ) → Option (ℝ × ℕ × ℕ) :=
  Option.map fun r => ((r.1.p : ℝ), encMS (r.1.X.val.map fun c => c.2.2), r.2)

/-- The sealed loop's result, read the same way. -/
def viewNew : Option (Num ℝ × List (Fin n → Num ℤ) × Num ℕ × Num ℕ) → Option (ℝ × ℕ × ℕ) :=
  Option.map fun r => (r.1.get, encMS ((r.2.1.map getZ : List _) : Multiset (Fin n → ℤ)), r.2.2.2.get)

theorem measurable_viewOld : Measurable (viewOld (n := n)) := by
  have hst : Measurable fun s : TTCState n => (s.p, s.X, s.nextLabel) :=
    Measurable.of_comap_le le_rfl
  refine measurable_optionMap ?_
  refine ((measurable_coe_nnreal_real.comp (measurable_fst.comp hst)).comp measurable_fst).prodMk
    (((measurable_of_countable (fun X : Finset (ttc.SampleCopy n) =>
      encMS (X.val.map fun c => c.2.2))).comp ((measurable_fst.comp measurable_snd).comp hst)).comp
        measurable_fst |>.prodMk measurable_snd)

theorem measurable_viewNew : Measurable (viewNew (n := n)) := by
  refine measurable_optionMap ?_
  refine (Num.measurable_get.comp measurable_fst).prodMk ?_
  refine Measurable.prodMk ?_ (Num.measurable_get.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hL : Measurable fun l : List (Fin n → Num ℤ) =>
      encMS ((l.map getZ : List _) : Multiset (Fin n → ℤ)) := by
    have := measurable_of_ofFn (X := Unit) (α := Fin n → Num ℤ)
      (F := fun p => encMS ((p.2.map getZ : List _) : Multiset (Fin n → ℤ)))
      (fun k => measurable_of_countable _)
    exact this.comp ((measurable_const (a := ())).prodMk measurable_id)
  exact hL.comp (measurable_fst.comp measurable_snd)

theorem multiset_points (Ls : List (ttc.SampleCopy n)) (X : List (Fin n → Num ℤ))
    (s : TTCState n) (hXL : X.map getZ = Ls.map fun c => c.2.2) (hX : Ls.toFinset = s.X)
    (hnd : Ls.Nodup) :
    ((X.map getZ : List _) : Multiset (Fin n → ℤ)) = s.X.val.map fun c => c.2.2 := by
  classical
  rw [hXL, ← hX, List.toFinset_val, List.dedup_eq_self.mpr hnd, Multiset.map_coe]

/-- **The sealed halving loop is the old second loop**, with at most `f` rounds, read as
`p`, the multiset of the copies' points and the pending count: when the sealed state lists
the old state's copies in some order with distinct labels below its next label. -/
theorem halveT_eq_oldLaw (K : Params) (b : ℕ) :
    ∀ (f : ℕ) (p : Num ℝ) (X : List (Fin n → Num ℤ)) (size N : Num ℕ) (s : TTCState n)
      (Ls : List (ttc.SampleCopy n)),
      p.get = s.p → X.map getZ = Ls.map (fun c => c.2.2) → size.get = Ls.length →
      Ls.toFinset = s.X → (Ls.map (·.1)).Nodup → (∀ c ∈ Ls, c.1 < s.nextLabel) →
      (vlaw (halveT K f p X size N) b).map viewNew =
        (oldLaw K.thresh.get f s N.get).map viewOld
  | 0, p, X, size, N, s, Ls, _, _, _, _, _, _ => by
      show (vlaw Tree.fail b).map _ = _
      rw [vlaw_fail, oldLaw_zero, Measure.map_dirac' measurable_viewNew,
        Measure.map_dirac' measurable_viewOld]
      rfl
  | f + 1, p, X, size, N, s, Ls, hp, hXL, hsize, hX, hlab, hbelow => by
      classical
      have hnd : Ls.Nodup := List.Nodup.of_map _ hlab
      have hcard : s.X.card = Ls.length := by rw [← hX, List.toFinset_card_of_nodup hnd]
      have hlen : X.length = Ls.length := by
        simpa using congrArg List.length hXL
      rw [vlaw_halveT_succ, oldLaw_succ' K.thresh.get Ls f s N.get hX hlab hbelow, hsize, hcard]
      split_ifs with hc
      · rw [Measure.map_dirac' measurable_viewNew, Measure.map_dirac' measurable_viewOld]
        simp only [viewNew, viewOld, Option.map_some, hp, multiset_points Ls X s hXL hX hnd]
      · rw [prod_bind_countable, pi_bind_cast hlen, ← half_eq_fairProbability,
          Measure.map_bind (measurable_of_countable _).aemeasurable measurable_viewNew.aemeasurable,
          Measure.map_bind (measurable_of_countable _).aemeasurable measurable_viewOld.aemeasurable]
        congr 1
        funext c
        rw [Measure.map_bind (measurable_of_countable _).aemeasurable measurable_viewNew.aemeasurable,
          Measure.map_bind (measurable_of_countable _).aemeasurable measurable_viewOld.aemeasurable]
        congr 1
        funext N'
        have hsel := selectBy_map_rel getZ (fun c : ttc.SampleCopy n => c.2.2) X Ls hlen hXL c
        have hsub := (selectBy_sublist Ls (c ∘ Fin.cast hlen.symm)).map (·.1)
        have hlen' : (selectBy X c).length = (selectBy Ls (c ∘ Fin.cast hlen.symm)).length := by
          simpa using congrArg List.length hsel
        exact halveT_eq_oldLaw K b f _ _ _ _ ⟨s.p / 2, keepSet Ls (c ∘ Fin.cast hlen.symm),
            s.nextLabel⟩ (selectBy Ls (c ∘ Fin.cast hlen.symm))
          (by simp [A.divLit, A.div, A.lit, Num.get_div, Num.get_lit, hp])
          hsel (by simp [hlen']) rfl (hsub.nodup hlab)
          (fun c' hc' => hbelow c' ((selectBy_sublist Ls _).subset hc'))

end Match

end ttc.Tape
