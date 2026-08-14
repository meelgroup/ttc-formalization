/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVPackedRun
import Ttc.Volume.CousinsVempala

/-!
# Runwise sampler-error transfer followed by median amplification

Sampler TV is tensorized only over the `m * k` elementary draws in one estimator run.
If that costs at most `1/10`, exact success `4/5` transfers to approximate success `7/10`.
Independent approximate runs are then amplified by the usual median theorem.  Thus the
per-coordinate sampler accuracy is independent of the requested final failure probability.
-/

namespace Ttc.CVRunwise

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open scoped ENNReal

universe u

variable {E : Type u} [MeasurableSpace E]
variable {r m k : Nat}

/-- The joint law of the `m * k` elementary draws in one estimator run. -/
noncomputable def oneRunLaw (nu : Fin m -> Fin k -> Measure E) :
    Measure (Fin m -> Fin k -> E) :=
  Measure.pi fun i => Measure.pi (nu i)

instance oneRunLaw_isProbabilityMeasure
    (nu : Fin m -> Fin k -> Measure E) [forall i l, IsProbabilityMeasure (nu i l)] :
    IsProbabilityMeasure (oneRunLaw nu) := by
  unfold oneRunLaw
  infer_instance

/-- Repeat a single-run elementary law independently at each median repetition. -/
noncomputable def iidRunFamily (nu : Fin m -> Fin k -> Measure E) :
    Fin r -> Fin m -> Fin k -> Measure E :=
  fun _ i l => nu i l

/-- Tensorization inside one run costs `m * k * b`, with no repetition factor. -/
theorem tvLe_oneRunLaw_const
    {nu nuExact : Fin m -> Fin k -> Measure E}
    [forall i l, IsProbabilityMeasure (nu i l)]
    [forall i l, IsProbabilityMeasure (nuExact i l)]
    {b : ENNReal} (htv : forall i l, TVLe (nu i l) (nuExact i l) b) :
    TVLe (oneRunLaw nu) (oneRunLaw nuExact) ((m * k : Nat) * b) := by
  have hphase : forall i,
      TVLe (Measure.pi (nu i)) (Measure.pi (nuExact i)) ((k : Nat) * b) := by
    intro i
    have h := TVLe.pi (fun l => htv i l)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hrun := TVLe.pi hphase
  simpa [oneRunLaw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul,
    mul_assoc] using hrun

/-- An exact one-run success probability of `4/5` becomes at least `7/10` after replacing
all elementary draws by approximate laws whose total one-run TV budget is at most `1/10`.
-/
theorem oneRun_success_seven_tenths
    {nu nuExact : Fin m -> Fin k -> Measure E}
    [forall i l, IsProbabilityMeasure (nu i l)]
    [forall i l, IsProbabilityMeasure (nuExact i l)]
    {b : ENNReal} (hb : b ≠ ⊤)
    (htv : forall i l, TVLe (nu i l) (nuExact i l) b)
    (hbudget : ((m * k : Nat) : Real) * b.toReal <= 1 / 10)
    {V : (Fin m -> Fin k -> E) -> Real} (hV : Measurable V)
    {L U : Real}
    (hexact : 4 / 5 <= (oneRunLaw nuExact).real {omega | V omega ∈ Icc L U}) :
    7 / 10 <= (oneRunLaw nu).real {omega | V omega ∈ Icc L U} := by
  have hmkb : ((m * k : Nat) * b : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by
      simpa only [Nat.cast_mul] using ENNReal.natCast_ne_top (m * k)) hb
  have hset : MeasurableSet {omega | V omega ∈ Icc L U} := hV measurableSet_Icc
  have hdist :=
    (tvLe_oneRunLaw_const htv).abs_measureReal_sub_le hmkb hset
  have htoReal : ((m * k : Nat) * b : ENNReal).toReal =
      ((m * k : Nat) : Real) * b.toReal := by
    rw [ENNReal.toReal_mul]
    simp
  rw [htoReal] at hdist
  rw [abs_sub_le_iff] at hdist
  linarith

/-- **Source-faithful probability amplification.**

Only one approximate run is compared with one exact run.  The `m * k` sampler errors cost
at most `1/10`, yielding success `7/10`.  The outer `r` runs are iid under the approximate
law, and their median succeeds with probability `1-p`.  In particular, the hypothesis on
the elementary TV error `b` contains no `p` and no `r`. -/
theorem median_success_of_runwise_sampler_tv
    {nu nuExact : Fin m -> Fin k -> Measure E}
    [forall i l, IsProbabilityMeasure (nu i l)]
    [forall i l, IsProbabilityMeasure (nuExact i l)]
    {b : ENNReal} (hb : b ≠ ⊤)
    (htv : forall i l, TVLe (nu i l) (nuExact i l) b)
    (hbudget : ((m * k : Nat) : Real) * b.toReal <= 1 / 10)
    {V : (Fin m -> Fin k -> E) -> Real} (hV : Measurable V)
    {L U p : Real}
    (hexact : 4 / 5 <= (oneRunLaw nuExact).real {omega | V omega ∈ Icc L U})
    (hr : 0 < r) (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2) <= (r : Real)) :
    1 - p <=
      (Arlib.Probability.runMeasure
        (Arlib.GaussianCooling.packedPhaseLaw
          (iidRunFamily (r := r) nu))).real
        {omega : Arlib.Probability.RunSpace (Fin k -> E) r m |
          Arlib.Probability.medianSel (fun t : Fin r => V (omega t)) ∈ Icc L U} := by
  letI : forall t : Fin r, forall i : Fin m, forall l : Fin k,
      IsProbabilityMeasure (iidRunFamily (r := r) nu t i l) :=
    fun _ i l => inferInstanceAs (IsProbabilityMeasure (nu i l))
  let mu : Measure (Fin r -> Fin m -> Fin k -> E) :=
    Arlib.Probability.runMeasure
      (Arlib.GaussianCooling.packedPhaseLaw (iidRunFamily (r := r) nu))
  haveI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hsingle : 7 / 10 <= (oneRunLaw nu).real {omega | V omega ∈ Icc L U} :=
    oneRun_success_seven_tenths hb htv hbudget hV hexact
  have hcoord : forall t : Fin r,
      (MeasurePreserving
        (fun omega : Fin r -> Fin m -> Fin k -> E => omega t)
        mu (oneRunLaw nu)) := by
    intro t
    exact measurePreserving_eval (fun _ : Fin r => oneRunLaw nu) t
  have hq : forall t : Fin r, 7 / 10 <=
      mu.real {omega | V (omega t) ∈ Icc L U} := by
    intro t
    have hS : MeasurableSet {omega | V omega ∈ Icc L U} := hV measurableSet_Icc
    have hmap := (hcoord t).map_eq
    have heq : mu.real {omega | V (omega t) ∈ Icc L U} =
        (oneRunLaw nu).real {omega | V omega ∈ Icc L U} := by
      rw [← hmap]
      change (mu {omega | V (omega t) ∈ Icc L U}).toReal =
        ((Measure.map (fun omega => omega t) mu) {omega | V omega ∈ Icc L U}).toReal
      rw [Measure.map_apply (hcoord t).measurable hS]
      rfl
    rw [heq]
    exact hsingle
  have hv : forall t : Fin r, Measurable
      (fun omega : Fin r -> Fin m -> Fin k -> E => V (omega t)) :=
    fun t => hV.comp (measurable_pi_apply t)
  have hindep : iIndepFun
      (fun t (omega : Fin r -> Fin m -> Fin k -> E) => V (omega t)) mu := by
    dsimp [mu, Arlib.Probability.runMeasure, Arlib.GaussianCooling.packedPhaseLaw,
      iidRunFamily, oneRunLaw]
    exact iIndepFun_pi fun _ => hV.aemeasurable
  have hmed : forall omega : Fin r -> Fin m -> Fin k -> E,
      IsMedian (fun t => V (omega t))
        (Arlib.Probability.medianSel (fun t => V (omega t))) :=
    fun omega => Arlib.Probability.medianSel_isMedian _
  have hmain := Arlib.GaussianCooling.median_boost (μ := mu) hr hv hindep hmed hq
    (by norm_num) hp hrp
  exact hmain

end Ttc.CVRunwise

#print axioms Ttc.CVRunwise.tvLe_oneRunLaw_const
#print axioms Ttc.CVRunwise.oneRun_success_seven_tenths
#print axioms Ttc.CVRunwise.median_success_of_runwise_sampler_tv
