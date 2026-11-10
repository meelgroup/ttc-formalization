import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Model.Program
import Kr25Ssmxt.Analysis.MeasurableFixedSfiniteBind
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Forgetting a real-RAM operation trace

The costed program is a writer-style composition of measure-valued steps.
These lemmas prove that operation counts do not change its output law.
-/

namespace Kr25Ssmxt

open MeasureTheory

instance TTCState.instMeasurableSingletonClass (n : Nat) :
    MeasurableSingletonClass (TTCState n) where
  measurableSet_singleton s := by
    let f : TTCState n → NNReal × Finset (SampleCopy n) × Nat :=
      fun t => (t.p, t.X, t.nextLabel)
    have hinj : Function.Injective f := by
      intro x y h
      cases x
      cases y
      simp only [f, Prod.mk.injEq] at h
      congr
      all_goals tauto
    have hset : ({s} : Set (TTCState n)) = f ⁻¹' {f s} := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact (hinj.eq_iff).symm
    rw [hset]
    exact ⟨{f s}, measurableSet_singleton _, rfl⟩

theorem costedCharge_fst {α : Type*} [MeasurableSpace α]
    (law : Measure α) (operations : Nat) :
    (costedCharge law operations).map Prod.fst = law := by
  unfold costedCharge
  rw [Measure.map_map measurable_fst (by fun_prop)]
  change law.map id = law
  exact Measure.map_id

theorem costedCharge_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (law : Measure α) [IsProbabilityMeasure law] (operations : Nat) :
    IsProbabilityMeasure (costedCharge law operations) := by
  unfold costedCharge
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- A charged law has the same total mass as its output marginal. -/
theorem costed_probability_of_fst {α : Type*} [MeasurableSpace α]
    (law : Measure (α × Nat))
    (hprob : IsProbabilityMeasure (law.map Prod.fst)) :
    IsProbabilityMeasure law := by
  apply IsProbabilityMeasure.mk
  have hmass : (law.map Prod.fst) Set.univ = law Set.univ := by
    rw [Measure.map_apply measurable_fst MeasurableSet.univ]
    simp
  rw [← hmass]
  exact hprob.measure_univ

set_option maxHeartbeats 800000 in
theorem costedBind_dirac_eq_map {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (law : Measure (α × Nat)) (f : α → β) (g : α → Nat)
    (hf : Measurable f) (hg : Measurable g) :
    costedBind law (fun x => costedCharge (Measure.dirac (f x)) (g x)) =
      law.map (fun result => (f result.1, result.2 + g result.1)) := by
  unfold costedBind costedCharge
  simp only [Measure.map_dirac]
  have hmap : Measurable (fun result : α × Nat =>
      (f result.1, result.2 + g result.1)) :=
    (hf.comp measurable_fst).prodMk
      (measurable_snd.add (hg.comp measurable_fst))
  exact Measure.bind_dirac_eq_map law hmap

theorem costedCharge_expected_cost {α : Type*} [MeasurableSpace α]
    (law : Measure α) [IsProbabilityMeasure law] (operations : Nat) :
    ∫⁻ result, (result.2 : ENNReal) ∂costedCharge law operations = operations := by
  unfold costedCharge
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]

theorem costedCharge_mass_le_one {α : Type*} [MeasurableSpace α]
    (law : Measure α) (operations : Nat) (hlaw : law Set.univ ≤ 1) :
    (costedCharge law operations) Set.univ ≤ 1 := by
  unfold costedCharge
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simpa using hlaw

theorem map_bind_measure {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (law : Measure α) (step : α → Measure β) (f : β → γ)
    (hstep : AEMeasurable step law) (hf : Measurable f) :
    (law.bind step).map f = law.bind fun x => (step x).map f := by
  ext s hs
  have hmapstep : AEMeasurable (fun x => (step x).map f) law :=
    (Measure.measurable_map f hf).comp_aemeasurable hstep
  calc
    ((law.bind step).map f) s = (law.bind step) (f ⁻¹' s) :=
      Measure.map_apply hf hs
    _ = ∫⁻ x, step x (f ⁻¹' s) ∂law := Measure.bind_apply (hf hs) hstep
    _ = ∫⁻ x, ((step x).map f) s ∂law :=
      lintegral_congr fun x => (Measure.map_apply hf hs).symm
    _ = (law.bind fun x => (step x).map f) s :=
      (Measure.bind_apply hs hmapstep).symm

private theorem measurable_costedContinuation {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (next : α → Measure (β × Nat)) (hnext : Measurable next) :
    Measurable (fun result : α × Nat =>
      (next result.1).map fun future => (future.1, result.2 + future.2)) := by
  apply measurable_from_prod_countable_left
  intro cost
  exact (Measure.measurable_map
    (fun future : β × Nat => (future.1, cost + future.2)) (by fun_prop)).comp hnext

/-- Composing normalized charged kernels preserves total probability. -/
theorem costedBind_isProbabilityMeasure {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) [IsProbabilityMeasure first]
    (next : α → Measure (β × Nat)) (hnext : Measurable next)
    (hprob : ∀ x, IsProbabilityMeasure (next x)) :
    IsProbabilityMeasure (costedBind first next) := by
  unfold costedBind
  apply isProbabilityMeasure_bind
    (measurable_costedContinuation next hnext).aemeasurable
  filter_upwards with result
  letI : IsProbabilityMeasure (next result.1) := hprob result.1
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem costedBind_kernel_measurable {X α β : Type*}
    [MeasurableSpace X] [MeasurableSpace α] [MeasurableSpace β]
    (first : X → Measure (α × Nat)) (next : α → Measure (β × Nat))
    (hfirst : Measurable first) (hnext : Measurable next) :
    Measurable (fun x => costedBind (first x) next) := by
  let continuation : (α × Nat) → Measure (β × Nat) := fun result =>
    (next result.1).map fun future => (future.1, result.2 + future.2)
  have hcont : Measurable continuation := measurable_costedContinuation next hnext
  exact (Measure.measurable_bind' hcont).comp hfirst

theorem costedBind_costedCharge_eq_bind {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (law : Measure α) (operations : Nat)
    (next : α → Measure (β × Nat)) (hnext : Measurable next) :
    costedBind (costedCharge law operations) next =
      law.bind fun x => (next x).map fun future =>
        (future.1, operations + future.2) := by
  let f : α → α × Nat := fun x => (x, operations)
  let K : α × Nat → Measure (β × Nat) := fun result =>
    (next result.1).map fun future => (future.1, result.2 + future.2)
  have hf : Measurable f := measurable_id.prodMk measurable_const
  have hK : Measurable K := measurable_costedContinuation next hnext
  change (law.map f).bind K = _
  calc
    (law.map f).bind K = (law.bind fun x => Measure.dirac (f x)).bind K := by
      rw [Measure.bind_dirac_eq_map law hf]
    _ = law.bind fun x => (Measure.dirac (f x)).bind K :=
      Measure.bind_bind ((Measure.measurable_dirac.comp hf).aemeasurable) hK.aemeasurable
    _ = law.bind fun x => K (f x) := by simp only [Measure.dirac_bind hK]
    _ = _ := rfl

theorem costedBind_costedCharge_dirac_eq_map {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (x : α) (operations : Nat) (next : α → Measure (β × Nat))
    (hnext : Measurable next) :
    costedBind (costedCharge (Measure.dirac x) operations) next =
      (next x).map (fun future => (future.1, operations + future.2)) := by
  rw [costedBind_costedCharge_eq_bind _ _ _ hnext]
  have hshift : Measurable (fun z =>
      (next z).map (fun future => (future.1, operations + future.2))) :=
    (Measure.measurable_map _ (by fun_prop)).comp hnext
  exact Measure.dirac_bind hshift x

theorem measurable_nat_bind_kernel {X β : Type*}
    [MeasurableSpace X] [MeasurableSpace β]
    (law : X → Measure Nat) (next : X × Nat → Measure β)
    (hlaw : Measurable law) (hnext : Measurable next) :
    Measurable (fun x => (law x).bind fun pending => next (x, pending)) := by
  apply Measure.measurable_of_measurable_coe
  intro event hevent
  have hsection (x : X) : Measurable (fun pending : Nat => next (x, pending)) :=
    Measurable.of_discrete
  simp_rw [Measure.bind_apply hevent (hsection _).aemeasurable,
    lintegral_countable']
  apply Measurable.tsum
  intro pending
  exact ((Measure.measurable_coe hevent).comp
      (hnext.comp (measurable_id.prodMk measurable_const))).mul
    ((Measure.measurable_coe (measurableSet_singleton pending)).comp hlaw)

theorem measurable_nat_costedCharge_bind_kernel {X β : Type*}
    [MeasurableSpace X] [MeasurableSpace β]
    (law : X → Measure Nat) (next : X × Nat → Measure (β × Nat))
    (operations : Nat) (hlaw : Measurable law) (hnext : Measurable next) :
    Measurable (fun x => costedBind (costedCharge (law x) operations)
      (fun pending => next (x, pending))) := by
  let shift : β × Nat → β × Nat := fun future =>
    (future.1, operations + future.2)
  have hshift : Measurable shift := by fun_prop
  have hnextShift : Measurable (fun z : X × Nat => (next z).map shift) :=
    (Measure.measurable_map shift hshift).comp hnext
  have htail := measurable_nat_bind_kernel law
    (fun z : X × Nat => (next z).map shift) hlaw hnextShift
  have heq :
      (fun x => costedBind (costedCharge (law x) operations)
        (fun pending => next (x, pending))) =
      (fun x => (law x).bind fun pending => (next (x, pending)).map shift) := by
    funext x
    exact costedBind_costedCharge_eq_bind (law x) operations
      (fun pending => next (x, pending)) Measurable.of_discrete
  rw [heq]
  exact htail

set_option maxHeartbeats 800000 in
theorem measurable_costedBind_fixed_source_map_kernel {X Y α β : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSpace β]
    (source : Measure Y) [SFinite source]
    (draw : X × Y → α × Nat)
    (next : X × α → Measure (β × Nat))
    (hdraw : Measurable draw) (hnext : Measurable next) :
    Measurable (fun x => costedBind
      (source.map fun y => draw (x, y))
      (fun a => next (x, a))) := by
  let C : X × (α × Nat) → Measure (β × Nat) := fun z =>
    (next (z.1, z.2.1)).map fun future =>
      (future.1, z.2.2 + future.2)
  have hC : Measurable C := by
    let C' : (X × α) × Nat → Measure (β × Nat) := fun z =>
      (next z.1).map fun future => (future.1, z.2 + future.2)
    have hC' : Measurable C' := by
      apply measurable_from_prod_countable_left
      intro cost
      exact (Measure.measurable_map
        (fun future : β × Nat => (future.1, cost + future.2)) (by fun_prop)).comp hnext
    exact hC'.comp
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  let K : X × Y → Measure (β × Nat) := fun z => C (z.1, draw z)
  have hK : Measurable K := hC.comp (measurable_fst.prodMk hdraw)
  have hfixed := measurable_fixed_sfinite_bind source K hK
  have heq :
      (fun x => costedBind (source.map fun y => draw (x, y))
        (fun a => next (x, a))) =
      (fun x => source.bind fun y => K (x, y)) := by
    funext x
    let f : Y → α × Nat := fun y => draw (x, y)
    have hf : Measurable f := hdraw.comp (measurable_const.prodMk measurable_id)
    let G : α × Nat → Measure (β × Nat) := fun a => C (x, a)
    have hG : Measurable G := hC.comp (measurable_const.prodMk measurable_id)
    change (source.map f).bind G = source.bind fun y => G (f y)
    calc
      (source.map f).bind G =
          (source.bind fun y => Measure.dirac (f y)).bind G := by
        rw [Measure.bind_dirac_eq_map source hf]
      _ = source.bind fun y => (Measure.dirac (f y)).bind G :=
        Measure.bind_bind ((Measure.measurable_dirac.comp hf).aemeasurable)
          hG.aemeasurable
      _ = source.bind fun y => G (f y) := by simp only [Measure.dirac_bind hG]
  rw [heq]
  exact hfixed

theorem measurable_map_dependent_finite {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (law : X → Measure Y) (f : X × Y → Z)
    (hlaw : Measurable law) (hf : Measurable f)
    (hmass : ∀ x, law x Set.univ ≤ 1) :
    Measurable (fun x => (law x).map fun y => f (x, y)) := by
  let κ : ProbabilityTheory.Kernel X Y := ⟨law, hlaw⟩
  have hfinite : ∀ x, IsFiniteMeasure (κ x) := fun x =>
    ⟨lt_of_le_of_lt (hmass x) ENNReal.one_lt_top⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hset : MeasurableSet (f ⁻¹' s) := hf hs
  have hbase := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite
    (κ := κ) hset hfinite
  have heq :
      (fun x => ((law x).map fun y => f (x, y)) s) =
      (fun x => κ x (Prod.mk x ⁻¹' (f ⁻¹' s))) := by
    funext x
    have hfx : Measurable (fun y => f (x, y)) :=
      hf.comp measurable_prodMk_left
    rw [Measure.map_apply hfx hs]
    rfl
  rw [heq]
  exact hbase

theorem measurable_costedBind_dependent_finite {X α β : Type*}
    [MeasurableSpace X] [MeasurableSpace α] [MeasurableSpace β]
    (first : X → Measure (α × Nat))
    (next : X × α → Measure (β × Nat))
    (hfirst : Measurable first) (hnext : Measurable next)
    (hmass : ∀ x, first x Set.univ ≤ 1) :
    Measurable (fun x => costedBind (first x) (fun a => next (x, a))) := by
  let C : X × (α × Nat) → Measure (β × Nat) := fun z =>
    (next (z.1, z.2.1)).map fun future =>
      (future.1, z.2.2 + future.2)
  have hC : Measurable C := by
    let C' : (X × α) × Nat → Measure (β × Nat) := fun z =>
      (next z.1).map fun future => (future.1, z.2 + future.2)
    have hC' : Measurable C' := by
      apply measurable_from_prod_countable_left
      intro cost
      exact (Measure.measurable_map
        (fun future : β × Nat => (future.1, cost + future.2)) (by fun_prop)).comp hnext
    exact hC'.comp
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  let lift : X × (α × Nat) → X × (α × Nat) := id
  have hlift : Measurable (fun x =>
      (first x).map fun a => (x, a)) :=
    measurable_map_dependent_finite first lift hfirst measurable_id hmass
  have hbind : Measurable (fun x =>
      ((first x).map fun a => (x, a)).bind C) :=
    (Measure.measurable_bind' hC).comp hlift
  have heq :
      (fun x => costedBind (first x) (fun a => next (x, a))) =
      (fun x => ((first x).map fun a => (x, a)).bind C) := by
    funext x
    let f : α × Nat → X × (α × Nat) := fun a => (x, a)
    have hf : Measurable f := measurable_const.prodMk measurable_id
    change (first x).bind (fun a => C (x, a)) = ((first x).map f).bind C
    calc
      (first x).bind (fun a => C (x, a)) =
          (first x).bind (fun a => (Measure.dirac (f a)).bind C) := by
        simp only [Measure.dirac_bind hC]
        rfl
      _ = ((first x).bind fun a => Measure.dirac (f a)).bind C :=
        (Measure.bind_bind ((Measure.measurable_dirac.comp hf).aemeasurable)
          hC.aemeasurable).symm
      _ = ((first x).map f).bind C := by
        rw [Measure.bind_dirac_eq_map (first x) hf]
  rw [heq]
  exact hbind

theorem costedBind_fst {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) (next : α → Measure (β × Nat))
    (hnext : Measurable next) :
    (costedBind first next).map Prod.fst =
      (first.map Prod.fst).bind fun x => (next x).map Prod.fst := by
  let continuation : (α × Nat) → Measure (β × Nat) := fun result =>
    (next result.1).map fun future => (future.1, result.2 + future.2)
  have hcont : Measurable continuation := measurable_costedContinuation next hnext
  unfold costedBind
  rw [map_bind_measure first continuation Prod.fst hcont.aemeasurable measurable_fst]
  have hpoint : ∀ result : α × Nat,
      (continuation result).map Prod.fst = (next result.1).map Prod.fst := by
    intro result
    unfold continuation
    rw [Measure.map_map measurable_fst (by fun_prop)]
    rfl
  simp only [hpoint]
  change first.bind (fun result => (next result.1).map Prod.fst) =
    (first.map Prod.fst).bind (fun x => (next x).map Prod.fst)
  unfold Measure.bind
  rw [Measure.map_map (by fun_prop) measurable_fst]
  rfl

/-- Expected cost of a charged composition, assuming each continuation is a
probability law. This is the accounting identity used for TTC components. -/
theorem costedBind_lintegral_cost {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) (next : α → Measure (β × Nat))
    (hnext : Measurable next)
    (hprob : ∀ x, IsProbabilityMeasure (next x)) :
    ∫⁻ run, (run.2 : ENNReal) ∂costedBind first next =
      ∫⁻ result, (result.2 : ENNReal) +
        ∫⁻ future, (future.2 : ENNReal) ∂next result.1 ∂first := by
  let continuation : (α × Nat) → Measure (β × Nat) := fun result =>
    (next result.1).map fun future => (future.1, result.2 + future.2)
  have hcont : Measurable continuation := measurable_costedContinuation next hnext
  unfold costedBind
  rw [Measure.lintegral_bind hcont.aemeasurable (by fun_prop)]
  congr 1
  funext result
  change (∫⁻ run, (run.2 : ENNReal) ∂continuation result) = _
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  simp only [Nat.cast_add]
  rw [lintegral_add_left (by fun_prop)]
  haveI : IsProbabilityMeasure (next result.1) := hprob result.1
  simp only [lintegral_const, measure_univ, mul_one]

/-- An upper expected-cost inequality requiring only subprobability
continuations. It applies to adaptive TTC binds before kernel measurability
has been established. -/
theorem costedBind_lintegral_cost_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) (next : α → Measure (β × Nat))
    (hnextMeas : Measurable next)
    (hnext : ∀ x, (next x) Set.univ ≤ 1) :
    ∫⁻ run, (run.2 : ENNReal) ∂costedBind first next ≤
      ∫⁻ result, (result.2 : ENNReal) +
        ∫⁻ future, (future.2 : ENNReal) ∂next result.1 ∂first := by
  let continuation : (α × Nat) → Measure (β × Nat) := fun result =>
    (next result.1).map fun future => (future.1, result.2 + future.2)
  have hmap (result : α × Nat) :
      (∫⁻ run, (run.2 : ENNReal) ∂continuation result) =
      (result.2 : ENNReal) * (next result.1) Set.univ +
        ∫⁻ future, (future.2 : ENNReal) ∂next result.1 := by
    unfold continuation
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    simp only [Nat.cast_add]
    rw [lintegral_add_left (by fun_prop)]
    simp only [lintegral_const]
  unfold costedBind
  apply (Measure.lintegral_bind_le _ first
    (measurable_costedContinuation next hnextMeas).aemeasurable).trans
  apply lintegral_mono
  intro result
  change (∫⁻ run, (run.2 : ENNReal) ∂continuation result) ≤ _
  rw [hmap]
  exact add_le_add_left
    (mul_le_of_le_one_right (by positivity) (hnext result.1)) _

theorem costedBind_mass_le_one {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) (next : α → Measure (β × Nat))
    (hnextMeas : Measurable next)
    (hfirst : first Set.univ ≤ 1) (hnext : ∀ x, (next x) Set.univ ≤ 1) :
    (costedBind first next) Set.univ ≤ 1 := by
  let continuation : (α × Nat) → Measure (β × Nat) := fun result =>
    (next result.1).map fun future => (future.1, result.2 + future.2)
  have hcont (result : α × Nat) : continuation result Set.univ ≤ 1 := by
    unfold continuation
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simpa using hnext result.1
  unfold costedBind
  calc
    (first.bind continuation) Set.univ ≤
        ∫⁻ result, continuation result Set.univ ∂first :=
      Measure.bind_apply_le
        (measurable_costedContinuation next hnextMeas).aemeasurable
        MeasurableSet.univ
    _ ≤ ∫⁻ _result, (1 : ENNReal) ∂first := lintegral_mono hcont
    _ = first Set.univ := by simp
    _ ≤ 1 := hfirst

/-- Uniform one-step cost bounds add across adaptive charged binds, even
when the adaptive kernel has not yet been shown measurable. -/
theorem costedBind_expected_cost_le_add {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) (next : α → Measure (β × Nat))
    (hnextMeas : Measurable next)
    (hfirstMass : first Set.univ ≤ 1)
    (hnextMass : ∀ x, (next x) Set.univ ≤ 1)
    {firstBudget nextBudget : ENNReal}
    (hfirstCost : (∫⁻ result, (result.2 : ENNReal) ∂first) ≤ firstBudget)
    (hnextCost : ∀ x, (∫⁻ result, (result.2 : ENNReal) ∂next x) ≤ nextBudget) :
    (∫⁻ result, (result.2 : ENNReal) ∂costedBind first next) ≤
      firstBudget + nextBudget := by
  apply (costedBind_lintegral_cost_le first next hnextMeas hnextMass).trans
  have hpoint :
      (∫⁻ result, (result.2 : ENNReal) +
        ∫⁻ future, (future.2 : ENNReal) ∂next result.1 ∂first) ≤
      ∫⁻ result, (result.2 : ENNReal) + nextBudget ∂first := by
    apply lintegral_mono
    intro result
    simpa using add_le_add_left (hnextCost result.1) (result.2 : ENNReal)
  apply hpoint.trans
  rw [lintegral_add_left (by fun_prop)]
  simp only [lintegral_const]
  exact add_le_add hfirstCost
    (mul_le_of_le_one_right (by positivity) hfirstMass)

/-- The same accounting rule when a continuation bound holds almost surely
for the state produced by the first computation. This permits TTC's thinning
guard and stored-population invariant to be used inside adaptive binds. -/
theorem costedBind_expected_cost_le_add_ae {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) (next : α → Measure (β × Nat))
    (hnextMeas : Measurable next)
    (hfirstMass : first Set.univ ≤ 1)
    (hnextMass : ∀ x, (next x) Set.univ ≤ 1)
    {firstBudget nextBudget : ENNReal}
    (hfirstCost : (∫⁻ result, (result.2 : ENNReal) ∂first) ≤ firstBudget)
    (hnextCost : ∀ᵐ result ∂first,
      (∫⁻ future, (future.2 : ENNReal) ∂next result.1) ≤ nextBudget) :
    (∫⁻ result, (result.2 : ENNReal) ∂costedBind first next) ≤
      firstBudget + nextBudget := by
  apply (costedBind_lintegral_cost_le first next hnextMeas hnextMass).trans
  have hpoint :
      (∫⁻ result, (result.2 : ENNReal) +
        ∫⁻ future, (future.2 : ENNReal) ∂next result.1 ∂first) ≤
      ∫⁻ result, (result.2 : ENNReal) + nextBudget ∂first := by
    apply lintegral_mono_ae
    filter_upwards [hnextCost] with result hresult
    simpa using add_le_add_left hresult (result.2 : ENNReal)
  apply hpoint.trans
  rw [lintegral_add_left (by fun_prop)]
  simp only [lintegral_const]
  exact add_le_add hfirstCost
    (mul_le_of_le_one_right (by positivity) hfirstMass)

/-- A deterministic state update contributes its fixed charge before an
adaptive charged continuation. -/
theorem costedBind_charge_dirac_expected_cost_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (x : α) (charge : Nat) (next : α → Measure (β × Nat))
    (hnextMeas : Measurable next)
    (hnextMass : ∀ y, (next y) Set.univ ≤ 1) :
    (∫⁻ result, (result.2 : ENNReal) ∂
      costedBind (costedCharge (Measure.dirac x) charge) next) ≤
      charge + ∫⁻ result, (result.2 : ENNReal) ∂next x := by
  apply (costedBind_lintegral_cost_le _ next hnextMeas hnextMass).trans
  unfold costedCharge
  apply (lintegral_map_le _ (by fun_prop)).trans
  simp only [lintegral_dirac]
  exact le_rfl

/-- A fixed charge followed by a mapped oracle result can be bounded using
only a pointwise continuation budget and the oracle's total mass. -/
theorem costedCharge_map_continuation_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (law : Measure α) (clip : α → β) (hclip : AEMeasurable clip law)
    (charge : Nat)
    (continuationCost : β → ENNReal) (hlaw : law Set.univ ≤ 1)
    {budget : ENNReal} (hbudget : ∀ x, continuationCost (clip x) ≤ budget) :
    (∫⁻ result, (result.2 : ENNReal) + continuationCost result.1 ∂
      costedCharge (law.map clip) charge) ≤ charge + budget := by
  unfold costedCharge
  apply (lintegral_map_le _ (by fun_prop)).trans
  apply (lintegral_map_le _ hclip).trans
  apply (lintegral_mono (fun x => add_le_add_right (hbudget x) _)).trans
  simp only [lintegral_const]
  exact mul_le_of_le_one_right (by positivity) hlaw

/-- An almost-sure state invariant propagates through a charged bind. The
writer addition changes only the cost coordinate. -/
theorem costedBind_ae_state_of_ae {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) (next : α → Measure (β × Nat))
    (hnextMeas : Measurable next)
    (Good : α → Prop) (Goal : β → Prop)
    (hGoal : MeasurableSet {y | Goal y})
    (hfirst : ∀ᵐ result ∂first, Good result.1)
    (hnext : ∀ x, Good x → ∀ᵐ future ∂next x, Goal future.1) :
    ∀ᵐ result ∂costedBind first next, Goal result.1 := by
  let bad : Set (β × Nat) := {result | ¬ Goal result.1}
  have hbad : MeasurableSet bad :=
    (hGoal.preimage measurable_fst).compl
  rw [ae_iff]
  change (costedBind first next) bad = 0
  let continuation : (α × Nat) → Measure (β × Nat) := fun result =>
    (next result.1).map fun future =>
      (future.1, result.2 + future.2)
  have hpoint : ∀ᵐ result ∂first, continuation result bad = 0 := by
    filter_upwards [hfirst] with result hgood
    have hfuture := hnext result.1 hgood
    rw [ae_iff] at hfuture
    unfold continuation
    rw [Measure.map_apply (by fun_prop) hbad]
    simpa only [bad, Set.preimage_ofPred_eq] using hfuture
  unfold costedBind
  apply le_antisymm
  · calc
    (first.bind continuation) bad ≤ ∫⁻ result, continuation result bad ∂first :=
      Measure.bind_apply_le
        (measurable_costedContinuation next hnextMeas).aemeasurable hbad
    _ = 0 := by
      rw [lintegral_congr_ae hpoint]
      simp
  · exact bot_le

theorem costedCharge_dirac_ae_state {α : Type*}
    [MeasurableSpace α] (x : α) (charge : Nat)
    (Goal : α → Prop) (hGoal : MeasurableSet {y | Goal y})
    (hx : Goal x) :
    ∀ᵐ result ∂costedCharge (Measure.dirac x) charge, Goal result.1 := by
  have hset : MeasurableSet {result : α × Nat | Goal result.1} :=
    hGoal.preimage measurable_fst
  have hmap : Measurable (fun y : α => (y, charge)) := by fun_prop
  unfold costedCharge
  rw [ae_map_iff hmap.aemeasurable hset]
  exact (ae_dirac_iff hGoal).2 hx

theorem costedBind_ae_state_of_forall {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) (next : α → Measure (β × Nat))
    (hnextMeas : Measurable next)
    (Goal : β → Prop) (hGoal : MeasurableSet {y | Goal y})
    (hnext : ∀ x, ∀ᵐ future ∂next x, Goal future.1) :
    ∀ᵐ result ∂costedBind first next, Goal result.1 := by
  apply costedBind_ae_state_of_ae first next hnextMeas (fun _ => True) Goal hGoal
  · exact Filter.Eventually.of_forall (fun _ => trivial)
  · intro x _
    exact hnext x

end Kr25Ssmxt
