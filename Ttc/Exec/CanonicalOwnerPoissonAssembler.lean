import Ttc.Exec.CostedMarkedPoissonTrajectory
import Mathlib.Probability.Independence.InfinitePi

/-!
# Canonical-owner assembly of independently marked Poisson streams

This file contains the measure-theoretic core needed by TTC's per-cube sampling
implementation.  Each cube owns an independent marked Poisson stream.  A global
fine-grid point reads exactly the cell belonging to its canonical owner; all
other marked cells (including the explicit drop cell) are ignored.
-/

namespace Ttc.CanonicalOwnerPoissonAssembler

open MeasureTheory ProbabilityTheory
open Ttc.CostedMarkedPoisson
open Ttc.CostedMarkedPoissonIdentified
open Ttc.CostedMarkedPoissonTrajectory
open Ttc.CostedInitialThinningTrajectory
open Ttc.SequentialCostedPathLumping
open scoped ENNReal BigOperators Classical NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Restricting an independent finite product to an injectively selected family
of coordinates again gives the corresponding product measure. -/
theorem map_pi_coordinateInjection
    (mu : I → Measure Nat) [∀ i, IsProbabilityMeasure (mu i)]
    (ownerCell : J → I) (hinj : Function.Injective ownerCell) :
    Measure.map (fun x j => x (ownerCell j)) (Measure.pi mu) =
      Measure.pi (fun j => mu (ownerCell j)) := by
  have hIndep : iIndepFun (fun i (x : I → Nat) => x i) (Measure.pi mu) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hsub : iIndepFun (fun j (x : I → Nat) => x (ownerCell j)) (Measure.pi mu) :=
    hIndep.precomp hinj
  rw [hsub.map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)]
  congr 1
  funext j
  exact (measurePreserving_eval mu (ownerCell j)).map_eq

/-- A finite product of finite products is the product indexed by pairs after
uncurrying the sample. -/
theorem map_pi_pi_uncurry
    {A : Type*} [Fintype A]
    (mu : I → A → Measure Nat) [∀ i a, IsProbabilityMeasure (mu i a)] :
    Measure.map (fun x (p : I × A) => x p.1 p.2)
        (Measure.pi fun i => Measure.pi (mu i)) =
      Measure.pi (fun p : I × A => mu p.1 p.2) := by
  have hnested : (Measure.pi fun i => Measure.pi (mu i)) =
      Measure.infinitePi (fun i => Measure.infinitePi (mu i)) := by
    rw [Measure.infinitePi_eq_pi]
    congr 1
    funext i
    rw [Measure.infinitePi_eq_pi]
  rw [hnested]
  change Measure.map Function.uncurry
      (Measure.infinitePi fun i => Measure.infinitePi (mu i)) = _
  have h := Measure.infinitePi_map_curry_symm mu
  simpa only [MeasurableEquiv.coe_curry_symm, Function.uncurry,
    Measure.infinitePi_eq_pi] using h

#print axioms map_pi_coordinateInjection
#print axioms map_pi_pi_uncurry

variable {L : Nat}

/-- Independently executable marked-Poisson data for every cube.  The extra
`Fin.last L` mark is the explicit drop category. -/
structure CubeMarkedFamily (I : Type*) [Fintype I] (L : Nat) where
  q : I → Fin (L + 1) → Real
  lam : I → Real
  lam_nonneg : ∀ i, 0 ≤ lam i
  q_nonneg : ∀ i a, 0 ≤ q i a
  q_sum : ∀ i, ∑ a, q i a = 1
  sampler : ∀ i, ExpectedQueryFiniteSampler (q i)

/-- Build the per-cube finite marked samplers directly from genuine costed fine
endpoint samplers.  `encode` may send every non-owner endpoint to `Fin.last L`;
the required pushforward identity is the exact finite categorical law. -/
noncomputable def CubeMarkedFamily.ofFine
    {n : Nat}
    (target : I → Measure (Ttc.Space n))
    (fine : ∀ i, Ttc.KV97RoundedEndpointBridge.ExpectedQueryFineSampler (target i))
    (encode : I → Ttc.Space n → Fin (L + 1))
    (q : I → Fin (L + 1) → Real)
    (hencodeMeas : ∀ i, Measurable (encode i))
    (hencoded : ∀ i, Measure.map (encode i) (target i) = categoricalLaw (q i))
    (lam : I → Real) (hlam : ∀ i, 0 ≤ lam i)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1) :
    CubeMarkedFamily I L where
  q := q
  lam := lam
  lam_nonneg := hlam
  q_nonneg := hq0
  q_sum := hqsum
  sampler := fun i => finiteSamplerOfFine (fine i) (encode i) (q i)
    (hencodeMeas i) (hencoded i)

@[simp] theorem CubeMarkedFamily.ofFine_sampler_expectedQueries
    {n : Nat}
    (target : I → Measure (Ttc.Space n))
    (fine : ∀ i, Ttc.KV97RoundedEndpointBridge.ExpectedQueryFineSampler (target i))
    (encode : I → Ttc.Space n → Fin (L + 1))
    (q : I → Fin (L + 1) → Real)
    (hencodeMeas : ∀ i, Measurable (encode i))
    (hencoded : ∀ i, Measure.map (encode i) (target i) = categoricalLaw (q i))
    (lam : I → Real) (hlam : ∀ i, 0 ≤ lam i)
    (hq0 : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1)
    (i : I) :
    ((CubeMarkedFamily.ofFine target fine encode q hencodeMeas hencoded
      lam hlam hq0 hqsum).sampler i).expectedQueries =
      (fine i).expectedQueries := rfl

namespace CubeMarkedFamily

variable (F : CubeMarkedFamily I L)

/-- The independent product of the actual costed cube streams. -/
noncomputable def jointLaw :
    Measure (I → ENNReal × (Fin (L + 1) → Nat)) :=
  Measure.pi fun i => levelZeroLaw (F.sampler i) (F.lam i)

instance : IsProbabilityMeasure F.jointLaw := by
  unfold jointLaw
  infer_instance

/-- Forget costs and expose every cube/mark count. -/
def allCellCounts
    (z : I → ENNReal × (Fin (L + 1) → Nat)) : I × Fin (L + 1) → Nat :=
  fun p => (z p.1).2 p.2

theorem measurable_allCellCounts : Measurable
    (fun z : I → ENNReal × (Fin (L + 1) → Nat) =>
      fun p : I × Fin (L + 1) => (z p.1).2 p.2) := by
  fun_prop

/-- Every cube/mark cell is an independent Poisson random variable with the
source-faithful intensity `lam i * q i a`. -/
theorem map_allCellCounts_jointLaw :
    Measure.map allCellCounts F.jointLaw =
      Measure.pi (fun p : I × Fin (L + 1) =>
        poissonMeasure (F.lam p.1 * F.q p.1 p.2).toNNReal) := by
  let countVector := fun z : I → ENNReal × (Fin (L + 1) → Nat) =>
    fun i => (z i).2
  have hcount : Measure.map countVector F.jointLaw =
      Measure.pi (fun i => Ttc.countLaw (F.lam i) (F.q i)) := by
    letI (i : I) : IsProbabilityMeasure
        (Measure.map (fun z : ENNReal × (Fin (L + 1) → Nat) => z.2)
          (levelZeroLaw (F.sampler i) (F.lam i))) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    unfold jointLaw
    rw [Measure.pi_map_pi
      (f := fun _ => fun z : ENNReal × (Fin (L + 1) → Nat) => z.2)
      (fun _ => measurable_snd.aemeasurable)]
    congr 1
    funext i
    exact map_snd_levelZeroLaw_eq_countLaw
      (F.lam_nonneg i) (F.q_nonneg i) (F.q_sum i) (F.sampler i)
  have hcell : (Measure.pi fun i => Ttc.countLaw (F.lam i) (F.q i)) =
      Measure.pi (fun i => Measure.pi fun a : Fin (L + 1) =>
        poissonMeasure (F.lam i * F.q i a).toNNReal) := by
    congr 1
    funext i
    exact Ttc.countLaw_eq_pi (F.lam_nonneg i) (F.q_nonneg i) (F.q_sum i)
  let uncurryCounts := fun x : I → Fin (L + 1) → Nat =>
    fun p : I × Fin (L + 1) => x p.1 p.2
  calc
    Measure.map allCellCounts F.jointLaw =
        Measure.map uncurryCounts (Measure.map countVector F.jointLaw) := by
          rw [Measure.map_map]
          · rfl
          · fun_prop
          · fun_prop
    _ = Measure.map uncurryCounts
        (Measure.pi fun i => Ttc.countLaw (F.lam i) (F.q i)) := by rw [hcount]
    _ = Measure.map uncurryCounts
        (Measure.pi fun i => Measure.pi fun a : Fin (L + 1) =>
          poissonMeasure (F.lam i * F.q i a).toNNReal) := by rw [hcell]
    _ = Measure.pi (fun p : I × Fin (L + 1) =>
        poissonMeasure (F.lam p.1 * F.q p.1 p.2).toNNReal) := by
          exact map_pi_pi_uncurry
            (fun i a => poissonMeasure (F.lam i * F.q i a).toNNReal)

/-- Read the retained cell of a global endpoint from its canonical owner's
stream.  Every non-owner occurrence and `Fin.last L` is thereby dropped. -/
def retainedCounts (owner : Fin L → I)
    (z : I → ENNReal × (Fin (L + 1) → Nat)) : Fin L → Nat :=
  fun s => (z (owner s)).2 s.castSucc

theorem measurable_retainedCounts (owner : Fin L → I) :
    Measurable (retainedCounts owner) := by
  change Measurable (fun z : I → ENNReal × (Fin (L + 1) → Nat) =>
    fun s : Fin L => (z (owner s)).2 s.castSucc)
  fun_prop

theorem ownerCell_injective (owner : Fin L → I) :
    Function.Injective (fun s : Fin L => (owner s, s.castSucc)) := by
  intro s t h
  exact Fin.castSucc_injective L (congrArg Prod.snd h)

/-- Canonical-owner projection: the retained global counts are independent
Poissons, and cell `s` has only its owner's contribution. -/
theorem map_retainedCounts_jointLaw (owner : Fin L → I) :
    Measure.map (retainedCounts owner) F.jointLaw =
      Measure.pi (fun s : Fin L => poissonMeasure
        (F.lam (owner s) * F.q (owner s) s.castSucc).toNNReal) := by
  let select := fun x : I × Fin (L + 1) → Nat =>
    fun s : Fin L => x (owner s, s.castSucc)
  calc
    Measure.map (retainedCounts owner) F.jointLaw =
        Measure.map select (Measure.map allCellCounts F.jointLaw) := by
          rw [Measure.map_map]
          · rfl
          · change Measurable (fun x : I × Fin (L + 1) → Nat =>
              fun s : Fin L => x (owner s, s.castSucc))
            fun_prop
          · exact measurable_allCellCounts (I := I) (L := L)
    _ = Measure.map select (Measure.pi (fun p : I × Fin (L + 1) =>
        poissonMeasure (F.lam p.1 * F.q p.1 p.2).toNNReal)) := by
          rw [F.map_allCellCounts_jointLaw]
    _ = Measure.pi (fun s : Fin L => poissonMeasure
        (F.lam (owner s) * F.q (owner s) s.castSucc).toNNReal) := by
          exact map_pi_coordinateInjection
            (fun p : I × Fin (L + 1) =>
              poissonMeasure (F.lam p.1 * F.q p.1 p.2).toNNReal)
            (fun s : Fin L => (owner s, s.castSucc)) (ownerCell_injective owner)

/-- Sum of the actual recorded query counts of all independent cube streams. -/
noncomputable def totalQueryCost (z : I → ENNReal × (Fin (L + 1) → Nat)) : ENNReal :=
  ∑ i, (z i).1

theorem measurable_totalQueryCost : Measurable (@totalQueryCost I _ L) := by
  change Measurable (fun z : I → ENNReal × (Fin (L + 1) → Nat) =>
    ∑ i, (z i).1)
  fun_prop

/-- Costed TTC level zero after dropping non-owner marks and summing the costs
of the independently run cube samplers. -/
noncomputable def assembledLevelZeroLaw (owner : Fin L → I) :
    Measure (ENNReal × (Fin L → Nat)) :=
  Measure.map (fun z => (totalQueryCost z, retainedCounts owner z)) F.jointLaw

instance (owner : Fin L → I) :
    IsProbabilityMeasure (F.assembledLevelZeroLaw owner) := by
  unfold assembledLevelZeroLaw
  exact Measure.isProbabilityMeasure_map
    ((measurable_totalQueryCost (I := I) (L := L)).prodMk
      (measurable_retainedCounts owner)).aemeasurable

theorem map_snd_assembledLevelZeroLaw (owner : Fin L → I) :
    Measure.map Prod.snd (F.assembledLevelZeroLaw owner) =
      Measure.pi (fun s : Fin L => poissonMeasure
        (F.lam (owner s) * F.q (owner s) s.castSucc).toNNReal) := by
  unfold assembledLevelZeroLaw
  rw [Measure.map_map]
  · exact F.map_retainedCounts_jointLaw owner
  · exact measurable_snd
  · exact (measurable_totalQueryCost (I := I) (L := L)).prodMk
      (measurable_retainedCounts owner)

/-- Exact source-faithful expected query cost: `sum_i lambda_i * B_i`.
Dropped marks still cost one sampler call, but cause no retry and no
renormalization. -/
theorem lintegral_fst_assembledLevelZeroLaw (owner : Fin L → I) :
    (∫⁻ z, z.1 ∂F.assembledLevelZeroLaw owner) =
      ∑ i, ((F.lam i).toNNReal : ENNReal) * (F.sampler i).expectedQueries := by
  have hone (i : I) :
      (∫⁻ z, (z i).1 ∂F.jointLaw) =
        ((F.lam i).toNNReal : ENNReal) * (F.sampler i).expectedQueries := by
    unfold jointLaw
    rw [← MeasureTheory.lintegral_map measurable_fst (measurable_pi_apply i)]
    rw [(measurePreserving_eval
      (fun i => levelZeroLaw (F.sampler i) (F.lam i)) i).map_eq]
    exact lintegral_fst_levelZeroLaw (F.sampler i) (F.lam i)
  unfold assembledLevelZeroLaw
  rw [MeasureTheory.lintegral_map measurable_fst
    ((measurable_totalQueryCost (I := I) (L := L)).prodMk
      (measurable_retainedCounts owner))]
  change (∫⁻ z, ∑ i, (z i).1 ∂F.jointLaw) = _
  rw [MeasureTheory.lintegral_finsetSum Finset.univ]
  · exact Finset.sum_congr rfl fun i _ => hone i
  · intro i _
    fun_prop

/-- The costed TTC trajectory driven by all cube streams at level zero. -/
noncomputable def assembledTrajectoryLaw (owner : Fin L → I) :
    Measure (Nat → ENNReal × (Fin L → Nat)) :=
  costedTrajLaw (F.assembledLevelZeroLaw owner)

instance (owner : Fin L → I) :
    IsProbabilityMeasure (F.assembledTrajectoryLaw owner) := by
  unfold assembledTrajectoryLaw
  infer_instance

/-- Erasing recorded costs gives the exact TTC trajectory at canonical-owner
rates, with no assignment-cell rejection or normalization. -/
theorem map_forgetCost_assembledTrajectoryLaw (owner : Fin L → I) :
    Measure.map (pathMap Prod.snd) (F.assembledTrajectoryLaw owner) =
      Ttc.trajLaw (fun s : Fin L => F.lam (owner s) * F.q (owner s) s.castSucc) := by
  unfold assembledTrajectoryLaw
  apply map_forgetCost_costedTrajLaw_eq_trajLaw
  exact F.map_snd_assembledLevelZeroLaw owner

/-- Every nonempty TTC prefix has exactly the sum of the independent cube
stream means; later thinning costs no membership queries. -/
theorem lintegral_finitePrefixQueryCost_assembledTrajectoryLaw
    (owner : Fin L → I) {J : Nat} (hJ : 0 < J) :
    (∫⁻ omega, finitePrefixQueryCost J omega
        ∂F.assembledTrajectoryLaw owner) =
      ∑ i, ((F.lam i).toNNReal : ENNReal) * (F.sampler i).expectedQueries := by
  unfold assembledTrajectoryLaw
  calc
    (∫⁻ omega, finitePrefixQueryCost J omega
        ∂costedTrajLaw (F.assembledLevelZeroLaw owner)) =
        ∫⁻ z, z.1 ∂F.assembledLevelZeroLaw owner :=
      lintegral_finitePrefixQueryCost_eq_initialMean _ hJ
    _ = _ := F.lintegral_fst_assembledLevelZeroLaw owner

#print axioms map_allCellCounts_jointLaw
#print axioms map_retainedCounts_jointLaw
#print axioms lintegral_fst_assembledLevelZeroLaw
#print axioms map_forgetCost_assembledTrajectoryLaw
#print axioms lintegral_finitePrefixQueryCost_assembledTrajectoryLaw

end CubeMarkedFamily

end Ttc.CanonicalOwnerPoissonAssembler
