/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.Conductance
import Arlib.MarkovChains.Continuous.Warmness
import Arlib.MarkovChains.Continuous.MixingFromConductance
import Arlib.MarkovChains.Continuous.BallWalk
import Arlib.MarkovChains.Continuous.MetropolisGaussian
import Arlib.MarkovChains.Continuous.MetropolisConductance
import Arlib.MarkovChains.Continuous.HitAndRun
import Arlib.MarkovChains.Continuous.SphereCoord
import Arlib.MarkovChains.Continuous.HitAndRunOverlap
import Arlib.MarkovChains.Continuous.HitAndRunConductance
import Arlib.MarkovChains.Continuous.Cheeger
import Arlib.MarkovChains.Continuous.PointwiseMixing
import Arlib.MarkovChains.Continuous.PointwiseRoute
import Arlib.MarkovChains.Continuous.L2Mixing
import Arlib.MarkovChains.Continuous.BallWalkConductance
import Arlib.MarkovChains.Continuous.SpeedyWalk
import Arlib.MarkovChains.Continuous.SpeedyConductanceSharp
import Arlib.MarkovChains.Continuous.SpeedyToUniform
import Arlib.MarkovChains.Continuous.TVWitness
import Arlib.MarkovChains.Continuous.HoldingTime
import Arlib.MarkovChains.Continuous.TrajTransfer
import Arlib.MarkovChains.Continuous.UnitBallMixing
import Arlib.MarkovChains.Continuous.ConvexBodyMixing
import Arlib.MarkovChains.Continuous.WarmStart
import Arlib.MarkovChains.Continuous.WarmStartGeneral
import Arlib.MarkovChains.Continuous.NonStationary
import Arlib.MarkovChains.Continuous.SpeedyOverlap
import Arlib.MarkovChains.Continuous.StarPolar
import Arlib.MarkovChains.Continuous.HitAndRunMixing
import Arlib.MarkovChains.Continuous.ConductanceToTV
import Arlib.MarkovChains.Continuous.MetropolisConductanceSharp
import Arlib.MarkovChains.Continuous.LensHalfspace
import Arlib.MarkovChains.Continuous.LensMin
import Arlib.MarkovChains.Continuous.OverlapSqrt
import Arlib.MarkovChains.Continuous.DeltaCap
import Arlib.MarkovChains.Continuous.LensSharp
import Arlib.MarkovChains.Continuous.MetropolisOverlapSqrt
import Arlib.MarkovChains.Continuous.MixingSqrt
import Arlib.MarkovChains.Continuous.MetropolisMixing
import Arlib.MarkovChains.Continuous.MetropolisMixingUncond
import Arlib.MarkovChains.Continuous.EllFloor
import Arlib.MarkovChains.Continuous.SpeedyUniformPoly
import Arlib.MarkovChains.Continuous.WarmEllProb
import Arlib.MarkovChains.Continuous.SpeedyConductanceSqrt
import Arlib.MarkovChains.Continuous.UniformSamplerUncond
import Arlib.MarkovChains.Continuous.SmoothSqrt
import Arlib.MarkovChains.Continuous.SpeedyAffine
import Arlib.MarkovChains.Continuous.BallWalkTransfer
import Arlib.MarkovChains.Continuous.UniformSamplerSharp
import Arlib.MarkovChains.Continuous.SpeedyGaussian
import Arlib.MarkovChains.Continuous.HitAndRunConductanceParam
import Arlib.MarkovChains.Continuous.StepSizeFunction
import Arlib.MarkovChains.Continuous.SphereCap
import Arlib.MarkovChains.Continuous.SpeedyGaussianConductance
import Arlib.MarkovChains.Continuous.HitAndRunUncond
import Arlib.MarkovChains.Continuous.HitAndRunLem41Discharge
import Arlib.MarkovChains.Continuous.HitAndRunMixingUncond
import Arlib.MarkovChains.Continuous.OverlapPerPair
import Arlib.MarkovChains.Continuous.SpeedyToGaussian
import Arlib.MarkovChains.Continuous.LambdaBoundGaussian
import Arlib.MarkovChains.Continuous.SpeedyRejection
import Arlib.MarkovChains.Continuous.LambdaBoundSharp
import Arlib.MarkovChains.Continuous.KLS97Shell
import Arlib.MarkovChains.Continuous.SpeedyExactOnShrunken
import Arlib.MarkovChains.Continuous.WastedSteps
import Arlib.MarkovChains.Continuous.MapSpeedyToTarget
import Arlib.MarkovChains.Continuous.LovaszSmoothing
import Arlib.MarkovChains.Continuous.LovaszSmoothingSharp
import Arlib.MarkovChains.Continuous.LambdaFromShrunken
import Arlib.MarkovChains.Continuous.SamplerStepCount
import Arlib.MarkovChains.Continuous.ColdPhaseRegime

/-!
# Arlib.MarkovChains

Area root. Modules are wired in here as they land; see `Arlib.lean` for the
staging rules.
-/
