/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.Polytope
import Arlib.Convexity.LogConcave
import Arlib.Convexity.PrekopaLeindler
import Arlib.Convexity.BrascampLieb1D
import Arlib.Convexity.PrekopaLeindlerN
import Arlib.Convexity.IntervalReduction
import Arlib.Convexity.Isoperimetry
import Arlib.Convexity.Localization
import Arlib.Convexity.LocalizationLemma
import Arlib.Convexity.BrunnSharp
import Arlib.Convexity.KLS97
import Arlib.Convexity.KLS97Sharp
import Arlib.Convexity.OneDimIsoperimetry
import Arlib.Convexity.ConcaveProfileIso
import Arlib.Convexity.SharpIsoperimetry
import Arlib.Convexity.CrossRatio
import Arlib.Convexity.CrossRatioOneDim
import Arlib.Convexity.ChordCompare
import Arlib.Convexity.StepLength
import Arlib.Convexity.HitAndRunStep
import Arlib.Convexity.LocalizationLimit
import Arlib.Convexity.NeedleProfile
import Arlib.Convexity.LocalizationAssembly
import Arlib.Convexity.LocalizationAffine
import Arlib.Convexity.LocalizationTransverse
import Arlib.Convexity.LocalizationClosed
import Arlib.Convexity.NeedleSlab
import Arlib.Convexity.NeedleSlabAffine
import Arlib.Convexity.NeedleSlabChain
import Arlib.Convexity.ConcaveSelection
import Arlib.Convexity.SignedCut
import Arlib.Convexity.DyerFrieze
import Arlib.Convexity.IsoBall
import Arlib.Convexity.NeedleLimit
import Arlib.Convexity.PositionalCut
import Arlib.Convexity.TransverseCut
import Arlib.Convexity.GaussianCooling.Schedule
import Arlib.Convexity.GaussianCooling.Chain
import Arlib.Convexity.GaussianCooling.Estimator
import Arlib.Convexity.GaussianCooling.Variance
import Arlib.Convexity.GaussianCooling.ZLogconcave
import Arlib.Convexity.GaussianCooling.IndicatorVariance
import Arlib.Convexity.GaussianCooling.Unblock
import Arlib.Convexity.GaussianCooling.PhaseMean
import Arlib.Convexity.GaussianCooling.PhaseVar
import Arlib.Convexity.GaussianCooling.PhaseSchedule
import Arlib.Convexity.GaussianCooling.TerminalPhase

/-!
# Arlib.Convexity

Area root. Modules are wired in here as they land; see `Arlib.lean` for the
staging rules.
-/
