/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.Theorem
import ttc.Meta.SealTests

/-! # Always-on audit of the sealed interface -/

#ttcModelClosure ttc.Program.estimator
#ttcModelClosure ttc.SealedRun.execution
#ttcModelClosure ttc.SealedRun.estimate
#ttcModelClosure ttc.SealedRun.expectedOperations
#ttcSurplusIn ttc.Model.Program from ttc.Program.estimator
#ttcSurplusIn ttc.Model from ttc.ttc_theorem1_volume_accuracy ttc.ttc_theorem3_expected_runtime
