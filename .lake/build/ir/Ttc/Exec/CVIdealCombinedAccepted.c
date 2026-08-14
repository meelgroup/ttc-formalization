// Lean compiler output
// Module: Ttc.Exec.CVIdealCombinedAccepted
// Imports: public import Init public meta import Init public import Ttc.Exec.CVGaussianAcceptedWarm public import Ttc.Exec.CostedAdaptiveTerminalWarmQ public import Arlib.Convexity.GaussianCooling.ScaledRawWarm public import Arlib.MarkovChains.Continuous.SpeedyAffine
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVGaussianAcceptedWarm(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CostedAdaptiveTerminalWarmQ(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_ScaledRawWarm(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_SpeedyAffine(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVIdealCombinedAccepted(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGaussianAcceptedWarm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CostedAdaptiveTerminalWarmQ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_ScaledRawWarm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_SpeedyAffine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
