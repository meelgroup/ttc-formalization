// Lean compiler output
// Module: Arlib.Convexity.GaussianCooling.AdaptiveRestartTruncatedFour
// Imports: public import Init public meta import Init public import Arlib.Convexity.GaussianCooling.AdaptiveRestartWarm public import Arlib.Convexity.GaussianCooling.PhaseSamplerTV public import Arlib.MarkovChains.Continuous.RadiusFourGaussian public import Arlib.MarkovChains.Continuous.ColdTruncationRelativeFour
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
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_AdaptiveRestartWarm(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseSamplerTV(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_RadiusFourGaussian(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_ColdTruncationRelativeFour(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_AdaptiveRestartTruncatedFour(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_AdaptiveRestartWarm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseSamplerTV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_RadiusFourGaussian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_ColdTruncationRelativeFour(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
