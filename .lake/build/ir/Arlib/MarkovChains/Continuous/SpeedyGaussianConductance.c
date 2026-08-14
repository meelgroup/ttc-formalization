// Lean compiler output
// Module: Arlib.MarkovChains.Continuous.SpeedyGaussianConductance
// Imports: public import Init public meta import Init public import Arlib.MarkovChains.Continuous.SpeedyGaussian public import Arlib.MarkovChains.Continuous.OverlapSqrt public import Arlib.MarkovChains.Continuous.MetropolisConductanceSharp public import Arlib.Convexity.IsoWeighted
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
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_SpeedyGaussian(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_OverlapSqrt(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_MetropolisConductanceSharp(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_IsoWeighted(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_SpeedyGaussianConductance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_SpeedyGaussian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_OverlapSqrt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_MetropolisConductanceSharp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_IsoWeighted(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
