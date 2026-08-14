// Lean compiler output
// Module: Arlib.MarkovChains.Continuous.MixingSqrt
// Imports: public import Init public meta import Init public import Arlib.MarkovChains.Continuous.ConductanceToTV public import Arlib.MarkovChains.Continuous.DeltaCap
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
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_ConductanceToTV(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_DeltaCap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_MixingSqrt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_ConductanceToTV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_DeltaCap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
