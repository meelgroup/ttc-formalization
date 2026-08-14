// Lean compiler output
// Module: Ttc.Exec.CVGaussianGuardedExpectedVolume
// Imports: public import Init public meta import Init public import Ttc.Exec.CVGuardedGeneralizedPublic public import Ttc.Exec.CVGaussianCappedExpectedVolume public import Ttc.Exec.CVGaussianAdaptiveIndependentOperational public import Ttc.Exec.CVGaussianWarmFallbackScoreMoment
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
lean_object* initialize_ttc_Ttc_Exec_CVGuardedGeneralizedPublic(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVGaussianCappedExpectedVolume(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVGaussianAdaptiveIndependentOperational(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVGaussianWarmFallbackScoreMoment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVGaussianGuardedExpectedVolume(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGuardedGeneralizedPublic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGaussianCappedExpectedVolume(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGaussianAdaptiveIndependentOperational(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGaussianWarmFallbackScoreMoment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
