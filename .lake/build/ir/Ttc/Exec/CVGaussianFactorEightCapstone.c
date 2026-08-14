// Lean compiler output
// Module: Ttc.Exec.CVGaussianFactorEightCapstone
// Imports: public import Init public meta import Init public import Ttc.Exec.CVGaussianWarmFallbackScoreMoment public import Ttc.Exec.CVGaussianScoreAwareMoment public import Ttc.Exec.CVIndependentStreamMoments public import Ttc.Exec.CVIndependentStreamBiasAccuracy public import Ttc.Exec.CVCorrectedClippingArithmetic
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
lean_object* initialize_ttc_Ttc_Exec_CVGaussianWarmFallbackScoreMoment(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVGaussianScoreAwareMoment(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVIndependentStreamMoments(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVIndependentStreamBiasAccuracy(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVCorrectedClippingArithmetic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVGaussianFactorEightCapstone(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGaussianWarmFallbackScoreMoment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGaussianScoreAwareMoment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVIndependentStreamMoments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVIndependentStreamBiasAccuracy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVCorrectedClippingArithmetic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
