// Lean compiler output
// Module: Ttc.Exec.CVFiniteAugmentedSeedOperational
// Imports: public import Init public meta import Init public import Ttc.Exec.CVGaussianScoreSeedPhaseKernel public import Ttc.Exec.CVScoreSeedPhaseKernel public import Ttc.Exec.CVGaussianAugmentedSelectiveTV public import Ttc.Exec.CVFiniteContinuingPhaseDistributional public import Ttc.Volume.CVDirectSequentialWarm
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
lean_object* initialize_ttc_Ttc_Exec_CVGaussianScoreSeedPhaseKernel(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVScoreSeedPhaseKernel(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVGaussianAugmentedSelectiveTV(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVFiniteContinuingPhaseDistributional(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_CVDirectSequentialWarm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVFiniteAugmentedSeedOperational(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGaussianScoreSeedPhaseKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVScoreSeedPhaseKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGaussianAugmentedSelectiveTV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVFiniteContinuingPhaseDistributional(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_CVDirectSequentialWarm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
