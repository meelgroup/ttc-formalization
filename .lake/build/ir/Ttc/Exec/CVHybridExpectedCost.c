// Lean compiler output
// Module: Ttc.Exec.CVHybridExpectedCost
// Imports: public import Init public meta import Init public import Ttc.Exec.CostedBackend public import Ttc.Exec.VolumePriceCV public import Ttc.Exec.CoolDrawPrice public import Ttc.Exec.PolyRun public import Ttc.Volume.CVHybridVolumeAlgorithm public import Ttc.Volume.CVOperationalRuntime
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
lean_object* initialize_ttc_Ttc_Exec_CostedBackend(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_VolumePriceCV(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CoolDrawPrice(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_PolyRun(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_CVHybridVolumeAlgorithm(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_CVOperationalRuntime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVHybridExpectedCost(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CostedBackend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_VolumePriceCV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CoolDrawPrice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_PolyRun(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_CVHybridVolumeAlgorithm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_CVOperationalRuntime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
