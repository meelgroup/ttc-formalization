// Lean compiler output
// Module: Ttc.Exec.PolyRun
// Imports: public import Init public meta import Init public import Ttc.Exec.CVBackend public import Ttc.Exec.PolyComplexity public import Ttc.Exec.SamplerCost public import Ttc.Exec.CoolDrawPrice public import Ttc.Sampler.ConstructHitAndRun public import Ttc.Monadic.Program
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
lean_object* initialize_ttc_Ttc_Exec_CVBackend(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_PolyComplexity(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_SamplerCost(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CoolDrawPrice(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Sampler_ConstructHitAndRun(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Monadic_Program(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_PolyRun(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVBackend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_PolyComplexity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_SamplerCost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CoolDrawPrice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Sampler_ConstructHitAndRun(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Monadic_Program(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
