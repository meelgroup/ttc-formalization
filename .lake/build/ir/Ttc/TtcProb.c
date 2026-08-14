// Lean compiler output
// Module: Ttc.TtcProb
// Imports: public import Init public meta import Init public import Ttc.Dnf public import Ttc.Runtime public import Ttc.Coupling.Family public import Ttc.Process.SketchProcess public import Ttc.Lattice.Decomposition public import Ttc.Volume.Oracle public import Ttc.Sampler.Interface public import Arlib.Lattice.KV97.Theorem2 public import Arlib.Probability.TV public import Arlib.Probability.UniformOn
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
lean_object* initialize_ttc_Ttc_Dnf(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Runtime(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Coupling_Family(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Process_SketchProcess(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Lattice_Decomposition(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_Oracle(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Sampler_Interface(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_Theorem2(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_TV(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_UniformOn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_TtcProb(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Dnf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Coupling_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Process_SketchProcess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Lattice_Decomposition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_Oracle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Sampler_Interface(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_Theorem2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_TV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_UniformOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
