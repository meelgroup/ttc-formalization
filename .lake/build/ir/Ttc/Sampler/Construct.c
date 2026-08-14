// Lean compiler output
// Module: Ttc.Sampler.Construct
// Imports: public import Init public meta import Init public import Ttc.TtcProb public import Arlib.MarkovChains.Continuous.ConvexBodyMixing public import Arlib.MarkovChains.Continuous.WarmStart public import Arlib.MarkovChains.Continuous.WarmStartGeneral public import Arlib.Lattice.KV97.InflateGeom public import Arlib.Lattice.Rounding.ProdKernel
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
lean_object* initialize_ttc_Ttc_TtcProb(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_ConvexBodyMixing(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_WarmStart(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_WarmStartGeneral(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_InflateGeom(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_Rounding_ProdKernel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Sampler_Construct(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_TtcProb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_ConvexBodyMixing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_WarmStart(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_WarmStartGeneral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_InflateGeom(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Rounding_ProdKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
