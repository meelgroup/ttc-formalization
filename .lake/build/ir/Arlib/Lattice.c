// Lean compiler output
// Module: Arlib.Lattice
// Imports: public import Init public meta import Init public import Arlib.Lattice.Basic public import Arlib.Lattice.Rounding.Tent public import Arlib.Lattice.Rounding.RoundLaw public import Arlib.Lattice.Rounding.ProdKernel public import Arlib.Lattice.Rounding.KernelIntegral public import Arlib.Lattice.KV97.Defs public import Arlib.Lattice.KV97.Inflate public import Arlib.Lattice.KV97.InflateGeom public import Arlib.Lattice.KV97.Escape public import Arlib.Lattice.KV97.Theorem2 public import Arlib.Lattice.KV97.Corollary public import Arlib.Lattice.KV97.Lemma1 public import Arlib.Lattice.Rounding.ContTent public import Arlib.Lattice.Rounding.Coins
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
lean_object* initialize_ttc_Arlib_Lattice_Basic(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_Rounding_Tent(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_Rounding_RoundLaw(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_Rounding_ProdKernel(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_Rounding_KernelIntegral(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_Defs(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_Inflate(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_InflateGeom(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_Escape(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_Theorem2(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_Corollary(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_Lemma1(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_Rounding_ContTent(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_Rounding_Coins(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Lattice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Rounding_Tent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Rounding_RoundLaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Rounding_ProdKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Rounding_KernelIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_Inflate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_InflateGeom(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_Escape(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_Theorem2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_Corollary(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_Lemma1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Rounding_ContTent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Rounding_Coins(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
