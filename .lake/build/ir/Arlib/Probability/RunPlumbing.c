// Lean compiler output
// Module: Arlib.Probability.RunPlumbing
// Imports: public import Init public meta import Init public import Mathlib.Probability.Independence.Basic public import Mathlib.MeasureTheory.Constructions.Pi public import Mathlib.MeasureTheory.Order.Lattice public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic public import Mathlib.Probability.Independence.InfinitePi public import Arlib.Convexity.GaussianCooling.Estimator
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
lean_object* initialize_mathlib_Mathlib_Probability_Independence_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Constructions_Pi(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Order_Lattice(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Function_LpSeminorm_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_Independence_InfinitePi(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_Estimator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Probability_RunPlumbing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_Independence_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Constructions_Pi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Order_Lattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Function_LpSeminorm_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_Independence_InfinitePi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_Estimator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
