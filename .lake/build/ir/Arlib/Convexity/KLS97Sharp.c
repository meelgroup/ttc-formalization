// Lean compiler output
// Module: Arlib.Convexity.KLS97Sharp
// Imports: public import Init public meta import Init public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace public import Mathlib.MeasureTheory.Measure.Prod public import Mathlib.Analysis.Convex.Basic public import Mathlib.Analysis.Convex.Measure public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal public import Mathlib.MeasureTheory.Integral.IntegralEqImproper public import Mathlib.MeasureTheory.Integral.ExpDecay public import Mathlib.Analysis.Complex.ExponentialBounds
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
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_EqHaar(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_InnerProductSpace(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Prod(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Convex_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Convex_Measure(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Projection_Minimal(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_IntegralEqImproper(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_ExpDecay(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_ExponentialBounds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_KLS97Sharp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_EqHaar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_InnerProductSpace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Convex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Convex_Measure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Projection_Minimal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_IntegralEqImproper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_ExpDecay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_ExponentialBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
