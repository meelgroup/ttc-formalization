// Lean compiler output
// Module: Arlib.Probability.UniformOn
// Imports: public import Init public meta import Init public import Arlib.Probability.Rejection public import Arlib.Probability.TV public import Mathlib.MeasureTheory.Integral.Bochner.Set public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic public import Mathlib.MeasureTheory.Measure.WithDensity
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
lean_object* initialize_ttc_Arlib_Probability_Rejection(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_TV(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_Bochner_Set(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_WithDensity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Probability_UniformOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_Rejection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_TV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_Bochner_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_WithDensity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
