// Lean compiler output
// Module: Arlib.Convexity.GaussianCooling.ZLogconcave
// Imports: public import Init public meta import Init public import Arlib.Convexity.GaussianCooling.Variance public import Arlib.Convexity.Localization public import Mathlib.MeasureTheory.Integral.Pi public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
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
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_Variance(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_Localization(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_Pi(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Gaussian_GaussianIntegral(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_NormedSpace(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_InnerProductSpace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_ZLogconcave(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_Variance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_Localization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_Pi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Gaussian_GaussianIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_NormedSpace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_InnerProductSpace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
