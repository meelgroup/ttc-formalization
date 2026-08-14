// Lean compiler output
// Module: Arlib.Convexity.KLS97Lemma38
// Imports: public import Init public meta import Init public import Mathlib.Analysis.Real.Pi.Bounds public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral public import Mathlib.MeasureTheory.Group.Integral public import Arlib.Convexity.OneDimIsoperimetry public import Arlib.Convexity.NeedleProfile
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
lean_object* initialize_mathlib_Mathlib_Analysis_Real_Pi_Bounds(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Gaussian_GaussianIntegral(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Group_Integral(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_OneDimIsoperimetry(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_NeedleProfile(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_KLS97Lemma38(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Real_Pi_Bounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Gaussian_GaussianIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Group_Integral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_OneDimIsoperimetry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_NeedleProfile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
