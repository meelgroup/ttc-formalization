// Lean compiler output
// Module: Arlib.Convexity.GaussianCooling.Variance
// Imports: public import Init public meta import Init public import Mathlib.MeasureTheory.Integral.Bochner.Basic public import Mathlib.MeasureTheory.Integral.Prod public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral public import Mathlib.Analysis.Calculus.Deriv.Pow public import Mathlib.Analysis.Calculus.Deriv.Inv public import Mathlib.Analysis.Calculus.MeanValue public import Mathlib.Analysis.SpecialFunctions.Exp public import Mathlib.Analysis.SpecialFunctions.ExpDeriv public import Mathlib.Analysis.SpecialFunctions.Log.Basic public import Mathlib.Analysis.SpecialFunctions.Log.Deriv public import Mathlib.Analysis.InnerProductSpace.Basic
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
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_Bochner_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_Prod(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_InnerProductSpace(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_EqHaar(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_FundThmCalculus(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_ParametricIntervalIntegral(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Pow(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Inv(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_MeanValue(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Exp(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_ExpDeriv(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Deriv(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_Variance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_Bochner_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_InnerProductSpace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_EqHaar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_FundThmCalculus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_ParametricIntervalIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_MeanValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Exp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_ExpDeriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Deriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
