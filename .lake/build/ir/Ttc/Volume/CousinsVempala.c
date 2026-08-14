// Lean compiler output
// Module: Ttc.Volume.CousinsVempala
// Imports: public import Init public meta import Init public import Ttc.Volume.Bridge public import Arlib.Convexity.GaussianCooling.Estimator public import Arlib.Convexity.GaussianCooling.ZLogconcave public import Arlib.Convexity.GaussianCooling.PhaseMean public import Arlib.Convexity.GaussianCooling.PhaseVar public import Arlib.Convexity.GaussianCooling.PhaseSchedule public import Arlib.Convexity.GaussianCooling.TerminalPhase public import Arlib.Convexity.GaussianCooling.Unblock public import Mathlib.Analysis.Convex.Measure
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* lp_ttc_Ttc_CV_witPhases(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CV_witPhases___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CV_witVarBudget(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CV_witVarBudget___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CV_witPhases(lean_object* v_n_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(1u);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CV_witPhases___boxed(lean_object* v_n_6_, lean_object* v_x_7_, lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_ttc_Ttc_CV_witPhases(v_n_6_, v_x_7_, v_x_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec(v_x_8_);
lean_dec(v_n_6_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CV_witVarBudget(lean_object* v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CV_witVarBudget___boxed(lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_ttc_Ttc_CV_witVarBudget(v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_Bridge(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_Estimator(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_ZLogconcave(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseMean(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseVar(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseSchedule(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_TerminalPhase(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_Unblock(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Convex_Measure(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Volume_CousinsVempala(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_Bridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_Estimator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_ZLogconcave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseMean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseSchedule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_TerminalPhase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_Unblock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Convex_Measure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
