// Lean compiler output
// Module: Ttc.Volume.CVRuntimeAmplification
// Imports: public import Init public meta import Init public import Arlib.Convexity.GaussianCooling.Estimator
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVRuntime_cutoffValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVRuntime_cutoffValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVRuntime_cutoffValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVRuntime_cutoffValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVRuntime_cutoffValue___redArg(lean_object* v_T_1_, lean_object* v_fallback_2_, lean_object* v_cost_3_, lean_object* v_value_4_, lean_object* v_omega_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
lean_inc(v_omega_5_);
v___x_6_ = lean_apply_1(v_cost_3_, v_omega_5_);
v___x_7_ = lean_nat_dec_le(v___x_6_, v_T_1_);
lean_dec(v___x_6_);
if (v___x_7_ == 0)
{
lean_dec(v_omega_5_);
lean_dec(v_value_4_);
lean_inc(v_fallback_2_);
return v_fallback_2_;
}
else
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_value_4_, v_omega_5_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVRuntime_cutoffValue___redArg___boxed(lean_object* v_T_9_, lean_object* v_fallback_10_, lean_object* v_cost_11_, lean_object* v_value_12_, lean_object* v_omega_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_ttc_Ttc_CVRuntime_cutoffValue___redArg(v_T_9_, v_fallback_10_, v_cost_11_, v_value_12_, v_omega_13_);
lean_dec(v_fallback_10_);
lean_dec(v_T_9_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVRuntime_cutoffValue(lean_object* v_Omega_15_, lean_object* v_T_16_, lean_object* v_fallback_17_, lean_object* v_cost_18_, lean_object* v_value_19_, lean_object* v_omega_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_ttc_Ttc_CVRuntime_cutoffValue___redArg(v_T_16_, v_fallback_17_, v_cost_18_, v_value_19_, v_omega_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVRuntime_cutoffValue___boxed(lean_object* v_Omega_22_, lean_object* v_T_23_, lean_object* v_fallback_24_, lean_object* v_cost_25_, lean_object* v_value_26_, lean_object* v_omega_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_ttc_Ttc_CVRuntime_cutoffValue(v_Omega_22_, v_T_23_, v_fallback_24_, v_cost_25_, v_value_26_, v_omega_27_);
lean_dec(v_fallback_24_);
lean_dec(v_T_23_);
return v_res_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_Estimator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Volume_CVRuntimeAmplification(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
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
