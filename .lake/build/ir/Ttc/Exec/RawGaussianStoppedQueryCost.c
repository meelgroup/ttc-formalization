// Lean compiler output
// Module: Ttc.Exec.RawGaussianStoppedQueryCost
// Imports: public import Init public meta import Init public import Ttc.Exec.RawGaussianSequentialQueryCost public import Mathlib.Probability.Process.FiniteDimensionalLaws
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapPath___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapHistory___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapHistory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapHistory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_rawInitial___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_rawInitial(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_rawInitial___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapPath___redArg(lean_object* v_f_1_, lean_object* v_omega_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_omega_2_, v_i_3_);
v___x_5_ = lean_apply_1(v_f_1_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapPath(lean_object* v_S_6_, lean_object* v_T_7_, lean_object* v_f_8_, lean_object* v_omega_9_, lean_object* v_i_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapPath___redArg(v_f_8_, v_omega_9_, v_i_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapHistory___redArg(lean_object* v_f_12_, lean_object* v_h_13_, lean_object* v_i_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_apply_1(v_h_13_, v_i_14_);
v___x_16_ = lean_apply_1(v_f_12_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapHistory(lean_object* v_S_17_, lean_object* v_T_18_, lean_object* v_f_19_, lean_object* v_b_20_, lean_object* v_h_21_, lean_object* v_i_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapHistory___redArg(v_f_19_, v_h_21_, v_i_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapHistory___boxed(lean_object* v_S_24_, lean_object* v_T_25_, lean_object* v_f_26_, lean_object* v_b_27_, lean_object* v_h_28_, lean_object* v_i_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_ttc_Ttc_RawGaussianStoppedQueryCost_mapHistory(v_S_24_, v_T_25_, v_f_26_, v_b_27_, v_h_28_, v_i_29_);
lean_dec(v_b_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_rawInitial___redArg(lean_object* v_x_31_){
_start:
{
uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_32_ = 0;
v___x_33_ = lean_box(v___x_32_);
lean_inc(v_x_31_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v_x_31_);
v___x_35_ = lean_box(v___x_32_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v_x_31_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_rawInitial(lean_object* v_n_38_, lean_object* v_x_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_ttc_Ttc_RawGaussianStoppedQueryCost_rawInitial___redArg(v_x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianStoppedQueryCost_rawInitial___boxed(lean_object* v_n_41_, lean_object* v_x_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_ttc_Ttc_RawGaussianStoppedQueryCost_rawInitial(v_n_41_, v_x_42_);
lean_dec(v_n_41_);
return v_res_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_RawGaussianSequentialQueryCost(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_Process_FiniteDimensionalLaws(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_RawGaussianStoppedQueryCost(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_RawGaussianSequentialQueryCost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_Process_FiniteDimensionalLaws(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
