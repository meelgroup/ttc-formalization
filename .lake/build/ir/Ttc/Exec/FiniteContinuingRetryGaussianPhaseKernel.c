// Lean compiler output
// Module: Ttc.Exec.FiniteContinuingRetryGaussianPhaseKernel
// Imports: public import Init public meta import Init public import Ttc.Exec.FiniteContinuingRetryGaussian public import Ttc.Exec.FiniteContinuingRetryGeneralDecomposition
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___redArg___closed__0;
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v_one_8_; lean_object* v_n_9_; lean_object* v___x_10_; 
lean_dec(v_h__1_2_);
v_one_8_ = lean_unsigned_to_nat(1u);
v_n_9_ = lean_nat_sub(v_x_1_, v_one_8_);
v___x_10_ = lean_apply_1(v_h__2_3_, v_n_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter___redArg___boxed(lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter___redArg(v_x_11_, v_h__1_12_, v_h__2_13_);
lean_dec(v_x_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter(lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_){
_start:
{
lean_object* v_zero_19_; uint8_t v_isZero_20_; 
v_zero_19_ = lean_unsigned_to_nat(0u);
v_isZero_20_ = lean_nat_dec_eq(v_x_16_, v_zero_19_);
if (v_isZero_20_ == 1)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_18_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__1_17_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_one_23_; lean_object* v_n_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_17_);
v_one_23_ = lean_unsigned_to_nat(1u);
v_n_24_ = lean_nat_sub(v_x_16_, v_one_23_);
v___x_25_ = lean_apply_1(v_h__2_18_, v_n_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter___boxed(lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_ttc___private_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel_0__Ttc_FiniteContinuingRetryGaussianPhaseKernel_adaptiveKernel_match__1_splitter(v_motive_26_, v_x_27_, v_h__1_28_, v_h__2_29_);
lean_dec(v_x_27_);
return v_res_30_;
}
}
static lean_object* _init_lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___redArg___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___redArg(lean_object* v_fallback_33_, lean_object* v_x_34_){
_start:
{
uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_35_ = 0;
v___x_36_ = lean_obj_once(&lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___redArg___closed__0, &lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___redArg___closed__0_once, _init_lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___redArg___closed__0);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v_fallback_33_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
v___x_38_ = lean_box(v___x_35_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v_x_34_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState(lean_object* v_n_41_, lean_object* v_fallback_42_, lean_object* v_x_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___redArg(v_fallback_42_, v_x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState___boxed(lean_object* v_n_45_, lean_object* v_fallback_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_ttc_Ttc_FiniteContinuingRetryGaussianPhaseKernel_initialRetryState(v_n_45_, v_fallback_46_, v_x_47_);
lean_dec(v_n_45_);
return v_res_48_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_FiniteContinuingRetryGaussian(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_FiniteContinuingRetryGeneralDecomposition(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_FiniteContinuingRetryGaussianPhaseKernel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_FiniteContinuingRetryGaussian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_FiniteContinuingRetryGeneralDecomposition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
