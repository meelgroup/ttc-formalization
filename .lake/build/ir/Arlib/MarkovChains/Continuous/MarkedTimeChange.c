// Lean compiler output
// Module: Arlib.MarkovChains.Continuous.MarkedTimeChange
// Imports: public import Init public meta import Init public import Arlib.MarkovChains.Continuous.TimeChange
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
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_markedCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_markedCount___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_markedCount(lean_object* v_mark_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_zero_3_; uint8_t v_isZero_4_; 
v_zero_3_ = lean_unsigned_to_nat(0u);
v_isZero_4_ = lean_nat_dec_eq(v_x_2_, v_zero_3_);
if (v_isZero_4_ == 1)
{
lean_dec_ref(v_mark_1_);
return v_zero_3_;
}
else
{
lean_object* v_one_5_; lean_object* v_n_6_; lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_one_5_ = lean_unsigned_to_nat(1u);
v_n_6_ = lean_nat_sub(v_x_2_, v_one_5_);
lean_inc_ref(v_mark_1_);
v___x_7_ = lp_ttc_Arlib_MarkovChains_markedCount(v_mark_1_, v_n_6_);
v___x_8_ = lean_apply_1(v_mark_1_, v_n_6_);
v___x_9_ = lean_unbox(v___x_8_);
if (v___x_9_ == 0)
{
return v___x_7_;
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_nat_add(v___x_7_, v_one_5_);
lean_dec(v___x_7_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_markedCount___boxed(lean_object* v_mark_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_ttc_Arlib_MarkovChains_markedCount(v_mark_11_, v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
lean_object* v_zero_17_; uint8_t v_isZero_18_; 
v_zero_17_ = lean_unsigned_to_nat(0u);
v_isZero_18_ = lean_nat_dec_eq(v_x_14_, v_zero_17_);
if (v_isZero_18_ == 1)
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_h__2_16_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_apply_1(v_h__1_15_, v___x_19_);
return v___x_20_;
}
else
{
lean_object* v_one_21_; lean_object* v_n_22_; lean_object* v___x_23_; 
lean_dec(v_h__1_15_);
v_one_21_ = lean_unsigned_to_nat(1u);
v_n_22_ = lean_nat_sub(v_x_14_, v_one_21_);
v___x_23_ = lean_apply_1(v_h__2_16_, v_n_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter___redArg___boxed(lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter___redArg(v_x_24_, v_h__1_25_, v_h__2_26_);
lean_dec(v_x_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter(lean_object* v_motive_28_, lean_object* v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
lean_object* v_zero_32_; uint8_t v_isZero_33_; 
v_zero_32_ = lean_unsigned_to_nat(0u);
v_isZero_33_ = lean_nat_dec_eq(v_x_29_, v_zero_32_);
if (v_isZero_33_ == 1)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_31_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__1_30_, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_one_36_; lean_object* v_n_37_; lean_object* v___x_38_; 
lean_dec(v_h__1_30_);
v_one_36_ = lean_unsigned_to_nat(1u);
v_n_37_ = lean_nat_sub(v_x_29_, v_one_36_);
v___x_38_ = lean_apply_1(v_h__2_31_, v_n_37_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter___boxed(lean_object* v_motive_39_, lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_ttc___private_Arlib_MarkovChains_Continuous_MarkedTimeChange_0__Arlib_MarkovChains_markedCount_match__1_splitter(v_motive_39_, v_x_40_, v_h__1_41_, v_h__2_42_);
lean_dec(v_x_40_);
return v_res_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_TimeChange(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_MarkedTimeChange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_TimeChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
