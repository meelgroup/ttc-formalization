// Lean compiler output
// Module: Ttc.Witness.BoxSharp
// Imports: public import Init public meta import Init public import Ttc.Exec.Endgoal
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
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Witness_BoxSharp_0__Ttc_Box_bxOffsetOf_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Witness_BoxSharp_0__Ttc_Box_bxOffsetOf_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Witness_BoxSharp_0__Ttc_Box_bxOffsetOf_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Witness_BoxSharp_0__Ttc_Box_bxOffsetOf_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_val_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v_val_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_4_);
lean_dec_ref_known(v_x_1_, 1);
v___x_5_ = lean_apply_1(v_h__1_2_, v_val_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Witness_BoxSharp_0__Ttc_Box_bxOffsetOf_match__1_splitter(lean_object* v_n_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v_val_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v_val_13_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_13_);
lean_dec_ref_known(v_x_10_, 1);
v___x_14_ = lean_apply_1(v_h__1_11_, v_val_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_11_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__2_12_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Witness_BoxSharp_0__Ttc_Box_bxOffsetOf_match__1_splitter___boxed(lean_object* v_n_17_, lean_object* v_motive_18_, lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_ttc___private_Ttc_Witness_BoxSharp_0__Ttc_Box_bxOffsetOf_match__1_splitter(v_n_17_, v_motive_18_, v_x_19_, v_h__1_20_, v_h__2_21_);
lean_dec(v_n_17_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_Endgoal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Witness_BoxSharp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_Endgoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
