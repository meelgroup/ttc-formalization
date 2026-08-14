// Lean compiler output
// Module: Ttc.Access
// Imports: public import Init public meta import Init public import Ttc.TtcProb
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_D___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_D(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_D___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_numCubes___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_numCubes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_numCubes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_cubeAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_cubeAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_cubeAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_D___redArg(lean_object* v_T_1_){
_start:
{
lean_object* v_00_u03c6_2_; lean_object* v_toDNF_3_; lean_object* v___x_4_; 
v_00_u03c6_2_ = lean_ctor_get(v_T_1_, 3);
lean_inc(v_00_u03c6_2_);
v_toDNF_3_ = lean_ctor_get(v_T_1_, 4);
lean_inc_ref(v_toDNF_3_);
lean_dec_ref(v_T_1_);
v___x_4_ = lean_apply_1(v_toDNF_3_, v_00_u03c6_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_D(lean_object* v_A_5_, lean_object* v_n_6_, lean_object* v_T_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_ttc_Ttc_TtcProb_D___redArg(v_T_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_D___boxed(lean_object* v_A_9_, lean_object* v_n_10_, lean_object* v_T_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_ttc_Ttc_TtcProb_D(v_A_9_, v_n_10_, v_T_11_);
lean_dec(v_n_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_numCubes___redArg(lean_object* v_T_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lp_ttc_Ttc_TtcProb_D___redArg(v_T_13_);
v___x_15_ = l_List_lengthTR___redArg(v___x_14_);
lean_dec(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_numCubes(lean_object* v_A_16_, lean_object* v_n_17_, lean_object* v_T_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_ttc_Ttc_TtcProb_numCubes___redArg(v_T_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_numCubes___boxed(lean_object* v_A_20_, lean_object* v_n_21_, lean_object* v_T_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_ttc_Ttc_TtcProb_numCubes(v_A_20_, v_n_21_, v_T_22_);
lean_dec(v_n_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_cubeAt___redArg(lean_object* v_T_24_, lean_object* v_j_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lp_ttc_Ttc_TtcProb_D___redArg(v_T_24_);
v___x_27_ = l_List_get___redArg(v___x_26_, v_j_25_);
lean_dec(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_cubeAt(lean_object* v_A_28_, lean_object* v_n_29_, lean_object* v_T_30_, lean_object* v_j_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_ttc_Ttc_TtcProb_cubeAt___redArg(v_T_30_, v_j_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TtcProb_cubeAt___boxed(lean_object* v_A_33_, lean_object* v_n_34_, lean_object* v_T_35_, lean_object* v_j_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_ttc_Ttc_TtcProb_cubeAt(v_A_33_, v_n_34_, v_T_35_, v_j_36_);
lean_dec(v_n_34_);
return v_res_37_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_TtcProb(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Access(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_TtcProb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
