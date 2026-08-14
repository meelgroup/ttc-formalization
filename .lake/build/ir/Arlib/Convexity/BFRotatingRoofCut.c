// Lean compiler output
// Module: Arlib.Convexity.BFRotatingRoofCut
// Imports: public import Init public meta import Init public import Arlib.Convexity.BFAffineCoreAttainment public import Arlib.Convexity.SignedCut
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
lean_object* lp_mathlib_Fin_tail___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_roofLinearMap___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_roofLinearMap___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_ttc_Multiset_sum___at___00Finset_sum___at___00Arlib_roofLinearMap_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_ttc_Multiset_sum___at___00Finset_sum___at___00Arlib_roofLinearMap_spec__0_spec__0___closed__0 = (const lean_object*)&lp_ttc_Multiset_sum___at___00Finset_sum___at___00Arlib_roofLinearMap_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_ttc_Multiset_sum___at___00Finset_sum___at___00Arlib_roofLinearMap_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Finset_sum___at___00Arlib_roofLinearMap_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_roofLinearMap___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_roofLinearMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Finset_sum___at___00Arlib_roofLinearMap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_roofLinearMap___lam__0(lean_object* v_x_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lp_mathlib_Fin_tail___redArg(v_x_1_, v_i_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_roofLinearMap___lam__0___boxed(lean_object* v_x_4_, lean_object* v_i_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_ttc_Arlib_roofLinearMap___lam__0(v_x_4_, v_i_5_);
lean_dec(v_i_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Multiset_sum___at___00Finset_sum___at___00Arlib_roofLinearMap_spec__0_spec__0(lean_object* v_s_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_9_ = ((lean_object*)(lp_ttc_Multiset_sum___at___00Finset_sum___at___00Arlib_roofLinearMap_spec__0_spec__0___closed__0));
v___x_10_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_11_ = l_List_foldrTR___redArg(v___f_9_, v___x_10_, v_s_8_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Finset_sum___at___00Arlib_roofLinearMap_spec__0___redArg(lean_object* v_s_12_, lean_object* v_f_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lp_mathlib_Multiset_map___redArg(v_f_13_, v_s_12_);
v___x_15_ = lp_ttc_Multiset_sum___at___00Finset_sum___at___00Arlib_roofLinearMap_spec__0_spec__0(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_roofLinearMap___lam__1(lean_object* v_m_16_, lean_object* v_a_17_, lean_object* v_b_18_, lean_object* v_x_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___f_30_; 
lean_inc(v_x_19_);
v___f_20_ = lean_alloc_closure((void*)(lp_ttc_Arlib_roofLinearMap___lam__0___boxed), 2, 1);
lean_closure_set(v___f_20_, 0, v_x_19_);
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_add(v_m_16_, v___x_21_);
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_nat_mod(v___x_23_, v___x_22_);
lean_dec(v___x_22_);
v___x_25_ = lean_apply_1(v_x_19_, v___x_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_26_, 0, v_a_17_);
lean_closure_set(v___f_26_, 1, v___x_25_);
v___x_27_ = l_List_finRange(v_m_16_);
v___x_28_ = lp_ttc_Finset_sum___at___00Arlib_roofLinearMap_spec__0___redArg(v___x_27_, v___f_20_);
v___f_29_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_29_, 0, v_b_18_);
lean_closure_set(v___f_29_, 1, v___x_28_);
v___f_30_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_30_, 0, v___f_26_);
lean_closure_set(v___f_30_, 1, v___f_29_);
return v___f_30_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_roofLinearMap(lean_object* v_m_31_, lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
lean_object* v___f_34_; 
v___f_34_ = lean_alloc_closure((void*)(lp_ttc_Arlib_roofLinearMap___lam__1), 4, 3);
lean_closure_set(v___f_34_, 0, v_m_31_);
lean_closure_set(v___f_34_, 1, v_a_32_);
lean_closure_set(v___f_34_, 2, v_b_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Finset_sum___at___00Arlib_roofLinearMap_spec__0(lean_object* v_00_u03b9_35_, lean_object* v_s_36_, lean_object* v_f_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_ttc_Finset_sum___at___00Arlib_roofLinearMap_spec__0___redArg(v_s_36_, v_f_37_);
return v___x_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_BFAffineCoreAttainment(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_SignedCut(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_BFRotatingRoofCut(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_BFAffineCoreAttainment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_SignedCut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
