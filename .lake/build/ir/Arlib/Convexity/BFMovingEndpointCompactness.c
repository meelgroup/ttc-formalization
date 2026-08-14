// Lean compiler output
// Module: Arlib.Convexity.BFMovingEndpointCompactness
// Imports: public import Init public meta import Init public import Arlib.Convexity.BFProfileCompactness
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_bfSegmentPoint___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_bfSegmentPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_bfSegmentPoint___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_a_3_, lean_object* v_b_4_, lean_object* v_t_5_){
_start:
{
lean_object* v_toAddCommGroup_6_; lean_object* v_toAddMonoid_7_; lean_object* v_toAddSemigroup_8_; lean_object* v___x_9_; lean_object* v___f_10_; lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_toAddCommGroup_6_ = lean_ctor_get(v_inst_1_, 1);
lean_inc_ref(v_toAddCommGroup_6_);
lean_dec_ref(v_inst_1_);
v_toAddMonoid_7_ = lean_ctor_get(v_toAddCommGroup_6_, 0);
lean_inc_ref(v_toAddMonoid_7_);
lean_dec_ref(v_toAddCommGroup_6_);
v_toAddSemigroup_8_ = lean_ctor_get(v_toAddMonoid_7_, 0);
lean_inc(v_toAddSemigroup_8_);
lean_dec_ref(v_toAddMonoid_7_);
v___x_9_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_inc(v_t_5_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_10_, 0, v_t_5_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_11_, 0, v___x_9_);
lean_closure_set(v___f_11_, 1, v___f_10_);
lean_inc(v_inst_2_);
v___x_12_ = lean_apply_2(v_inst_2_, v___f_11_, v_a_3_);
v___x_13_ = lean_apply_2(v_inst_2_, v_t_5_, v_b_4_);
v___x_14_ = lean_apply_2(v_toAddSemigroup_8_, v___x_12_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_bfSegmentPoint(lean_object* v_E_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_a_18_, lean_object* v_b_19_, lean_object* v_t_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_ttc_Arlib_bfSegmentPoint___redArg(v_inst_16_, v_inst_17_, v_a_18_, v_b_19_, v_t_20_);
return v___x_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_BFProfileCompactness(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_BFMovingEndpointCompactness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_BFProfileCompactness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
