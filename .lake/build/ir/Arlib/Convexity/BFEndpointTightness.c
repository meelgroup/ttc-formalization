// Lean compiler output
// Module: Arlib.Convexity.BFEndpointTightness
// Imports: public import Init public meta import Init public import Arlib.Convexity.BFEndpointJumpObstruction public import Mathlib.Analysis.SpecificLimits.Basic
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_ttc_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Arlib_bfNormalizedProfileBound_spec__0_spec__0_spec__1(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_bfRampProfile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_bfRampProfile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_bfRampProfile(lean_object* v_k_1_, lean_object* v_t_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___f_7_; lean_object* v___f_8_; 
v___x_3_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_add(v_k_1_, v___x_4_);
v___x_6_ = lp_ttc_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Arlib_bfNormalizedProfileBound_spec__0_spec__0_spec__1(v___x_5_);
v___f_7_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_7_, 0, v___x_6_);
lean_closure_set(v___f_7_, 1, v_t_2_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_8_, 0, v___x_3_);
lean_closure_set(v___f_8_, 1, v___f_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_bfRampProfile___boxed(lean_object* v_k_9_, lean_object* v_t_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_ttc_Arlib_bfRampProfile(v_k_9_, v_t_10_);
lean_dec(v_k_9_);
return v_res_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_BFEndpointJumpObstruction(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecificLimits_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_BFEndpointTightness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_BFEndpointJumpObstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecificLimits_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
