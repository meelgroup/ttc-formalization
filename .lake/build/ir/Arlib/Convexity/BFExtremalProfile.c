// Lean compiler output
// Module: Arlib.Convexity.BFExtremalProfile
// Imports: public import Init public meta import Init public import Arlib.Convexity.AdaptedProfileChain
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_clippedProfile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_clippedProfile(lean_object* v_00_u03c8_1_, lean_object* v_00_u03c4_2_, lean_object* v_t_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___f_5_; 
v___x_4_ = lean_apply_1(v_00_u03c8_1_, v_t_3_);
v___f_5_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_5_, 0, v___x_4_);
lean_closure_set(v___f_5_, 1, v_00_u03c4_2_);
return v___f_5_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_AdaptedProfileChain(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_BFExtremalProfile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_AdaptedProfileChain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
