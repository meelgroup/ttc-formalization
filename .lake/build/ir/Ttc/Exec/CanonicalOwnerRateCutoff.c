// Lean compiler output
// Module: Ttc.Exec.CanonicalOwnerRateCutoff
// Imports: public import Init public meta import Init public import Ttc.Exec.PolyHybridCanonicalFinal
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerRateCutoff_clippedRates___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerRateCutoff_clippedRates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerRateCutoff_clippedRates___redArg(lean_object* v_cap_1_, lean_object* v_lam_2_, lean_object* v_omega_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___f_7_; 
lean_inc(v_i_4_);
v___x_5_ = lean_apply_2(v_lam_2_, v_omega_3_, v_i_4_);
v___x_6_ = lean_apply_1(v_cap_1_, v_i_4_);
v___f_7_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_7_, 0, v___x_5_);
lean_closure_set(v___f_7_, 1, v___x_6_);
return v___f_7_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerRateCutoff_clippedRates(lean_object* v_Omega_8_, lean_object* v_I_9_, lean_object* v_cap_10_, lean_object* v_lam_11_, lean_object* v_omega_12_, lean_object* v_i_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_ttc_Ttc_CanonicalOwnerRateCutoff_clippedRates___redArg(v_cap_10_, v_lam_11_, v_omega_12_, v_i_13_);
return v___x_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_PolyHybridCanonicalFinal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CanonicalOwnerRateCutoff(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_PolyHybridCanonicalFinal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
