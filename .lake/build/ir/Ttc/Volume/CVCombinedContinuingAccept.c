// Lean compiler output
// Module: Ttc.Volume.CVCombinedContinuingAccept
// Imports: public import Init public meta import Init public import Ttc.Volume.ContinuingRejectionSignificant public import Ttc.Volume.SpeedyAcceptanceRejection
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext___redArg(lean_object* v_p_1_){
_start:
{
lean_object* v_fst_2_; 
v_fst_2_ = lean_ctor_get(v_p_1_, 0);
lean_inc(v_fst_2_);
return v_fst_2_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext___redArg___boxed(lean_object* v_p_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext___redArg(v_p_3_);
lean_dec_ref(v_p_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext(lean_object* v_n_5_, lean_object* v_p_6_){
_start:
{
lean_object* v_fst_7_; 
v_fst_7_ = lean_ctor_get(v_p_6_, 0);
lean_inc(v_fst_7_);
return v_fst_7_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext___boxed(lean_object* v_n_8_, lean_object* v_p_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_ttc_Ttc_CVCombinedContinuingAccept_combinedNext(v_n_8_, v_p_9_);
lean_dec_ref(v_p_9_);
lean_dec(v_n_8_);
return v_res_10_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_ContinuingRejectionSignificant(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_SpeedyAcceptanceRejection(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Volume_CVCombinedContinuingAccept(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_ContinuingRejectionSignificant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_SpeedyAcceptanceRejection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
