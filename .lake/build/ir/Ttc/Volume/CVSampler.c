// Lean compiler output
// Module: Ttc.Volume.CVSampler
// Imports: public import Init public meta import Init public import Ttc.Volume.CVAmended public import Arlib.Convexity.GaussianCooling.WarmSpeedy public import Arlib.Convexity.GaussianCooling.InteriorBridge
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVSampler_coinX___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVSampler_coinX(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVSampler_coinX___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVSampler_coinX___redArg(lean_object* v_a_1_, lean_object* v_00_u03c9_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_00_u03c9_2_, v_a_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVSampler_coinX(lean_object* v_n_4_, lean_object* v_a_5_, lean_object* v_00_u03c9_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_apply_1(v_00_u03c9_6_, v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVSampler_coinX___boxed(lean_object* v_n_8_, lean_object* v_a_9_, lean_object* v_00_u03c9_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_ttc_Ttc_CVSampler_coinX(v_n_8_, v_a_9_, v_00_u03c9_10_);
lean_dec(v_n_8_);
return v_res_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_CVAmended(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_WarmSpeedy(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_InteriorBridge(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Volume_CVSampler(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_CVAmended(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_WarmSpeedy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_InteriorBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
