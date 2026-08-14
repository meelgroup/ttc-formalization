// Lean compiler output
// Module: Ttc.Volume.CVEstimatorNonuniform
// Imports: public import Init public meta import Init public import Ttc.Volume.CVEstimator
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVEst_phaseVector___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVEst_phaseVector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVEst_phaseVector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVEst_phaseVector___redArg(lean_object* v_Y_1_, lean_object* v_i_2_, lean_object* v_omega_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_3(v_Y_1_, v_i_2_, v_j_4_, v_omega_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVEst_phaseVector(lean_object* v_Omega_6_, lean_object* v_m_7_, lean_object* v_k_8_, lean_object* v_Y_9_, lean_object* v_i_10_, lean_object* v_omega_11_, lean_object* v_j_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_apply_3(v_Y_9_, v_i_10_, v_j_12_, v_omega_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVEst_phaseVector___boxed(lean_object* v_Omega_14_, lean_object* v_m_15_, lean_object* v_k_16_, lean_object* v_Y_17_, lean_object* v_i_18_, lean_object* v_omega_19_, lean_object* v_j_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_ttc_Ttc_CVEst_phaseVector(v_Omega_14_, v_m_15_, v_k_16_, v_Y_17_, v_i_18_, v_omega_19_, v_j_20_);
lean_dec(v_k_16_);
lean_dec(v_m_15_);
return v_res_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_CVEstimator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Volume_CVEstimatorNonuniform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_CVEstimator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
