// Lean compiler output
// Module: Ttc.Exec.CVIndependentStreamGeneralizedCertificate
// Imports: public import Init public meta import Init public import Ttc.Exec.CVIndependentStreamAccuracy public import Ttc.Exec.GenericCostedPhaseCertificate public import Ttc.Exec.CVGeneralPolynomialCutoffCapstone
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
lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentStatePaths___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentStatePaths(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentStatePaths___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentStatePaths___redArg(lean_object* v_omega_1_, lean_object* v_l_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_omega_1_, v_l_2_);
v___x_5_ = lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg(v___x_4_, v_a_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentStatePaths(lean_object* v_E_6_, lean_object* v_k_7_, lean_object* v_omega_8_, lean_object* v_l_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentStatePaths___redArg(v_omega_8_, v_l_9_, v_a_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentStatePaths___boxed(lean_object* v_E_12_, lean_object* v_k_13_, lean_object* v_omega_14_, lean_object* v_l_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentStatePaths(v_E_12_, v_k_13_, v_omega_14_, v_l_15_, v_a_16_);
lean_dec(v_k_13_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentValue___redArg(lean_object* v_k_18_, lean_object* v_est_19_, lean_object* v_omega_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_alloc_closure((void*)(lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentStatePaths___boxed), 5, 3);
lean_closure_set(v___x_21_, 0, lean_box(0));
lean_closure_set(v___x_21_, 1, v_k_18_);
lean_closure_set(v___x_21_, 2, v_omega_20_);
v___x_22_ = lean_apply_1(v_est_19_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentValue(lean_object* v_E_23_, lean_object* v_k_24_, lean_object* v_est_25_, lean_object* v_omega_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_ttc_Ttc_CVIndependentStreamGeneralizedCertificate_independentValue___redArg(v_k_24_, v_est_25_, v_omega_26_);
return v___x_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVIndependentStreamAccuracy(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_GenericCostedPhaseCertificate(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVGeneralPolynomialCutoffCapstone(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVIndependentStreamGeneralizedCertificate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVIndependentStreamAccuracy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_GenericCostedPhaseCertificate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGeneralPolynomialCutoffCapstone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
