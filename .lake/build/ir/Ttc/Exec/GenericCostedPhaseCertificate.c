// Lean compiler output
// Module: Ttc.Exec.GenericCostedPhaseCertificate
// Imports: public import Init public meta import Init public import Ttc.Exec.SequentialCostedPathLumping public import Ttc.Exec.CVSourcePolynomialCutoffCapstone
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
lean_object* l_Ttc_SequentialCostedPathLumping_pathMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___closed__0 = (const lean_object*)&lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_value___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_value(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___lam__0(lean_object* v_self_1_){
_start:
{
lean_object* v_snd_2_; 
v_snd_2_ = lean_ctor_get(v_self_1_, 1);
lean_inc(v_snd_2_);
return v_snd_2_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___lam__0___boxed(lean_object* v_self_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___lam__0(v_self_3_);
lean_dec_ref(v_self_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg(lean_object* v_omega_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_9_; 
v___f_8_ = ((lean_object*)(lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg___closed__0));
v___x_9_ = l_Ttc_SequentialCostedPathLumping_pathMap___redArg(v___f_8_, v_omega_6_, v_a_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath(lean_object* v_E_10_, lean_object* v_omega_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath___redArg(v_omega_11_, v_a_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_value___redArg(lean_object* v_est_14_, lean_object* v_omega_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_alloc_closure((void*)(lp_ttc_Ttc_GenericCostedPhaseCertificate_statePath), 3, 2);
lean_closure_set(v___x_16_, 0, lean_box(0));
lean_closure_set(v___x_16_, 1, v_omega_15_);
v___x_17_ = lean_apply_1(v_est_14_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_GenericCostedPhaseCertificate_value(lean_object* v_E_18_, lean_object* v_est_19_, lean_object* v_omega_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_ttc_Ttc_GenericCostedPhaseCertificate_value___redArg(v_est_19_, v_omega_20_);
return v___x_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Ttc_Exec_SequentialCostedPathLumping(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVSourcePolynomialCutoffCapstone(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_GenericCostedPhaseCertificate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Ttc_Exec_SequentialCostedPathLumping(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVSourcePolynomialCutoffCapstone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
