// Lean compiler output
// Module: Ttc.Exec.CostedMarkedPoisson
// Imports: public import Init public meta import Init public import Ttc.Exec.CostedAdaptiveIidCalls public import Ttc.Exec.KV97RoundedEndpointBridge public import Ttc.Process.PoissonLaws
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00FormalMultilinearSeries_compChangeOfVariables_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___redArg___lam__0(lean_object* v_omega_1_, lean_object* v_a_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_snd_5_; uint8_t v___x_6_; 
v___x_4_ = lean_apply_1(v_omega_1_, v_j_3_);
v_snd_5_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_nat_dec_eq(v_snd_5_, v_a_2_);
lean_dec(v_snd_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(0u);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(1u);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___redArg___lam__0___boxed(lean_object* v_omega_9_, lean_object* v_a_10_, lean_object* v_j_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___redArg___lam__0(v_omega_9_, v_a_10_, v_j_11_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___redArg(lean_object* v_N_13_, lean_object* v_omega_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___f_16_ = lean_alloc_closure((void*)(lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_16_, 0, v_omega_14_);
lean_closure_set(v___f_16_, 1, v_a_15_);
v___x_17_ = l_List_range(v_N_13_);
v___x_18_ = lp_mathlib_Finset_sum___at___00FormalMultilinearSeries_compChangeOfVariables_spec__0___redArg(v___x_17_, v___f_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts(lean_object* v_L_19_, lean_object* v_N_20_, lean_object* v_omega_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___redArg(v_N_20_, v_omega_21_, v_a_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts___boxed(lean_object* v_L_24_, lean_object* v_N_25_, lean_object* v_omega_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_ttc_Ttc_CostedMarkedPoisson_prefixMarkCounts(v_L_24_, v_N_25_, v_omega_26_, v_a_27_);
lean_dec(v_L_24_);
return v_res_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CostedAdaptiveIidCalls(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_KV97RoundedEndpointBridge(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Process_PoissonLaws(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CostedMarkedPoisson(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CostedAdaptiveIidCalls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_KV97RoundedEndpointBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Process_PoissonLaws(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
