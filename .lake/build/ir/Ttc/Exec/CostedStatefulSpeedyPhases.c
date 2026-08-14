// Lean compiler output
// Module: Ttc.Exec.CostedStatefulSpeedyPhases
// Imports: public import Init public meta import Init public import Ttc.Exec.SequentialExecutionKernel public import Ttc.Exec.RawGaussianLazyStoppedExecution public import Ttc.Volume.CVDirectSequentialAccuracy
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedStatefulSpeedyPhases_statePath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedStatefulSpeedyPhases_statePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedStatefulSpeedyPhases_statePath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedStatefulSpeedyPhases_statePath___redArg(lean_object* v_omega_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; lean_object* v_snd_4_; 
v___x_3_ = lean_apply_1(v_omega_1_, v_i_2_);
v_snd_4_ = lean_ctor_get(v___x_3_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v___x_3_);
return v_snd_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedStatefulSpeedyPhases_statePath(lean_object* v_n_5_, lean_object* v_omega_6_, lean_object* v_i_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_ttc_Ttc_CostedStatefulSpeedyPhases_statePath___redArg(v_omega_6_, v_i_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedStatefulSpeedyPhases_statePath___boxed(lean_object* v_n_9_, lean_object* v_omega_10_, lean_object* v_i_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_ttc_Ttc_CostedStatefulSpeedyPhases_statePath(v_n_9_, v_omega_10_, v_i_11_);
lean_dec(v_n_9_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_SequentialExecutionKernel(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_RawGaussianLazyStoppedExecution(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_CVDirectSequentialAccuracy(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CostedStatefulSpeedyPhases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_SequentialExecutionKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_RawGaussianLazyStoppedExecution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_CVDirectSequentialAccuracy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
