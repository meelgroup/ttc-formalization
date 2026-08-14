// Lean compiler output
// Module: Ttc.Exec.CostedPackedJointLaw
// Imports: public import Init public meta import Init public import Ttc.Exec.CostedHybridCoordinateSchedule public import Ttc.Exec.CVCostedRuntimeCutoff
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedPackedJointLaw_stateProjection___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedPackedJointLaw_stateProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedPackedJointLaw_stateProjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedPackedJointLaw_stateProjection___redArg(lean_object* v_omega_1_, lean_object* v_j_2_, lean_object* v_i_3_, lean_object* v_l_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_snd_6_; 
v___x_5_ = lean_apply_3(v_omega_1_, v_j_2_, v_i_3_, v_l_4_);
v_snd_6_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_snd_6_);
lean_dec_ref(v___x_5_);
return v_snd_6_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedPackedJointLaw_stateProjection(lean_object* v_n_7_, lean_object* v_r_8_, lean_object* v_m_9_, lean_object* v_k_10_, lean_object* v_omega_11_, lean_object* v_j_12_, lean_object* v_i_13_, lean_object* v_l_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_ttc_Ttc_CostedPackedJointLaw_stateProjection___redArg(v_omega_11_, v_j_12_, v_i_13_, v_l_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedPackedJointLaw_stateProjection___boxed(lean_object* v_n_16_, lean_object* v_r_17_, lean_object* v_m_18_, lean_object* v_k_19_, lean_object* v_omega_20_, lean_object* v_j_21_, lean_object* v_i_22_, lean_object* v_l_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_ttc_Ttc_CostedPackedJointLaw_stateProjection(v_n_16_, v_r_17_, v_m_18_, v_k_19_, v_omega_20_, v_j_21_, v_i_22_, v_l_23_);
lean_dec(v_k_19_);
lean_dec(v_m_18_);
lean_dec(v_r_17_);
lean_dec(v_n_16_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CostedHybridCoordinateSchedule(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVCostedRuntimeCutoff(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CostedPackedJointLaw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CostedHybridCoordinateSchedule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVCostedRuntimeCutoff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
