// Lean compiler output
// Module: Ttc.Exec.CVCorrectedHybridRuntimeAssembly
// Imports: public import Init public meta import Init public import Ttc.Exec.CVCorrectedFixedBlockCost public import Ttc.Exec.CostedPackedJointLaw public import Ttc.Volume.AdaptiveTerminalWarmLawAdjustable
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
lean_object* lp_ttc_Ttc_CostedPackedJointLaw_stateProjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCorrectedHybridRuntimeAssembly_hybridStateProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVCorrectedHybridRuntimeAssembly_hybridStateProjection(lean_object* v_n_1_, lean_object* v_r_2_, lean_object* v_k_3_, lean_object* v_c_4_, lean_object* v_m_5_, lean_object* v_omega_6_){
_start:
{
lean_object* v_fst_7_; lean_object* v_snd_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_17_; 
v_fst_7_ = lean_ctor_get(v_omega_6_, 0);
v_snd_8_ = lean_ctor_get(v_omega_6_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v_omega_6_);
if (v_isSharedCheck_17_ == 0)
{
v___x_10_ = v_omega_6_;
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_snd_8_);
lean_inc(v_fst_7_);
lean_dec(v_omega_6_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
lean_inc(v_k_3_);
lean_inc(v_r_2_);
lean_inc(v_n_1_);
v___x_12_ = lean_alloc_closure((void*)(lp_ttc_Ttc_CostedPackedJointLaw_stateProjection___boxed), 8, 5);
lean_closure_set(v___x_12_, 0, v_n_1_);
lean_closure_set(v___x_12_, 1, v_r_2_);
lean_closure_set(v___x_12_, 2, v_c_4_);
lean_closure_set(v___x_12_, 3, v_k_3_);
lean_closure_set(v___x_12_, 4, v_fst_7_);
v___x_13_ = lean_alloc_closure((void*)(lp_ttc_Ttc_CostedPackedJointLaw_stateProjection___boxed), 8, 5);
lean_closure_set(v___x_13_, 0, v_n_1_);
lean_closure_set(v___x_13_, 1, v_r_2_);
lean_closure_set(v___x_13_, 2, v_m_5_);
lean_closure_set(v___x_13_, 3, v_k_3_);
lean_closure_set(v___x_13_, 4, v_snd_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v___x_13_);
lean_ctor_set(v___x_10_, 0, v___x_12_);
v___x_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVCorrectedFixedBlockCost(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CostedPackedJointLaw(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_AdaptiveTerminalWarmLawAdjustable(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVCorrectedHybridRuntimeAssembly(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVCorrectedFixedBlockCost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CostedPackedJointLaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_AdaptiveTerminalWarmLawAdjustable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
