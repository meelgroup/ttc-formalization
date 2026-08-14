// Lean compiler output
// Module: Ttc.Exec.SequentialCostedPathLumping
// Imports: public import Init public meta import Init public import Ttc.Exec.CostedStatefulSpeedyPhases
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_pathMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_pathMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_historyMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_historyMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_historyMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_pathMap___redArg(lean_object* v_f_1_, lean_object* v_omega_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_omega_2_, v_i_3_);
v___x_5_ = lean_apply_1(v_f_1_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_pathMap(lean_object* v_A_6_, lean_object* v_B_7_, lean_object* v_f_8_, lean_object* v_omega_9_, lean_object* v_i_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_ttc_Ttc_SequentialCostedPathLumping_pathMap___redArg(v_f_8_, v_omega_9_, v_i_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_historyMap___redArg(lean_object* v_f_12_, lean_object* v_h_13_, lean_object* v_j_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_apply_1(v_h_13_, v_j_14_);
v___x_16_ = lean_apply_1(v_f_12_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_historyMap(lean_object* v_A_17_, lean_object* v_B_18_, lean_object* v_f_19_, lean_object* v_i_20_, lean_object* v_h_21_, lean_object* v_j_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_ttc_Ttc_SequentialCostedPathLumping_historyMap___redArg(v_f_19_, v_h_21_, v_j_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_historyMap___boxed(lean_object* v_A_24_, lean_object* v_B_25_, lean_object* v_f_26_, lean_object* v_i_27_, lean_object* v_h_28_, lean_object* v_j_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_ttc_Ttc_SequentialCostedPathLumping_historyMap(v_A_24_, v_B_25_, v_f_26_, v_i_27_, v_h_28_, v_j_29_);
lean_dec(v_i_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory___redArg(lean_object* v_i_31_, lean_object* v_p_32_, lean_object* v_j_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = lean_nat_dec_le(v_j_33_, v_i_31_);
if (v___x_34_ == 0)
{
lean_object* v_snd_35_; 
lean_dec(v_j_33_);
v_snd_35_ = lean_ctor_get(v_p_32_, 1);
lean_inc(v_snd_35_);
lean_dec_ref(v_p_32_);
return v_snd_35_;
}
else
{
lean_object* v_fst_36_; lean_object* v___x_37_; 
v_fst_36_ = lean_ctor_get(v_p_32_, 0);
lean_inc(v_fst_36_);
lean_dec_ref(v_p_32_);
v___x_37_ = lean_apply_1(v_fst_36_, v_j_33_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory___redArg___boxed(lean_object* v_i_38_, lean_object* v_p_39_, lean_object* v_j_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory___redArg(v_i_38_, v_p_39_, v_j_40_);
lean_dec(v_i_38_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory(lean_object* v_B_42_, lean_object* v_i_43_, lean_object* v_p_44_, lean_object* v_j_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory___redArg(v_i_43_, v_p_44_, v_j_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory___boxed(lean_object* v_B_47_, lean_object* v_i_48_, lean_object* v_p_49_, lean_object* v_j_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_ttc_Ttc_SequentialCostedPathLumping_extendHistory(v_B_47_, v_i_48_, v_p_49_, v_j_50_);
lean_dec(v_i_48_);
return v_res_51_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CostedStatefulSpeedyPhases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_SequentialCostedPathLumping(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CostedStatefulSpeedyPhases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
