// Lean compiler output
// Module: Ttc.Exec.CanonicalOwnerPoissonAssembler
// Imports: public import Init public meta import Init public import Ttc.Exec.CostedMarkedPoissonTrajectory public import Mathlib.Probability.Independence.InfinitePi
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_allCellCounts___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_allCellCounts(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_allCellCounts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_retainedCounts___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_retainedCounts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_retainedCounts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_allCellCounts___redArg(lean_object* v_z_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_5_; lean_object* v_snd_6_; lean_object* v___x_7_; 
v_fst_3_ = lean_ctor_get(v_p_2_, 0);
lean_inc(v_fst_3_);
v_snd_4_ = lean_ctor_get(v_p_2_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v_p_2_);
v___x_5_ = lean_apply_1(v_z_1_, v_fst_3_);
v_snd_6_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_snd_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_apply_1(v_snd_6_, v_snd_4_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_allCellCounts(lean_object* v_I_8_, lean_object* v_L_9_, lean_object* v_z_10_, lean_object* v_p_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_allCellCounts___redArg(v_z_10_, v_p_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_allCellCounts___boxed(lean_object* v_I_13_, lean_object* v_L_14_, lean_object* v_z_15_, lean_object* v_p_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_allCellCounts(v_I_13_, v_L_14_, v_z_15_, v_p_16_);
lean_dec(v_L_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_retainedCounts___redArg(lean_object* v_owner_18_, lean_object* v_z_19_, lean_object* v_s_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_snd_23_; lean_object* v___x_24_; 
lean_inc(v_s_20_);
v___x_21_ = lean_apply_1(v_owner_18_, v_s_20_);
v___x_22_ = lean_apply_1(v_z_19_, v___x_21_);
v_snd_23_ = lean_ctor_get(v___x_22_, 1);
lean_inc(v_snd_23_);
lean_dec_ref(v___x_22_);
v___x_24_ = lean_apply_1(v_snd_23_, v_s_20_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_retainedCounts(lean_object* v_I_25_, lean_object* v_L_26_, lean_object* v_owner_27_, lean_object* v_z_28_, lean_object* v_s_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_retainedCounts___redArg(v_owner_27_, v_z_28_, v_s_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_retainedCounts___boxed(lean_object* v_I_31_, lean_object* v_L_32_, lean_object* v_owner_33_, lean_object* v_z_34_, lean_object* v_s_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_ttc_Ttc_CanonicalOwnerPoissonAssembler_CubeMarkedFamily_retainedCounts(v_I_31_, v_L_32_, v_owner_33_, v_z_34_, v_s_35_);
lean_dec(v_L_32_);
return v_res_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CostedMarkedPoissonTrajectory(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_Independence_InfinitePi(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CanonicalOwnerPoissonAssembler(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CostedMarkedPoissonTrajectory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_Independence_InfinitePi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
