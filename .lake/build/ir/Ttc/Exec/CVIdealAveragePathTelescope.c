// Lean compiler output
// Module: Ttc.Exec.CVIdealAveragePathTelescope
// Imports: public import Init public meta import Init public import Arlib.Probability.AdaptiveTVTelescope public import Arlib.Probability.TVKernelHeterogeneous public import Arlib.Probability.InhomogeneousMarkov public import Ttc.Volume.CVDirectSequentialWarm
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic___redArg(lean_object* v_i_1_, lean_object* v_p_2_, lean_object* v_j_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_nat_dec_le(v_j_3_, v_i_1_);
if (v___x_4_ == 0)
{
lean_object* v_snd_5_; 
lean_dec(v_j_3_);
v_snd_5_ = lean_ctor_get(v_p_2_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_p_2_);
return v_snd_5_;
}
else
{
lean_object* v_fst_6_; lean_object* v___x_7_; 
v_fst_6_ = lean_ctor_get(v_p_2_, 0);
lean_inc(v_fst_6_);
lean_dec_ref(v_p_2_);
v___x_7_ = lean_apply_1(v_fst_6_, v_j_3_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic___redArg___boxed(lean_object* v_i_8_, lean_object* v_p_9_, lean_object* v_j_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic___redArg(v_i_8_, v_p_9_, v_j_10_);
lean_dec(v_i_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic(lean_object* v_X_12_, lean_object* v_i_13_, lean_object* v_p_14_, lean_object* v_j_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic___redArg(v_i_13_, v_p_14_, v_j_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic___boxed(lean_object* v_X_17_, lean_object* v_i_18_, lean_object* v_p_19_, lean_object* v_j_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_ttc_Ttc_CVIdealAveragePathTelescope_extendIic(v_X_17_, v_i_18_, v_p_19_, v_j_20_);
lean_dec(v_i_18_);
return v_res_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_AdaptiveTVTelescope(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_TVKernelHeterogeneous(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_InhomogeneousMarkov(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_CVDirectSequentialWarm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVIdealAveragePathTelescope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_AdaptiveTVTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_TVKernelHeterogeneous(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_InhomogeneousMarkov(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_CVDirectSequentialWarm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
