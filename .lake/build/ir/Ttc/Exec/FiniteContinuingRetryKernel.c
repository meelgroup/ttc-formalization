// Lean compiler output
// Module: Ttc.Exec.FiniteContinuingRetryKernel
// Imports: public import Init public meta import Init public import Ttc.Volume.ContinuingRejectionSignificant public import Arlib.Probability.InhomogeneousMarkov
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_current___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_current___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_current(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_current___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accepted___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accepted___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_ttc_Ttc_FiniteContinuingRetry_accepted(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accepted___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_output___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_output___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_output(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_output___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_retryCount(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_retryCount___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_current___redArg(lean_object* v_s_1_){
_start:
{
lean_object* v_fst_2_; 
v_fst_2_ = lean_ctor_get(v_s_1_, 0);
lean_inc(v_fst_2_);
return v_fst_2_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_current___redArg___boxed(lean_object* v_s_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_ttc_Ttc_FiniteContinuingRetry_current___redArg(v_s_3_);
lean_dec_ref(v_s_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_current(lean_object* v_E_5_, lean_object* v_F_6_, lean_object* v_s_7_){
_start:
{
lean_object* v_fst_8_; 
v_fst_8_ = lean_ctor_get(v_s_7_, 0);
lean_inc(v_fst_8_);
return v_fst_8_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_current___boxed(lean_object* v_E_9_, lean_object* v_F_10_, lean_object* v_s_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_ttc_Ttc_FiniteContinuingRetry_current(v_E_9_, v_F_10_, v_s_11_);
lean_dec_ref(v_s_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accepted___redArg(lean_object* v_s_13_){
_start:
{
lean_object* v_snd_14_; lean_object* v_fst_15_; 
v_snd_14_ = lean_ctor_get(v_s_13_, 1);
v_fst_15_ = lean_ctor_get(v_snd_14_, 0);
lean_inc(v_fst_15_);
return v_fst_15_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accepted___redArg___boxed(lean_object* v_s_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_ttc_Ttc_FiniteContinuingRetry_accepted___redArg(v_s_16_);
lean_dec_ref(v_s_16_);
return v_res_17_;
}
}
LEAN_EXPORT uint8_t lp_ttc_Ttc_FiniteContinuingRetry_accepted(lean_object* v_E_18_, lean_object* v_F_19_, lean_object* v_s_20_){
_start:
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = lp_ttc_Ttc_FiniteContinuingRetry_accepted___redArg(v_s_20_);
v___x_22_ = lean_unbox(v___x_21_);
lean_dec(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accepted___boxed(lean_object* v_E_23_, lean_object* v_F_24_, lean_object* v_s_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = lp_ttc_Ttc_FiniteContinuingRetry_accepted(v_E_23_, v_F_24_, v_s_25_);
lean_dec_ref(v_s_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_output___redArg(lean_object* v_s_28_){
_start:
{
lean_object* v_snd_29_; lean_object* v_snd_30_; lean_object* v_fst_31_; 
v_snd_29_ = lean_ctor_get(v_s_28_, 1);
v_snd_30_ = lean_ctor_get(v_snd_29_, 1);
v_fst_31_ = lean_ctor_get(v_snd_30_, 0);
lean_inc(v_fst_31_);
return v_fst_31_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_output___redArg___boxed(lean_object* v_s_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_ttc_Ttc_FiniteContinuingRetry_output___redArg(v_s_32_);
lean_dec_ref(v_s_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_output(lean_object* v_E_34_, lean_object* v_F_35_, lean_object* v_s_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_ttc_Ttc_FiniteContinuingRetry_output___redArg(v_s_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_output___boxed(lean_object* v_E_38_, lean_object* v_F_39_, lean_object* v_s_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_ttc_Ttc_FiniteContinuingRetry_output(v_E_38_, v_F_39_, v_s_40_);
lean_dec_ref(v_s_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___redArg(lean_object* v_s_42_){
_start:
{
lean_object* v_snd_43_; lean_object* v_snd_44_; lean_object* v_snd_45_; 
v_snd_43_ = lean_ctor_get(v_s_42_, 1);
v_snd_44_ = lean_ctor_get(v_snd_43_, 1);
v_snd_45_ = lean_ctor_get(v_snd_44_, 1);
lean_inc(v_snd_45_);
return v_snd_45_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___redArg___boxed(lean_object* v_s_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___redArg(v_s_46_);
lean_dec_ref(v_s_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost(lean_object* v_E_48_, lean_object* v_F_49_, lean_object* v_s_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___redArg(v_s_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___boxed(lean_object* v_E_52_, lean_object* v_F_53_, lean_object* v_s_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost(v_E_52_, v_F_53_, v_s_54_);
lean_dec_ref(v_s_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_retryCount(lean_object* v_L_56_){
_start:
{
lean_inc(v_L_56_);
return v_L_56_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetry_retryCount___boxed(lean_object* v_L_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_ttc_Ttc_FiniteContinuingRetry_retryCount(v_L_57_);
lean_dec(v_L_57_);
return v_res_58_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_ContinuingRejectionSignificant(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_InhomogeneousMarkov(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_FiniteContinuingRetryKernel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_ContinuingRejectionSignificant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_InhomogeneousMarkov(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
