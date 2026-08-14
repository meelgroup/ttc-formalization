// Lean compiler output
// Module: Ttc.Exec.FiniteContinuingRetryGaussian
// Imports: public import Init public meta import Init public import Ttc.Exec.FiniteContinuingRetryConcreteDecomposition public import Ttc.Exec.CostedPathwisePhaseKernel public import Ttc.Volume.CVCombinedContinuingAccept
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
lean_object* lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___redArg(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext___redArg(lean_object* v_z_1_){
_start:
{
lean_object* v_snd_2_; lean_object* v_fst_3_; 
v_snd_2_ = lean_ctor_get(v_z_1_, 1);
v_fst_3_ = lean_ctor_get(v_snd_2_, 0);
lean_inc(v_fst_3_);
return v_fst_3_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext___redArg___boxed(lean_object* v_z_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext___redArg(v_z_4_);
lean_dec_ref(v_z_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext(lean_object* v_n_6_, lean_object* v_z_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext___redArg(v_z_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext___boxed(lean_object* v_n_9_, lean_object* v_z_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_ttc_Ttc_FiniteContinuingRetryGaussian_rejectedNext(v_n_9_, v_z_10_);
lean_dec_ref(v_z_10_);
lean_dec(v_n_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost___redArg(lean_object* v_z_12_){
_start:
{
lean_object* v_fst_13_; 
v_fst_13_ = lean_ctor_get(v_z_12_, 0);
lean_inc(v_fst_13_);
return v_fst_13_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost___redArg___boxed(lean_object* v_z_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost___redArg(v_z_14_);
lean_dec_ref(v_z_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost(lean_object* v_n_16_, lean_object* v_z_17_){
_start:
{
lean_object* v_fst_18_; 
v_fst_18_ = lean_ctor_get(v_z_17_, 0);
lean_inc(v_fst_18_);
return v_fst_18_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost___boxed(lean_object* v_n_19_, lean_object* v_z_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_ttc_Ttc_FiniteContinuingRetryGaussian_roundQueryCost(v_n_19_, v_z_20_);
lean_dec_ref(v_z_20_);
lean_dec(v_n_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge___redArg(lean_object* v_cutoff_22_, lean_object* v_z_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_ttc_Ttc_FiniteContinuingRetry_accumulatedCost___redArg(v_z_23_);
if (lean_obj_tag(v___x_24_) == 0)
{
return v_cutoff_22_;
}
else
{
if (lean_obj_tag(v_cutoff_22_) == 0)
{
return v___x_24_;
}
else
{
lean_object* v_val_25_; lean_object* v_val_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_34_; 
v_val_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_val_25_);
lean_dec_ref_known(v___x_24_, 1);
v_val_26_ = lean_ctor_get(v_cutoff_22_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v_cutoff_22_);
if (v_isSharedCheck_34_ == 0)
{
v___x_28_ = v_cutoff_22_;
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_val_26_);
lean_dec(v_cutoff_22_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___f_30_; lean_object* v___x_32_; 
v___f_30_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_30_, 0, v_val_25_);
lean_closure_set(v___f_30_, 1, v_val_26_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___f_30_);
v___x_32_ = v___x_28_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___f_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge___redArg___boxed(lean_object* v_cutoff_35_, lean_object* v_z_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge___redArg(v_cutoff_35_, v_z_36_);
lean_dec_ref(v_z_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge(lean_object* v_n_38_, lean_object* v_cutoff_39_, lean_object* v_z_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge___redArg(v_cutoff_39_, v_z_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge___boxed(lean_object* v_n_42_, lean_object* v_cutoff_43_, lean_object* v_z_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_ttc_Ttc_FiniteContinuingRetryGaussian_cutoffQueryCharge(v_n_42_, v_cutoff_43_, v_z_44_);
lean_dec_ref(v_z_44_);
lean_dec(v_n_42_);
return v_res_45_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_FiniteContinuingRetryConcreteDecomposition(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CostedPathwisePhaseKernel(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_CVCombinedContinuingAccept(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_FiniteContinuingRetryGaussian(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_FiniteContinuingRetryConcreteDecomposition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CostedPathwisePhaseKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_CVCombinedContinuingAccept(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
