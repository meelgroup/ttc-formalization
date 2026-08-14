// Lean compiler output
// Module: Ttc.Exec.CVGaussianWarmFallbackCappedOperational
// Imports: public import Init public meta import Init public import Ttc.Exec.CVGaussianWarmFallbackIndependentCertificate public import Ttc.Exec.CVScoreSeedReferenceSchedule
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
static lean_once_cell_t lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError___closed__0;
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2_, 0, v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError(lean_object* v_m_3_, lean_object* v_eps_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_nat_add(v_i_5_, v___x_6_);
v___x_8_ = lean_nat_dec_lt(v___x_7_, v_m_3_);
lean_dec(v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec(v_i_5_);
lean_dec_ref(v_eps_4_);
v___x_9_ = lean_obj_once(&lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError___closed__0, &lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError___closed__0_once, _init_lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError___closed__0);
return v___x_9_;
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_1(v_eps_4_, v_i_5_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError___boxed(lean_object* v_m_11_, lean_object* v_eps_12_, lean_object* v_i_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_ttc_Ttc_CVGaussianWarmFallbackCappedOperational_activeReferenceMixError(v_m_11_, v_eps_12_, v_i_13_);
lean_dec(v_m_11_);
return v_res_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVGaussianWarmFallbackIndependentCertificate(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVScoreSeedReferenceSchedule(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVGaussianWarmFallbackCappedOperational(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGaussianWarmFallbackIndependentCertificate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVScoreSeedReferenceSchedule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
