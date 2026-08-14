// Lean compiler output
// Module: Arlib.Convexity.Isoperimetry
// Imports: public import Init public meta import Init public import Arlib.Convexity.LogConcave public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar public import Mathlib.MeasureTheory.Measure.WithDensity public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace public import Mathlib.Analysis.InnerProductSpace.PiL2
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
LEAN_EXPORT lean_object* lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal___closed__0 = (const lean_object*)&lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal___closed__0_value;
LEAN_EXPORT lean_object* lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_needleMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_needleMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal___lam__0(lean_object* v_self_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_self_1_, v___y_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___f_9_; 
v___f_9_ = ((lean_object*)(lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal___closed__0));
return v___f_9_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal___boxed(lean_object* v_E_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_ttc_Arlib_instCoeFunLogConcaveDensityForallReal(v_E_10_, v_inst_11_, v_inst_12_, v_inst_13_);
lean_dec(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_needleMap___redArg(lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_a_17_, lean_object* v_v_18_, lean_object* v_t_19_){
_start:
{
lean_object* v_toAddMonoid_20_; lean_object* v_toAddSemigroup_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_toAddMonoid_20_ = lean_ctor_get(v_inst_15_, 0);
lean_inc_ref(v_toAddMonoid_20_);
lean_dec_ref(v_inst_15_);
v_toAddSemigroup_21_ = lean_ctor_get(v_toAddMonoid_20_, 0);
lean_inc(v_toAddSemigroup_21_);
lean_dec_ref(v_toAddMonoid_20_);
v___x_22_ = lean_apply_2(v_inst_16_, v_t_19_, v_v_18_);
v___x_23_ = lean_apply_2(v_toAddSemigroup_21_, v_a_17_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_needleMap(lean_object* v_E_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_a_27_, lean_object* v_v_28_, lean_object* v_t_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_ttc_Arlib_needleMap___redArg(v_inst_25_, v_inst_26_, v_a_27_, v_v_28_, v_t_29_);
return v___x_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_LogConcave(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_EqHaar(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_WithDensity(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_InnerProductSpace(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_PiL2(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_Isoperimetry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_LogConcave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_EqHaar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_WithDensity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_InnerProductSpace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_PiL2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
