// Lean compiler output
// Module: Arlib.MarkovChains.Continuous.SphereCoord
// Imports: public import Init public meta import Init public import Arlib.MarkovChains.Continuous.HitAndRun public import Mathlib.Analysis.Normed.Group.BallSphere
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
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_sphereMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_sphereMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_sphereMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_sphereMap___redArg(lean_object* v_f_1_, lean_object* v_00_u03b8_2_){
_start:
{
lean_object* v_toLinearMap_3_; lean_object* v___x_4_; 
v_toLinearMap_3_ = lean_ctor_get(v_f_1_, 0);
lean_inc(v_toLinearMap_3_);
lean_dec_ref(v_f_1_);
v___x_4_ = lean_apply_1(v_toLinearMap_3_, v_00_u03b8_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_sphereMap(lean_object* v_E_5_, lean_object* v_F_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_f_11_, lean_object* v_00_u03b8_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_ttc_Arlib_MarkovChains_sphereMap___redArg(v_f_11_, v_00_u03b8_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_sphereMap___boxed(lean_object* v_E_14_, lean_object* v_F_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_f_20_, lean_object* v_00_u03b8_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_ttc_Arlib_MarkovChains_sphereMap(v_E_14_, v_F_15_, v_inst_16_, v_inst_17_, v_inst_18_, v_inst_19_, v_f_20_, v_00_u03b8_21_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_16_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_HitAndRun(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Group_BallSphere(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_SphereCoord(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_HitAndRun(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Group_BallSphere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
