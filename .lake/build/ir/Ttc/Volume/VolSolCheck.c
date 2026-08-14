// Lean compiler output
// Module: Ttc.Volume.VolSolCheck
// Imports: public import Init public meta import Init public import Ttc.Model.Prelude public import Ttc.Lattice.Decomposition public import Ttc.TtcProb public import Mathlib.MeasureTheory.Constructions.Pi
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
LEAN_EXPORT uint8_t lp_ttc_Ttc_VolSolCheck_evalBool___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_VolSolCheck_evalBool___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ttc_Ttc_VolSolCheck_evalBool(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_VolSolCheck_evalBool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ttc_Ttc_VolSolCheck_evalBool___redArg(lean_object* v_v_1_, lean_object* v_x_2_){
_start:
{
switch(lean_obj_tag(v_x_2_))
{
case 0:
{
uint8_t v___x_3_; 
lean_dec_ref(v_v_1_);
v___x_3_ = 1;
return v___x_3_;
}
case 1:
{
lean_object* v_a_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v_a_4_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_x_2_, 1);
v___x_5_ = lean_apply_1(v_v_1_, v_a_4_);
v___x_6_ = lean_unbox(v___x_5_);
return v___x_6_;
}
case 2:
{
lean_object* v_a_7_; uint8_t v___x_8_; 
v_a_7_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_a_7_);
lean_dec_ref_known(v_x_2_, 1);
v___x_8_ = lp_ttc_Ttc_VolSolCheck_evalBool___redArg(v_v_1_, v_a_7_);
if (v___x_8_ == 0)
{
uint8_t v___x_9_; 
v___x_9_ = 1;
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
case 3:
{
lean_object* v_a_11_; lean_object* v_a_12_; uint8_t v___x_13_; 
v_a_11_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_a_11_);
v_a_12_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_a_12_);
lean_dec_ref_known(v_x_2_, 2);
lean_inc_ref(v_v_1_);
v___x_13_ = lp_ttc_Ttc_VolSolCheck_evalBool___redArg(v_v_1_, v_a_11_);
if (v___x_13_ == 0)
{
lean_dec(v_a_12_);
lean_dec_ref(v_v_1_);
return v___x_13_;
}
else
{
v_x_2_ = v_a_12_;
goto _start;
}
}
default: 
{
lean_object* v_a_15_; lean_object* v_a_16_; uint8_t v___x_17_; 
v_a_15_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_a_15_);
v_a_16_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_a_16_);
lean_dec_ref_known(v_x_2_, 2);
lean_inc_ref(v_v_1_);
v___x_17_ = lp_ttc_Ttc_VolSolCheck_evalBool___redArg(v_v_1_, v_a_15_);
if (v___x_17_ == 0)
{
v_x_2_ = v_a_16_;
goto _start;
}
else
{
lean_dec(v_a_16_);
lean_dec_ref(v_v_1_);
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_VolSolCheck_evalBool___redArg___boxed(lean_object* v_v_19_, lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = lp_ttc_Ttc_VolSolCheck_evalBool___redArg(v_v_19_, v_x_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t lp_ttc_Ttc_VolSolCheck_evalBool(lean_object* v_A_23_, lean_object* v_v_24_, lean_object* v_x_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lp_ttc_Ttc_VolSolCheck_evalBool___redArg(v_v_24_, v_x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_VolSolCheck_evalBool___boxed(lean_object* v_A_27_, lean_object* v_v_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = lp_ttc_Ttc_VolSolCheck_evalBool(v_A_27_, v_v_28_, v_x_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Model_Prelude(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Lattice_Decomposition(uint8_t builtin);
lean_object* initialize_ttc_Ttc_TtcProb(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Constructions_Pi(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Volume_VolSolCheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Model_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Lattice_Decomposition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_TtcProb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Constructions_Pi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
