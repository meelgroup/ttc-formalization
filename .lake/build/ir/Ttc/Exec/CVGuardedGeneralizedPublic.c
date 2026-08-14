// Lean compiler output
// Module: Ttc.Exec.CVGuardedGeneralizedPublic
// Imports: public import Init public meta import Init public import Ttc.Exec.CVGeneralPolynomialCutoffCapstone public import Ttc.Volume.CVBodyRegularization
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGuardedGeneralizedPublic_regularizedInput___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGuardedGeneralizedPublic_regularizedInput(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGuardedGeneralizedPublic_regularizedInput___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGuardedGeneralizedPublic_regularizedInput___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v_snd_2_; lean_object* v___x_4_; uint8_t v_isShared_5_; uint8_t v_isSharedCheck_18_; 
v_snd_2_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_18_ == 0)
{
lean_object* v_unused_19_; 
v_unused_19_ = lean_ctor_get(v_a_1_, 0);
lean_dec(v_unused_19_);
v___x_4_ = v_a_1_;
v_isShared_5_ = v_isSharedCheck_18_;
goto v_resetjp_3_;
}
else
{
lean_inc(v_snd_2_);
lean_dec(v_a_1_);
v___x_4_ = lean_box(0);
v_isShared_5_ = v_isSharedCheck_18_;
goto v_resetjp_3_;
}
v_resetjp_3_:
{
lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_17_; 
v_fst_6_ = lean_ctor_get(v_snd_2_, 0);
v_snd_7_ = lean_ctor_get(v_snd_2_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v_snd_2_);
if (v_isSharedCheck_17_ == 0)
{
v___x_9_ = v_snd_2_;
v_isShared_10_ = v_isSharedCheck_17_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_snd_7_);
lean_inc(v_fst_6_);
lean_dec(v_snd_2_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_17_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_12_; 
if (v_isShared_10_ == 0)
{
v___x_12_ = v___x_9_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_fst_6_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_snd_7_);
v___x_12_ = v_reuseFailAlloc_16_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_object* v___x_14_; 
if (v_isShared_5_ == 0)
{
lean_ctor_set(v___x_4_, 1, v___x_12_);
lean_ctor_set(v___x_4_, 0, lean_box(0));
v___x_14_ = v___x_4_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, lean_box(0));
lean_ctor_set(v_reuseFailAlloc_15_, 1, v___x_12_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGuardedGeneralizedPublic_regularizedInput(lean_object* v_n_20_, lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_ttc_Ttc_CVGuardedGeneralizedPublic_regularizedInput___redArg(v_a_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CVGuardedGeneralizedPublic_regularizedInput___boxed(lean_object* v_n_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_ttc_Ttc_CVGuardedGeneralizedPublic_regularizedInput(v_n_23_, v_a_24_);
lean_dec(v_n_23_);
return v_res_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CVGeneralPolynomialCutoffCapstone(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_CVBodyRegularization(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CVGuardedGeneralizedPublic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CVGeneralPolynomialCutoffCapstone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_CVBodyRegularization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
