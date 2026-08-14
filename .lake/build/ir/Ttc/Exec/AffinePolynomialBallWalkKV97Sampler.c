// Lean compiler output
// Module: Ttc.Exec.AffinePolynomialBallWalkKV97Sampler
// Imports: public import Init public meta import Init public import Ttc.Exec.PolynomialBallWalkKV97Sampler public import Ttc.Sampler.SpeedyBackend public import Arlib.Lattice.KV97.InflateGeom public import Arlib.MarkovChains.Continuous.SpeedyAffine
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
lean_object* lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(lean_object*);
lean_object* lp_mathlib_WithLp_equiv(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__0;
static lean_once_cell_t lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__1;
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___lam__0(lean_object* v_toFun_1_, lean_object* v_y_2_, lean_object* v_gamma_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___f_6_; 
v___x_5_ = lean_apply_2(v_toFun_1_, v_y_2_, v___y_4_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_6_, 0, v_gamma_3_);
lean_closure_set(v___f_6_, 1, v___x_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___lam__1(lean_object* v_toFun_7_, lean_object* v_cen_8_, lean_object* v___x_9_, lean_object* v___y_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___f_13_; 
lean_inc(v_toFun_7_);
lean_inc(v___y_10_);
v___x_11_ = lean_apply_2(v_toFun_7_, v_cen_8_, v___y_10_);
v___x_12_ = lean_apply_2(v_toFun_7_, v___x_9_, v___y_10_);
v___f_13_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_13_, 0, v___x_11_);
lean_closure_set(v___f_13_, 1, v___x_12_);
return v___f_13_;
}
}
static lean_object* _init_lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__0(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(2u);
v___x_15_ = lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__1(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_obj_once(&lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__0, &lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__0_once, _init_lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__0);
v___x_17_ = lp_mathlib_WithLp_equiv(v___x_16_, lean_box(0));
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg(lean_object* v_cen_18_, lean_object* v_gamma_19_, lean_object* v_y_20_){
_start:
{
lean_object* v___x_21_; lean_object* v_toFun_22_; lean_object* v_invFun_23_; lean_object* v___f_24_; lean_object* v___x_25_; lean_object* v___f_26_; lean_object* v___x_27_; 
v___x_21_ = lean_obj_once(&lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__1, &lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__1_once, _init_lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__1);
v_toFun_22_ = lean_ctor_get(v___x_21_, 0);
v_invFun_23_ = lean_ctor_get(v___x_21_, 1);
lean_inc_n(v_toFun_22_, 2);
v___f_24_ = lean_alloc_closure((void*)(lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___lam__0), 4, 3);
lean_closure_set(v___f_24_, 0, v_toFun_22_);
lean_closure_set(v___f_24_, 1, v_y_20_);
lean_closure_set(v___f_24_, 2, v_gamma_19_);
lean_inc_n(v_invFun_23_, 2);
v___x_25_ = lean_apply_1(v_invFun_23_, v___f_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___lam__1), 4, 3);
lean_closure_set(v___f_26_, 0, v_toFun_22_);
lean_closure_set(v___f_26_, 1, v_cen_18_);
lean_closure_set(v___f_26_, 2, v___x_25_);
v___x_27_ = lean_apply_1(v_invFun_23_, v___f_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart(lean_object* v_n_28_, lean_object* v_cen_29_, lean_object* v_gamma_30_, lean_object* v_y_31_){
_start:
{
lean_object* v___x_32_; lean_object* v_toFun_33_; lean_object* v_invFun_34_; lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___f_37_; lean_object* v___x_38_; 
v___x_32_ = lean_obj_once(&lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__1, &lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__1_once, _init_lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___closed__1);
v_toFun_33_ = lean_ctor_get(v___x_32_, 0);
v_invFun_34_ = lean_ctor_get(v___x_32_, 1);
lean_inc_n(v_toFun_33_, 2);
v___f_35_ = lean_alloc_closure((void*)(lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___lam__0), 4, 3);
lean_closure_set(v___f_35_, 0, v_toFun_33_);
lean_closure_set(v___f_35_, 1, v_y_31_);
lean_closure_set(v___f_35_, 2, v_gamma_30_);
lean_inc_n(v_invFun_34_, 2);
v___x_36_ = lean_apply_1(v_invFun_34_, v___f_35_);
v___f_37_ = lean_alloc_closure((void*)(lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___redArg___lam__1), 4, 3);
lean_closure_set(v___f_37_, 0, v_toFun_33_);
lean_closure_set(v___f_37_, 1, v_cen_29_);
lean_closure_set(v___f_37_, 2, v___x_36_);
v___x_38_ = lean_apply_1(v_invFun_34_, v___f_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart___boxed(lean_object* v_n_39_, lean_object* v_cen_40_, lean_object* v_gamma_41_, lean_object* v_y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_ttc_Ttc_AffinePolynomialBallWalkKV97Sampler_chart(v_n_39_, v_cen_40_, v_gamma_41_, v_y_42_);
lean_dec(v_n_39_);
return v_res_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_PolynomialBallWalkKV97Sampler(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Sampler_SpeedyBackend(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_InflateGeom(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_SpeedyAffine(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_AffinePolynomialBallWalkKV97Sampler(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_PolynomialBallWalkKV97Sampler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Sampler_SpeedyBackend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_InflateGeom(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_SpeedyAffine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
