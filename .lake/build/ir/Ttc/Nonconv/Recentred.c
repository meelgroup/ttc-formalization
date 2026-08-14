// Lean compiler output
// Module: Ttc.Nonconv.Recentred
// Imports: public import Init public meta import Init public import Ttc.Nonconv.Geometry public import Mathlib.Analysis.Complex.ExponentialBounds
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_shift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_shift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_shift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_shift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_scale___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_scale___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_scale(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_scale___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_shift___redArg___lam__0(lean_object* v_b_1_, lean_object* v_w_2_, lean_object* v_00_u03ba_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___f_7_; lean_object* v___f_8_; lean_object* v___f_9_; 
lean_inc(v_j_4_);
v___x_5_ = lean_apply_1(v_b_1_, v_j_4_);
v___x_6_ = lean_apply_1(v_w_2_, v_j_4_);
v___f_7_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_7_, 0, v_00_u03ba_3_);
lean_closure_set(v___f_7_, 1, v___x_6_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_8_, 0, v___f_7_);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_9_, 0, v___x_5_);
lean_closure_set(v___f_9_, 1, v___f_8_);
return v___f_9_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_shift___redArg(lean_object* v_S_10_, lean_object* v_00_u03ba_11_){
_start:
{
lean_object* v_part_12_; lean_object* v_f_13_; lean_object* v_b_14_; lean_object* v_w_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_23_; 
v_part_12_ = lean_ctor_get(v_S_10_, 0);
v_f_13_ = lean_ctor_get(v_S_10_, 1);
v_b_14_ = lean_ctor_get(v_S_10_, 2);
v_w_15_ = lean_ctor_get(v_S_10_, 3);
v_isSharedCheck_23_ = !lean_is_exclusive(v_S_10_);
if (v_isSharedCheck_23_ == 0)
{
v___x_17_ = v_S_10_;
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_w_15_);
lean_inc(v_b_14_);
lean_inc(v_f_13_);
lean_inc(v_part_12_);
lean_dec(v_S_10_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___f_19_; lean_object* v___x_21_; 
lean_inc(v_w_15_);
v___f_19_ = lean_alloc_closure((void*)(lp_ttc_Ttc_FacetSystem_shift___redArg___lam__0), 4, 3);
lean_closure_set(v___f_19_, 0, v_b_14_);
lean_closure_set(v___f_19_, 1, v_w_15_);
lean_closure_set(v___f_19_, 2, v_00_u03ba_11_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 2, v___f_19_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_part_12_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_f_13_);
lean_ctor_set(v_reuseFailAlloc_22_, 2, v___f_19_);
lean_ctor_set(v_reuseFailAlloc_22_, 3, v_w_15_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_shift(lean_object* v_n_24_, lean_object* v_00_u03b9_25_, lean_object* v_F_26_, lean_object* v_S_27_, lean_object* v_00_u03ba_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_ttc_Ttc_FacetSystem_shift___redArg(v_S_27_, v_00_u03ba_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_shift___boxed(lean_object* v_n_30_, lean_object* v_00_u03b9_31_, lean_object* v_F_32_, lean_object* v_S_33_, lean_object* v_00_u03ba_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_ttc_Ttc_FacetSystem_shift(v_n_30_, v_00_u03b9_31_, v_F_32_, v_S_33_, v_00_u03ba_34_);
lean_dec(v_n_30_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_scale___redArg___lam__0(lean_object* v_b_36_, lean_object* v_c_37_, lean_object* v_j_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___f_40_; 
v___x_39_ = lean_apply_1(v_b_36_, v_j_38_);
v___f_40_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_40_, 0, v_c_37_);
lean_closure_set(v___f_40_, 1, v___x_39_);
return v___f_40_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_scale___redArg(lean_object* v_S_41_, lean_object* v_c_42_){
_start:
{
lean_object* v_part_43_; lean_object* v_f_44_; lean_object* v_b_45_; lean_object* v_w_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_54_; 
v_part_43_ = lean_ctor_get(v_S_41_, 0);
v_f_44_ = lean_ctor_get(v_S_41_, 1);
v_b_45_ = lean_ctor_get(v_S_41_, 2);
v_w_46_ = lean_ctor_get(v_S_41_, 3);
v_isSharedCheck_54_ = !lean_is_exclusive(v_S_41_);
if (v_isSharedCheck_54_ == 0)
{
v___x_48_ = v_S_41_;
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_w_46_);
lean_inc(v_b_45_);
lean_inc(v_f_44_);
lean_inc(v_part_43_);
lean_dec(v_S_41_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___f_50_; lean_object* v___x_52_; 
v___f_50_ = lean_alloc_closure((void*)(lp_ttc_Ttc_FacetSystem_scale___redArg___lam__0), 3, 2);
lean_closure_set(v___f_50_, 0, v_b_45_);
lean_closure_set(v___f_50_, 1, v_c_42_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 2, v___f_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_part_43_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_f_44_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v___f_50_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v_w_46_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_scale(lean_object* v_n_55_, lean_object* v_00_u03b9_56_, lean_object* v_F_57_, lean_object* v_S_58_, lean_object* v_c_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_ttc_Ttc_FacetSystem_scale___redArg(v_S_58_, v_c_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FacetSystem_scale___boxed(lean_object* v_n_61_, lean_object* v_00_u03b9_62_, lean_object* v_F_63_, lean_object* v_S_64_, lean_object* v_c_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_ttc_Ttc_FacetSystem_scale(v_n_61_, v_00_u03b9_62_, v_F_63_, v_S_64_, v_c_65_);
lean_dec(v_n_61_);
return v_res_66_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Nonconv_Geometry(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_ExponentialBounds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Nonconv_Recentred(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Nonconv_Geometry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_ExponentialBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
