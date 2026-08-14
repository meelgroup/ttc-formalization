// Lean compiler output
// Module: Ttc.Exec.RawGaussianMembershipKernel
// Imports: public import Init public meta import Init public import Ttc.Exec.MembershipQueryTrace public import Mathlib.Probability.Distributions.Bernoulli
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOfChoices___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOfChoices(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOfChoices___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOfChoices___redArg(lean_object* v_oracle_1_, lean_object* v_q_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_26_; 
v_fst_3_ = lean_ctor_get(v_q_2_, 0);
v_snd_4_ = lean_ctor_get(v_q_2_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v_q_2_);
if (v_isSharedCheck_26_ == 0)
{
v___x_6_ = v_q_2_;
v_isShared_7_ = v_isSharedCheck_26_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_snd_4_);
lean_inc(v_fst_3_);
lean_dec(v_q_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_26_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v_fst_8_; lean_object* v_snd_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_25_; 
v_fst_8_ = lean_ctor_get(v_fst_3_, 0);
v_snd_9_ = lean_ctor_get(v_fst_3_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v_fst_3_);
if (v_isSharedCheck_25_ == 0)
{
v___x_11_ = v_fst_3_;
v_isShared_12_ = v_isSharedCheck_25_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_snd_9_);
lean_inc(v_fst_8_);
lean_dec(v_fst_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_25_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v_proper_13_; lean_object* v___y_15_; uint8_t v___x_23_; 
lean_inc(v_snd_9_);
v_proper_13_ = lean_apply_1(v_oracle_1_, v_snd_9_);
v___x_23_ = lean_unbox(v_proper_13_);
if (v___x_23_ == 0)
{
v___y_15_ = v_fst_8_;
goto v___jp_14_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = lean_unbox(v_snd_4_);
if (v___x_24_ == 0)
{
v___y_15_ = v_fst_8_;
goto v___jp_14_;
}
else
{
lean_dec(v_fst_8_);
lean_inc(v_snd_9_);
v___y_15_ = v_snd_9_;
goto v___jp_14_;
}
}
v___jp_14_:
{
lean_object* v___x_17_; 
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v___y_15_);
lean_ctor_set(v___x_11_, 0, v_snd_4_);
v___x_17_ = v___x_11_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_snd_4_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v___y_15_);
v___x_17_ = v_reuseFailAlloc_22_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_19_; 
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_17_);
lean_ctor_set(v___x_6_, 0, v_proper_13_);
v___x_19_ = v___x_6_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_proper_13_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___x_17_);
v___x_19_ = v_reuseFailAlloc_21_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
lean_object* v___x_20_; 
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v_snd_9_);
lean_ctor_set(v___x_20_, 1, v___x_19_);
return v___x_20_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOfChoices(lean_object* v_n_27_, lean_object* v_K_28_, lean_object* v_oracle_29_, lean_object* v_q_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_ttc_Ttc_RawGaussianMembership_rawRoundOfChoices___redArg(v_oracle_29_, v_q_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOfChoices___boxed(lean_object* v_n_32_, lean_object* v_K_33_, lean_object* v_oracle_34_, lean_object* v_q_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_ttc_Ttc_RawGaussianMembership_rawRoundOfChoices(v_n_32_, v_K_33_, v_oracle_34_, v_q_35_);
lean_dec(v_n_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput___redArg(lean_object* v_r_37_){
_start:
{
lean_object* v_snd_38_; lean_object* v_snd_39_; lean_object* v_fst_40_; lean_object* v_snd_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
v_snd_38_ = lean_ctor_get(v_r_37_, 1);
lean_inc(v_snd_38_);
lean_dec_ref(v_r_37_);
v_snd_39_ = lean_ctor_get(v_snd_38_, 1);
lean_inc(v_snd_39_);
v_fst_40_ = lean_ctor_get(v_snd_38_, 0);
lean_inc(v_fst_40_);
lean_dec(v_snd_38_);
v_snd_41_ = lean_ctor_get(v_snd_39_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_snd_39_);
if (v_isSharedCheck_48_ == 0)
{
lean_object* v_unused_49_; 
v_unused_49_ = lean_ctor_get(v_snd_39_, 0);
lean_dec(v_unused_49_);
v___x_43_ = v_snd_39_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_snd_41_);
lean_dec(v_snd_39_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v_fst_40_);
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_fst_40_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_snd_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput(lean_object* v_n_50_, lean_object* v_r_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput___redArg(v_r_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput___boxed(lean_object* v_n_53_, lean_object* v_r_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput(v_n_53_, v_r_54_);
lean_dec(v_n_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace___redArg(lean_object* v_r_56_){
_start:
{
lean_object* v_snd_57_; lean_object* v_fst_58_; lean_object* v_fst_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_69_; 
v_snd_57_ = lean_ctor_get(v_r_56_, 1);
lean_inc(v_snd_57_);
v_fst_58_ = lean_ctor_get(v_r_56_, 0);
lean_inc(v_fst_58_);
lean_dec_ref(v_r_56_);
v_fst_59_ = lean_ctor_get(v_snd_57_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v_snd_57_);
if (v_isSharedCheck_69_ == 0)
{
lean_object* v_unused_70_; 
v_unused_70_ = lean_ctor_get(v_snd_57_, 1);
lean_dec(v_unused_70_);
v___x_61_ = v_snd_57_;
v_isShared_62_ = v_isSharedCheck_69_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_fst_59_);
lean_dec(v_snd_57_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_69_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_63_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_63_, 0, v_fst_58_);
v___x_64_ = lean_unbox(v_fst_59_);
lean_dec(v_fst_59_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*1, v___x_64_);
v___x_65_ = lean_box(0);
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 1);
lean_ctor_set(v___x_61_, 1, v___x_65_);
lean_ctor_set(v___x_61_, 0, v___x_63_);
v___x_67_ = v___x_61_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace(lean_object* v_n_71_, lean_object* v_r_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace___redArg(v_r_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace___boxed(lean_object* v_n_74_, lean_object* v_r_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace(v_n_74_, v_r_75_);
lean_dec(v_n_74_);
return v_res_76_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_MembershipQueryTrace(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_Distributions_Bernoulli(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_RawGaussianMembershipKernel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_MembershipQueryTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_Distributions_Bernoulli(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
