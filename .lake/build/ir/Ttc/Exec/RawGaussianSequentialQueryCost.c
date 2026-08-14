// Lean compiler output
// Module: Ttc.Exec.RawGaussianSequentialQueryCost
// Imports: public import Init public meta import Init public import Ttc.Exec.RawGaussianNormalization public import Ttc.Exec.LazyProperProposalCost
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput___redArg(lean_object*);
lean_object* lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00modelWithCornersEuclideanQuadrant_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawQueryCostOutput___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawQueryCostOutput(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawQueryCostOutput___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawQueryCostOutput___redArg(lean_object* v_r_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v_snd_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_13_; 
lean_inc_ref(v_r_1_);
v___x_2_ = lp_ttc_Ttc_RawGaussianMembership_rawRoundTrace___redArg(v_r_1_);
v___x_3_ = lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput___redArg(v_r_1_);
v_snd_4_ = lean_ctor_get(v___x_3_, 1);
v_isSharedCheck_13_ = !lean_is_exclusive(v___x_3_);
if (v_isSharedCheck_13_ == 0)
{
lean_object* v_unused_14_; 
v_unused_14_ = lean_ctor_get(v___x_3_, 0);
lean_dec(v_unused_14_);
v___x_6_ = v___x_3_;
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_snd_4_);
lean_dec(v___x_3_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_8_ = l_List_lengthTR___redArg(v___x_2_);
lean_dec(v___x_2_);
v___x_9_ = lp_mathlib_Nat_cast___at___00modelWithCornersEuclideanQuadrant_spec__0(v___x_8_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 0, v___x_9_);
v___x_11_ = v___x_6_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v_snd_4_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawQueryCostOutput(lean_object* v_n_15_, lean_object* v_r_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_ttc_Ttc_RawGaussianQueryCost_rawQueryCostOutput___redArg(v_r_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawQueryCostOutput___boxed(lean_object* v_n_18_, lean_object* v_r_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_ttc_Ttc_RawGaussianQueryCost_rawQueryCostOutput(v_n_18_, v_r_19_);
lean_dec(v_n_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath___redArg(lean_object* v_x_21_, lean_object* v_omega_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_zero_24_; uint8_t v_isZero_25_; 
v_zero_24_ = lean_unsigned_to_nat(0u);
v_isZero_25_ = lean_nat_dec_eq(v_x_23_, v_zero_24_);
if (v_isZero_25_ == 1)
{
uint8_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec_ref(v_omega_22_);
v___x_26_ = 0;
v___x_27_ = lean_box(v___x_26_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v_x_21_);
return v___x_28_;
}
else
{
lean_object* v_one_29_; lean_object* v_n_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
lean_dec(v_x_21_);
v_one_29_ = lean_unsigned_to_nat(1u);
v_n_30_ = lean_nat_sub(v_x_23_, v_one_29_);
v___x_31_ = lean_nat_add(v_n_30_, v_one_29_);
lean_dec(v_n_30_);
v___x_32_ = lean_apply_1(v_omega_22_, v___x_31_);
v___x_33_ = lp_ttc_Ttc_RawGaussianMembership_rawRoundOutput___redArg(v___x_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath___redArg___boxed(lean_object* v_x_34_, lean_object* v_omega_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath___redArg(v_x_34_, v_omega_35_, v_x_36_);
lean_dec(v_x_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath(lean_object* v_n_38_, lean_object* v_x_39_, lean_object* v_omega_40_, lean_object* v_x_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath___redArg(v_x_39_, v_omega_40_, v_x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath___boxed(lean_object* v_n_43_, lean_object* v_x_44_, lean_object* v_omega_45_, lean_object* v_x_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_ttc_Ttc_RawGaussianQueryCost_rawMarkedPath(v_n_43_, v_x_44_, v_omega_45_, v_x_46_);
lean_dec(v_x_46_);
lean_dec(v_n_43_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint___redArg(lean_object* v_omega_48_, lean_object* v_k_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v_fst_53_; 
v___x_50_ = lean_unsigned_to_nat(1u);
v___x_51_ = lean_nat_add(v_k_49_, v___x_50_);
v___x_52_ = lean_apply_1(v_omega_48_, v___x_51_);
v_fst_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_fst_53_);
lean_dec_ref(v___x_52_);
return v_fst_53_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint___redArg___boxed(lean_object* v_omega_54_, lean_object* v_k_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint___redArg(v_omega_54_, v_k_55_);
lean_dec(v_k_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint(lean_object* v_n_57_, lean_object* v_omega_58_, lean_object* v_k_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint___redArg(v_omega_58_, v_k_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint___boxed(lean_object* v_n_61_, lean_object* v_omega_62_, lean_object* v_k_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_ttc_Ttc_RawGaussianQueryCost_rawProposalPoint(v_n_61_, v_omega_62_, v_k_63_);
lean_dec(v_k_63_);
lean_dec(v_n_61_);
return v_res_64_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_RawGaussianNormalization(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_LazyProperProposalCost(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_RawGaussianSequentialQueryCost(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_RawGaussianNormalization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_LazyProperProposalCost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
