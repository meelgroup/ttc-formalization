// Lean compiler output
// Module: Ttc.Exec.MembershipQueryTrace
// Imports: public import Init public meta import Init public import Arlib.MarkovChains.Continuous.ProperProposalGaussian
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
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_queryCost___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_queryCost___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_queryCost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_queryCost___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_query___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_query(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_properProposalRound___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_properProposalRound(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_queryCost___redArg(lean_object* v_trace_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_List_lengthTR___redArg(v_trace_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_queryCost___redArg___boxed(lean_object* v_trace_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_ttc_Ttc_MembershipQuery_queryCost___redArg(v_trace_3_);
lean_dec(v_trace_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_queryCost(lean_object* v_S_5_, lean_object* v_trace_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_List_lengthTR___redArg(v_trace_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_queryCost___boxed(lean_object* v_S_8_, lean_object* v_trace_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_ttc_Ttc_MembershipQuery_queryCost(v_S_8_, v_trace_9_);
lean_dec(v_trace_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_query___redArg(lean_object* v_oracle_11_, lean_object* v_point_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
lean_inc(v_point_12_);
v___x_13_ = lean_apply_1(v_oracle_11_, v_point_12_);
v___x_14_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_14_, 0, v_point_12_);
v___x_15_ = lean_unbox(v___x_13_);
lean_ctor_set_uint8(v___x_14_, sizeof(void*)*1, v___x_15_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_14_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_query(lean_object* v_S_18_, lean_object* v_inst_19_, lean_object* v_K_20_, lean_object* v_oracle_21_, lean_object* v_point_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_ttc_Ttc_MembershipQuery_query___redArg(v_oracle_21_, v_point_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_properProposalRound___redArg(lean_object* v_oracle_24_, lean_object* v_choices_25_){
_start:
{
lean_object* v_current_26_; lean_object* v_proposal_27_; uint8_t v_metropolisAccepts_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_47_; 
v_current_26_ = lean_ctor_get(v_choices_25_, 0);
v_proposal_27_ = lean_ctor_get(v_choices_25_, 1);
v_metropolisAccepts_28_ = lean_ctor_get_uint8(v_choices_25_, sizeof(void*)*2);
v_isSharedCheck_47_ = !lean_is_exclusive(v_choices_25_);
if (v_isSharedCheck_47_ == 0)
{
v___x_30_ = v_choices_25_;
v_isShared_31_ = v_isSharedCheck_47_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_proposal_27_);
lean_inc(v_current_26_);
lean_dec(v_choices_25_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_47_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v_proper_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
lean_inc_ref(v_oracle_24_);
lean_inc_n(v_proposal_27_, 2);
v_proper_32_ = lean_apply_1(v_oracle_24_, v_proposal_27_);
v___x_33_ = lp_ttc_Ttc_MembershipQuery_query___redArg(v_oracle_24_, v_proposal_27_);
v___x_34_ = lean_unbox(v_proper_32_);
if (v___x_34_ == 0)
{
lean_object* v___x_36_; 
lean_dec(v_proposal_27_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v_current_26_);
lean_ctor_set(v___x_30_, 0, v___x_33_);
v___x_36_ = v___x_30_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_current_26_);
v___x_36_ = v_reuseFailAlloc_38_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
uint8_t v___x_37_; 
v___x_37_ = lean_unbox(v_proper_32_);
lean_ctor_set_uint8(v___x_36_, sizeof(void*)*2, v___x_37_);
return v___x_36_;
}
}
else
{
if (v_metropolisAccepts_28_ == 0)
{
lean_object* v___x_40_; 
lean_dec(v_proposal_27_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v_current_26_);
lean_ctor_set(v___x_30_, 0, v___x_33_);
v___x_40_ = v___x_30_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_current_26_);
v___x_40_ = v_reuseFailAlloc_42_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
uint8_t v___x_41_; 
v___x_41_ = lean_unbox(v_proper_32_);
lean_ctor_set_uint8(v___x_40_, sizeof(void*)*2, v___x_41_);
return v___x_40_;
}
}
else
{
lean_object* v___x_44_; 
lean_dec(v_current_26_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_33_);
v___x_44_ = v___x_30_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_proposal_27_);
v___x_44_ = v_reuseFailAlloc_46_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
uint8_t v___x_45_; 
v___x_45_ = lean_unbox(v_proper_32_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*2, v___x_45_);
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_MembershipQuery_properProposalRound(lean_object* v_S_48_, lean_object* v_inst_49_, lean_object* v_K_50_, lean_object* v_oracle_51_, lean_object* v_choices_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_ttc_Ttc_MembershipQuery_properProposalRound___redArg(v_oracle_51_, v_choices_52_);
return v___x_53_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_ProperProposalGaussian(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_MembershipQueryTrace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_ProperProposalGaussian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
