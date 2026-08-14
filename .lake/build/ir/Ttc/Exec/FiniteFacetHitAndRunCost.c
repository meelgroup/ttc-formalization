// Lean compiler output
// Module: Ttc.Exec.FiniteFacetHitAndRunCost
// Imports: public import Init public meta import Init public import Arlib.MarkovChains.Continuous.PolytopeHitAndRunExecution public import Ttc.Exec.CostedLazyHitAndRunAdapter public import Ttc.Exec.LazyProperProposalCost
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
lean_object* lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = l_List_lengthTR___redArg(v_inst_1_);
v___x_3_ = lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost___redArg___boxed(lean_object* v_inst_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost___redArg(v_inst_4_);
lean_dec(v_inst_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost(lean_object* v_00_u03b9_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost___redArg(v_inst_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost___boxed(lean_object* v_00_u03b9_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_ttc_Ttc_FiniteFacetHitAndRunCost_facetScanCost(v_00_u03b9_9_, v_inst_10_);
lean_dec(v_inst_10_);
return v_res_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_PolytopeHitAndRunExecution(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_CostedLazyHitAndRunAdapter(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_LazyProperProposalCost(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_FiniteFacetHitAndRunCost(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_PolytopeHitAndRunExecution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_CostedLazyHitAndRunAdapter(builtin);
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
