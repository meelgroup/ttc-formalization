// Lean compiler output
// Module: Ttc.Coupling.Readoff
// Imports: public import Init public meta import Init public import Ttc.Model.Prelude
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
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Finset_Nat_sigmaAntidiagonalTupleEquivTuple_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ttc_Ttc_trajPois___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_trajPois___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_trajPois___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_trajPois(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ttc_Ttc_trajPois___lam__0(lean_object* v_m_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_apply_1(v_m_1_, v_a_2_);
v___x_4_ = lean_unbox(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_trajPois___lam__0___boxed(lean_object* v_m_5_, lean_object* v_a_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = lp_ttc_Ttc_trajPois___lam__0(v_m_5_, v_a_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_trajPois___lam__1(lean_object* v_00_u03c9j_9_, lean_object* v_s_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_apply_1(v_00_u03c9j_9_, v_s_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_trajPois(lean_object* v_L_12_, lean_object* v_m_13_, lean_object* v_00_u03c9j_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___f_15_ = lean_alloc_closure((void*)(lp_ttc_Ttc_trajPois___lam__0___boxed), 2, 1);
lean_closure_set(v___f_15_, 0, v_m_13_);
v___f_16_ = lean_alloc_closure((void*)(lp_ttc_Ttc_trajPois___lam__1), 2, 1);
lean_closure_set(v___f_16_, 0, v_00_u03c9j_14_);
v___x_17_ = l_List_finRange(v_L_12_);
v___x_18_ = lp_mathlib_Multiset_filter___redArg(v___f_15_, v___x_17_);
v___x_19_ = lp_mathlib_Finset_sum___at___00Finset_Nat_sigmaAntidiagonalTupleEquivTuple_spec__0___redArg(v___x_18_, v___f_16_);
return v___x_19_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Model_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Coupling_Readoff(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
