// Lean compiler output
// Module: Arlib.Probability.RejectionRounds
// Imports: public import Init public meta import Init public import Mathlib.Probability.ProductMeasure public import Mathlib.Probability.Independence.InfinitePi public import Mathlib.Analysis.SpecificLimits.Basic public import Mathlib.Analysis.Complex.ExponentialBounds public import Arlib.Lattice.KV97.Lemma1 public import Arlib.Probability.Geometric public import Arlib.Probability.RunPlumbing
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
LEAN_EXPORT lean_object* lp_ttc_Arlib_Probability_draw___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_Probability_draw(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_Probability_draw___redArg(lean_object* v_k_1_, lean_object* v_00_u03c9_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_00_u03c9_2_, v_k_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_Probability_draw(lean_object* v_E_4_, lean_object* v_k_5_, lean_object* v_00_u03c9_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_apply_1(v_00_u03c9_6_, v_k_5_);
return v___x_7_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_ProductMeasure(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_Independence_InfinitePi(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecificLimits_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_ExponentialBounds(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_KV97_Lemma1(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_Geometric(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_RunPlumbing(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Probability_RejectionRounds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_ProductMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_Independence_InfinitePi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecificLimits_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_ExponentialBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_KV97_Lemma1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_Geometric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_RunPlumbing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
