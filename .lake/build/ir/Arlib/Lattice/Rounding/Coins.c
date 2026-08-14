// Lean compiler output
// Module: Arlib.Lattice.Rounding.Coins
// Imports: public import Init public meta import Init public import Arlib.Lattice.Rounding.RoundLaw public import Mathlib.Probability.ProductMeasure public import Mathlib.NumberTheory.Real.Irrational
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
extern lean_object* lp_mathlib_finTwoEquiv;
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_Equiv_arrowCongr___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_finFunctionFinEquiv(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__0;
static lean_once_cell_t lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__1;
static lean_once_cell_t lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__2;
LEAN_EXPORT lean_object* lp_ttc_Arlib_Lattice_Rounding_bitEquiv(lean_object*);
static lean_object* _init_lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lp_mathlib_finTwoEquiv;
v___x_3_ = lp_mathlib_Equiv_symm___redArg(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__1, &lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__1_once, _init_lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__1);
v___x_5_ = lean_obj_once(&lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__0, &lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__0_once, _init_lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__0);
v___x_6_ = lp_mathlib_Equiv_arrowCongr___redArg(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_Lattice_Rounding_bitEquiv(lean_object* v_N_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_8_ = lean_obj_once(&lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__2, &lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__2_once, _init_lp_ttc_Arlib_Lattice_Rounding_bitEquiv___closed__2);
v___x_9_ = lean_unsigned_to_nat(2u);
v___x_10_ = lp_mathlib_finFunctionFinEquiv(v___x_9_, v_N_7_);
v___x_11_ = lp_mathlib_Equiv_trans___redArg(v___x_8_, v___x_10_);
return v___x_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_Rounding_RoundLaw(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_ProductMeasure(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_Real_Irrational(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Lattice_Rounding_Coins(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Rounding_RoundLaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_ProductMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_Real_Irrational(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
