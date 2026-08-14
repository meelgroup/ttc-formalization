// Lean compiler output
// Module: Ttc.Exec.FiniteContinuingRetryInitialMeasure
// Imports: public import Init public meta import Init public import Ttc.Exec.FiniteContinuingRetryGeneralDecomposition
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
static lean_once_cell_t lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding___redArg___closed__0;
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2_, 0, v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding___redArg(lean_object* v_fallback_3_, lean_object* v_x_4_){
_start:
{
uint8_t v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_5_ = 0;
v___x_6_ = lean_obj_once(&lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding___redArg___closed__0, &lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding___redArg___closed__0_once, _init_lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding___redArg___closed__0);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_fallback_3_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
v___x_8_ = lean_box(v___x_5_);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_x_4_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding(lean_object* v_E_11_, lean_object* v_F_12_, lean_object* v_fallback_13_, lean_object* v_x_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_ttc_Ttc_FiniteContinuingRetryInitialMeasure_initialEmbedding___redArg(v_fallback_13_, v_x_14_);
return v___x_15_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_FiniteContinuingRetryGeneralDecomposition(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_FiniteContinuingRetryInitialMeasure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_FiniteContinuingRetryGeneralDecomposition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
