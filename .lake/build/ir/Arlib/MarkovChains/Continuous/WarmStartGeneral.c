// Lean compiler output
// Module: Arlib.MarkovChains.Continuous.WarmStartGeneral
// Imports: public import Init public meta import Init public import Arlib.MarkovChains.Continuous.ConvexBodyMixing
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_cubeb(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_cubeb___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_cubeb(lean_object* v_n_1_, lean_object* v_x_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_MarkovChains_cubeb___boxed(lean_object* v_n_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_ttc_Arlib_MarkovChains_cubeb(v_n_4_, v_x_5_);
lean_dec_ref(v_x_5_);
lean_dec(v_n_4_);
return v_res_6_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_ConvexBodyMixing(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_WarmStartGeneral(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_ConvexBodyMixing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
