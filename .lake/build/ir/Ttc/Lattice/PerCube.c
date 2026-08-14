// Lean compiler output
// Module: Ttc.Lattice.PerCube
// Imports: public import Init public meta import Init public import Ttc.Sampler.Contract
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
lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_cubeForm_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_ttc_Ttc_conj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_PosCube_cubeForm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_PosCube_cubeForm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_PosCube_cubeForm___redArg(lean_object* v_c_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_box(0);
v___x_3_ = lp_ttc_List_mapTR_loop___at___00Ttc_cubeForm_spec__0___redArg(v_c_1_, v___x_2_);
v___x_4_ = lp_ttc_Ttc_conj___redArg(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_PosCube_cubeForm(lean_object* v_A_5_, lean_object* v_c_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lp_ttc_Ttc_PosCube_cubeForm___redArg(v_c_6_);
return v___x_7_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Sampler_Contract(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Lattice_PerCube(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Sampler_Contract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
