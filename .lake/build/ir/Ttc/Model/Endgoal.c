// Lean compiler output
// Module: Ttc.Model.Endgoal
// Imports: public import Init public meta import Init public import Ttc.Coupling.Product public import Ttc.Exec.Params public import Ttc.Exec.Geometry public import Ttc.Exec.Coverage public import Ttc.Volume.VolSolCheck public import Ttc.Dnf
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
LEAN_EXPORT uint8_t lp_ttc_Ttc_Box_mmC(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_Box_mmC___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ttc_Ttc_Box_mmC(lean_object* v_n_1_, lean_object* v_hn_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = 1;
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_Box_mmC___boxed(lean_object* v_n_6_, lean_object* v_hn_7_, lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_ttc_Ttc_Box_mmC(v_n_6_, v_hn_7_, v_x_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec(v_x_8_);
lean_dec(v_n_6_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Coupling_Product(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_Params(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_Geometry(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_Coverage(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Volume_VolSolCheck(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Dnf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Model_Endgoal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Coupling_Product(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_Params(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_Geometry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_Coverage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Volume_VolSolCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Dnf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
