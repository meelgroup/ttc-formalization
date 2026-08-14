// Lean compiler output
// Module: Ttc.Exec.CostedInitialThinningTrajectory
// Imports: public import Init public meta import Init public import Ttc.Exec.SequentialCostedPathLumping public import Ttc.Process.PoissonLaws
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg___closed__0;
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2_, 0, v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg(lean_object* v_j_3_, lean_object* v_omega_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_nat_dec_eq(v_j_3_, v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
lean_dec_ref(v_omega_4_);
v___x_7_ = lean_obj_once(&lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg___closed__0, &lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg___closed__0_once, _init_lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg___closed__0);
return v___x_7_;
}
else
{
lean_object* v___x_8_; lean_object* v_fst_9_; 
v___x_8_ = lean_apply_1(v_omega_4_, v___x_5_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
lean_dec_ref(v___x_8_);
return v_fst_9_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg___boxed(lean_object* v_j_10_, lean_object* v_omega_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg(v_j_10_, v_omega_11_);
lean_dec(v_j_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement(lean_object* v_L_13_, lean_object* v_j_14_, lean_object* v_omega_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___redArg(v_j_14_, v_omega_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement___boxed(lean_object* v_L_17_, lean_object* v_j_18_, lean_object* v_omega_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_ttc_Ttc_CostedInitialThinningTrajectory_levelQueryIncrement(v_L_17_, v_j_18_, v_omega_19_);
lean_dec(v_j_18_);
lean_dec(v_L_17_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Ttc_Exec_SequentialCostedPathLumping(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Process_PoissonLaws(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_CostedInitialThinningTrajectory(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Ttc_Exec_SequentialCostedPathLumping(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Process_PoissonLaws(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
