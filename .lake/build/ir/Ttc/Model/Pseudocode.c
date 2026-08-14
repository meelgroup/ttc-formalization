// Lean compiler output
// Module: Ttc.Model.Pseudocode
// Imports: public import Init public meta import Init public import Ttc.ModelSupport public import Ttc.Probability public import Arlib.MarkovChains.Continuous.HitAndRunMixing public import Arlib.Convexity.GaussianCooling.PhaseSchedule
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lp_ttc_Ttc_conj___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ttc_Ttc_dropCovered___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_dropCovered___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_dropCovered___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_dropCovered(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_dropCovered___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_stepCost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_stepCost___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_cubeForm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_cubeForm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_cubeForm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_cubeForm_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_dnfForm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_dnfForm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_scaleAtoms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_scaleAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_scaleAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ttc_Ttc_dropCovered___redArg___lam__0(lean_object* v_O_1_, lean_object* v_i_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_covered_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v_covered_4_ = lean_ctor_get(v_O_1_, 1);
lean_inc_ref(v_covered_4_);
lean_dec_ref(v_O_1_);
v___x_5_ = lean_apply_2(v_covered_4_, v_a_3_, v_i_2_);
v___x_6_ = lean_unbox(v___x_5_);
if (v___x_6_ == 0)
{
uint8_t v___x_7_; 
v___x_7_ = 1;
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = 0;
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_dropCovered___redArg___lam__0___boxed(lean_object* v_O_9_, lean_object* v_i_10_, lean_object* v_a_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = lp_ttc_Ttc_dropCovered___redArg___lam__0(v_O_9_, v_i_10_, v_a_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_dropCovered___redArg(lean_object* v_O_14_, lean_object* v_i_15_, lean_object* v_X_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; 
v___f_17_ = lean_alloc_closure((void*)(lp_ttc_Ttc_dropCovered___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_17_, 0, v_O_14_);
lean_closure_set(v___f_17_, 1, v_i_15_);
v___x_18_ = lp_mathlib_Multiset_filter___redArg(v___f_17_, v_X_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_dropCovered(lean_object* v_n_19_, lean_object* v_00_u03b9_20_, lean_object* v_O_21_, lean_object* v_i_22_, lean_object* v_X_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_ttc_Ttc_dropCovered___redArg(v_O_21_, v_i_22_, v_X_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_dropCovered___boxed(lean_object* v_n_25_, lean_object* v_00_u03b9_26_, lean_object* v_O_27_, lean_object* v_i_28_, lean_object* v_X_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_ttc_Ttc_dropCovered(v_n_25_, v_00_u03b9_26_, v_O_27_, v_i_28_, v_X_29_);
lean_dec(v_n_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_stepCost(lean_object* v_cVol_31_, lean_object* v_cSample_32_, lean_object* v_N_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_nat_mul(v_cSample_32_, v_N_33_);
v___x_35_ = lean_nat_add(v_cVol_31_, v___x_34_);
lean_dec(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_stepCost___boxed(lean_object* v_cVol_36_, lean_object* v_cSample_37_, lean_object* v_N_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_ttc_Ttc_stepCost(v_cVol_36_, v_cSample_37_, v_N_38_);
lean_dec(v_N_38_);
lean_dec(v_cSample_37_);
lean_dec(v_cVol_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_cubeForm_spec__0___redArg(lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
if (lean_obj_tag(v_a_40_) == 0)
{
lean_object* v___x_42_; 
v___x_42_ = l_List_reverse___redArg(v_a_41_);
return v___x_42_;
}
else
{
lean_object* v_head_43_; lean_object* v_tail_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_53_; 
v_head_43_ = lean_ctor_get(v_a_40_, 0);
v_tail_44_ = lean_ctor_get(v_a_40_, 1);
v_isSharedCheck_53_ = !lean_is_exclusive(v_a_40_);
if (v_isSharedCheck_53_ == 0)
{
v___x_46_ = v_a_40_;
v_isShared_47_ = v_isSharedCheck_53_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_tail_44_);
lean_inc(v_head_43_);
lean_dec(v_a_40_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_53_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_atom_48_; lean_object* v___x_50_; 
v_atom_48_ = lean_ctor_get(v_head_43_, 0);
lean_inc(v_atom_48_);
lean_dec(v_head_43_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v_a_41_);
lean_ctor_set(v___x_46_, 0, v_atom_48_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_atom_48_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_a_41_);
v___x_50_ = v_reuseFailAlloc_52_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
v_a_40_ = v_tail_44_;
v_a_41_ = v___x_50_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_cubeForm___redArg(lean_object* v_c_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_box(0);
v___x_56_ = lp_ttc_List_mapTR_loop___at___00Ttc_cubeForm_spec__0___redArg(v_c_54_, v___x_55_);
v___x_57_ = lp_ttc_Ttc_conj___redArg(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_cubeForm(lean_object* v_A_58_, lean_object* v_c_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_ttc_Ttc_cubeForm___redArg(v_c_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_cubeForm_spec__0(lean_object* v_A_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lp_ttc_List_mapTR_loop___at___00Ttc_cubeForm_spec__0___redArg(v_a_62_, v_a_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_dnfForm___redArg(lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
else
{
lean_object* v_tail_67_; 
v_tail_67_ = lean_ctor_get(v_x_65_, 1);
if (lean_obj_tag(v_tail_67_) == 0)
{
lean_object* v_head_68_; lean_object* v___x_69_; 
v_head_68_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_head_68_);
lean_dec_ref_known(v_x_65_, 2);
v___x_69_ = lp_ttc_Ttc_cubeForm___redArg(v_head_68_);
return v___x_69_;
}
else
{
lean_object* v_head_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_79_; 
lean_inc(v_tail_67_);
v_head_70_ = lean_ctor_get(v_x_65_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_65_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_x_65_, 1);
lean_dec(v_unused_80_);
v___x_72_ = v_x_65_;
v_isShared_73_ = v_isSharedCheck_79_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_head_70_);
lean_dec(v_x_65_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_79_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = lp_ttc_Ttc_cubeForm___redArg(v_head_70_);
v___x_75_ = lp_ttc_Ttc_dnfForm___redArg(v_tail_67_);
if (v_isShared_73_ == 0)
{
lean_ctor_set_tag(v___x_72_, 4);
lean_ctor_set(v___x_72_, 1, v___x_75_);
lean_ctor_set(v___x_72_, 0, v___x_74_);
v___x_77_ = v___x_72_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_dnfForm(lean_object* v_A_81_, lean_object* v_x_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lp_ttc_Ttc_dnfForm___redArg(v_x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_scaleAtoms___redArg(lean_object* v_c_84_, lean_object* v_atoms_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_87_; lean_object* v_coeff_88_; lean_object* v_bound_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_97_; 
v___x_87_ = lean_apply_1(v_atoms_85_, v_a_86_);
v_coeff_88_ = lean_ctor_get(v___x_87_, 0);
v_bound_89_ = lean_ctor_get(v___x_87_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_97_ == 0)
{
v___x_91_ = v___x_87_;
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_bound_89_);
lean_inc(v_coeff_88_);
lean_dec(v___x_87_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___f_93_; lean_object* v___x_95_; 
v___f_93_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_93_, 0, v_c_84_);
lean_closure_set(v___f_93_, 1, v_bound_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___f_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_coeff_88_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___f_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_scaleAtoms(lean_object* v_n_98_, lean_object* v_A_99_, lean_object* v_c_100_, lean_object* v_atoms_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_ttc_Ttc_scaleAtoms___redArg(v_c_100_, v_atoms_101_, v_a_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_scaleAtoms___boxed(lean_object* v_n_104_, lean_object* v_A_105_, lean_object* v_c_106_, lean_object* v_atoms_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_ttc_Ttc_scaleAtoms(v_n_104_, v_A_105_, v_c_106_, v_atoms_107_, v_a_108_);
lean_dec(v_n_104_);
return v_res_109_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_ModelSupport(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Probability(uint8_t builtin);
lean_object* initialize_ttc_Arlib_MarkovChains_Continuous_HitAndRunMixing(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseSchedule(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Model_Pseudocode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_ModelSupport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Probability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_MarkovChains_Continuous_HitAndRunMixing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_GaussianCooling_PhaseSchedule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
