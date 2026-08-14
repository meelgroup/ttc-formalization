// Lean compiler output
// Module: Ttc.Witness.Box
// Imports: public import Init public meta import Init public import Ttc.Nonconv.BallFacet public import Ttc.Dnf
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lp_ttc_Ttc_conj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_ttc_Ttc_boxAtoms___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_boxAtoms___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_boxAtomList_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_boxAtomList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtomList(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_boxCube_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxCube(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxDNF(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxForm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxForm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg___lam__0(lean_object* v_val_1_, lean_object* v_i_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_eq(v_i_2_, v_val_1_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; 
v___x_4_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_4_;
}
else
{
lean_object* v___x_5_; 
v___x_5_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg___lam__0___boxed(lean_object* v_val_6_, lean_object* v_i_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_ttc_Ttc_boxAtoms___redArg___lam__0(v_val_6_, v_i_7_);
lean_dec(v_i_7_);
lean_dec(v_val_6_);
return v_res_8_;
}
}
static lean_object* _init_lp_ttc_Ttc_boxAtoms___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_9_; lean_object* v___f_10_; 
v___x_9_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_10_, 0, v___x_9_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg___lam__1(lean_object* v_val_11_, lean_object* v_i_12_){
_start:
{
uint8_t v___x_13_; 
v___x_13_ = lean_nat_dec_eq(v_i_12_, v_val_11_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
v___x_14_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_14_;
}
else
{
lean_object* v___f_15_; 
v___f_15_ = lean_obj_once(&lp_ttc_Ttc_boxAtoms___redArg___lam__1___closed__0, &lp_ttc_Ttc_boxAtoms___redArg___lam__1___closed__0_once, _init_lp_ttc_Ttc_boxAtoms___redArg___lam__1___closed__0);
return v___f_15_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg___lam__1___boxed(lean_object* v_val_16_, lean_object* v_i_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_ttc_Ttc_boxAtoms___redArg___lam__1(v_val_16_, v_i_17_);
lean_dec(v_i_17_);
lean_dec(v_val_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___redArg(lean_object* v_c_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v_val_21_; lean_object* v___f_22_; lean_object* v___x_23_; 
v_val_21_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v_x_20_, 1);
v___f_22_ = lean_alloc_closure((void*)(lp_ttc_Ttc_boxAtoms___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_22_, 0, v_val_21_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___f_22_);
lean_ctor_set(v___x_23_, 1, v_c_19_);
return v___x_23_;
}
else
{
lean_object* v_val_24_; lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_c_19_);
v_val_24_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_val_24_);
lean_dec_ref_known(v_x_20_, 1);
v___f_25_ = lean_alloc_closure((void*)(lp_ttc_Ttc_boxAtoms___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_25_, 0, v_val_24_);
v___x_26_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___f_25_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms(lean_object* v_n_28_, lean_object* v_c_29_, lean_object* v_x_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_ttc_Ttc_boxAtoms___redArg(v_c_29_, v_x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtoms___boxed(lean_object* v_n_32_, lean_object* v_c_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_ttc_Ttc_boxAtoms(v_n_32_, v_c_33_, v_x_34_);
lean_dec(v_n_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_boxAtomList_spec__1(lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
if (lean_obj_tag(v_a_36_) == 0)
{
lean_object* v___x_38_; 
v___x_38_ = l_List_reverse___redArg(v_a_37_);
return v___x_38_;
}
else
{
lean_object* v_head_39_; lean_object* v_tail_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_49_; 
v_head_39_ = lean_ctor_get(v_a_36_, 0);
v_tail_40_ = lean_ctor_get(v_a_36_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_a_36_);
if (v_isSharedCheck_49_ == 0)
{
v___x_42_ = v_a_36_;
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_tail_40_);
lean_inc(v_head_39_);
lean_dec(v_a_36_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v_head_39_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v_a_37_);
lean_ctor_set(v___x_42_, 0, v___x_44_);
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_a_37_);
v___x_46_ = v_reuseFailAlloc_48_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
v_a_36_ = v_tail_40_;
v_a_37_ = v___x_46_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_boxAtomList_spec__0(lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
if (lean_obj_tag(v_a_50_) == 0)
{
lean_object* v___x_52_; 
v___x_52_ = l_List_reverse___redArg(v_a_51_);
return v___x_52_;
}
else
{
lean_object* v_head_53_; lean_object* v_tail_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_63_; 
v_head_53_ = lean_ctor_get(v_a_50_, 0);
v_tail_54_ = lean_ctor_get(v_a_50_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_a_50_);
if (v_isSharedCheck_63_ == 0)
{
v___x_56_ = v_a_50_;
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_tail_54_);
lean_inc(v_head_53_);
lean_dec(v_a_50_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v_head_53_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v_a_51_);
lean_ctor_set(v___x_56_, 0, v___x_58_);
v___x_60_ = v___x_56_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_a_51_);
v___x_60_ = v_reuseFailAlloc_62_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
v_a_50_ = v_tail_54_;
v_a_51_ = v___x_60_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxAtomList(lean_object* v_n_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_65_ = l_List_finRange(v_n_64_);
v___x_66_ = lean_box(0);
lean_inc(v___x_65_);
v___x_67_ = lp_ttc_List_mapTR_loop___at___00Ttc_boxAtomList_spec__0(v___x_65_, v___x_66_);
v___x_68_ = lp_ttc_List_mapTR_loop___at___00Ttc_boxAtomList_spec__1(v___x_65_, v___x_66_);
v___x_69_ = l_List_appendTR___redArg(v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_boxCube_spec__0(lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
if (lean_obj_tag(v_a_70_) == 0)
{
lean_object* v___x_72_; 
v___x_72_ = l_List_reverse___redArg(v_a_71_);
return v___x_72_;
}
else
{
lean_object* v_head_73_; lean_object* v_tail_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_84_; 
v_head_73_ = lean_ctor_get(v_a_70_, 0);
v_tail_74_ = lean_ctor_get(v_a_70_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_a_70_);
if (v_isSharedCheck_84_ == 0)
{
v___x_76_ = v_a_70_;
v_isShared_77_ = v_isSharedCheck_84_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_tail_74_);
lean_inc(v_head_73_);
lean_dec(v_a_70_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_84_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_78_ = 1;
v___x_79_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_79_, 0, v_head_73_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*1, v___x_78_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v_a_71_);
lean_ctor_set(v___x_76_, 0, v___x_79_);
v___x_81_ = v___x_76_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_a_71_);
v___x_81_ = v_reuseFailAlloc_83_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
v_a_70_ = v_tail_74_;
v_a_71_ = v___x_81_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxCube(lean_object* v_n_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lp_ttc_Ttc_boxAtomList(v_n_85_);
v___x_87_ = lean_box(0);
v___x_88_ = lp_ttc_List_mapTR_loop___at___00Ttc_boxCube_spec__0(v___x_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxDNF(lean_object* v_n_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lp_ttc_Ttc_boxCube(v_n_89_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_90_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxForm___redArg(lean_object* v_n_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lp_ttc_Ttc_boxAtomList(v_n_93_);
v___x_95_ = lp_ttc_Ttc_conj___redArg(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_boxForm(lean_object* v_n_96_, lean_object* v___hn_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lp_ttc_Ttc_boxForm___redArg(v_n_96_);
return v___x_98_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Nonconv_BallFacet(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Dnf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Witness_Box(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Nonconv_BallFacet(builtin);
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
