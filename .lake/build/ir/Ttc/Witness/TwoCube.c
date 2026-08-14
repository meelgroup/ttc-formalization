// Lean compiler output
// Module: Ttc.Witness.TwoCube
// Imports: public import Init public meta import Init public import Ttc.Exec.Final
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
lean_object* lp_ttc_Ttc_boxAtomList(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_ttc_Ttc_conj___redArg(lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_twoAtoms(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_cubeL_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_cubeL(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_cubeR_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_cubeR(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_twoForm_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_twoForm_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_twoForm(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__0(lean_object* v_val_1_, lean_object* v_i_2_){
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
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__0___boxed(lean_object* v_val_6_, lean_object* v_i_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__0(v_val_6_, v_i_7_);
lean_dec(v_i_7_);
lean_dec(v_val_6_);
return v_res_8_;
}
}
static lean_object* _init_lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_9_; lean_object* v___f_10_; 
v___x_9_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_10_, 0, v___x_9_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1(lean_object* v_val_11_, lean_object* v_i_12_){
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
v___f_15_ = lean_obj_once(&lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1___closed__0, &lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1___closed__0_once, _init_lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1___closed__0);
return v___f_15_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1___boxed(lean_object* v_val_16_, lean_object* v_i_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1(v_val_16_, v_i_17_);
lean_dec(v_i_17_);
lean_dec(v_val_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___redArg(lean_object* v_lo_19_, lean_object* v_c_20_, lean_object* v_x_21_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
lean_object* v_val_22_; lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___x_25_; 
v_val_22_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_val_22_);
lean_dec_ref_known(v_x_21_, 1);
v___f_23_ = lean_alloc_closure((void*)(lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_23_, 0, v_val_22_);
v___f_24_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_24_, 0, v_lo_19_);
lean_closure_set(v___f_24_, 1, v_c_20_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___f_23_);
lean_ctor_set(v___x_25_, 1, v___f_24_);
return v___x_25_;
}
else
{
lean_object* v_val_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___x_29_; 
lean_dec(v_c_20_);
v_val_26_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_val_26_);
lean_dec_ref_known(v_x_21_, 1);
v___f_27_ = lean_alloc_closure((void*)(lp_ttc_Ttc_TwoCube_sbAtoms___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_27_, 0, v_val_26_);
v___f_28_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_28_, 0, v_lo_19_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___f_27_);
lean_ctor_set(v___x_29_, 1, v___f_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms(lean_object* v_n_30_, lean_object* v_lo_31_, lean_object* v_c_32_, lean_object* v_x_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_ttc_Ttc_TwoCube_sbAtoms___redArg(v_lo_31_, v_c_32_, v_x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_sbAtoms___boxed(lean_object* v_n_35_, lean_object* v_lo_36_, lean_object* v_c_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_ttc_Ttc_TwoCube_sbAtoms(v_n_35_, v_lo_36_, v_c_37_, v_x_38_);
lean_dec(v_n_35_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_twoAtoms(lean_object* v_n_40_, lean_object* v_lo_41_, lean_object* v_c_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_44_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_inc(v_c_42_);
lean_inc(v_n_40_);
v___x_45_ = lean_alloc_closure((void*)(lp_ttc_Ttc_TwoCube_sbAtoms___boxed), 4, 3);
lean_closure_set(v___x_45_, 0, v_n_40_);
lean_closure_set(v___x_45_, 1, v___x_44_);
lean_closure_set(v___x_45_, 2, v_c_42_);
v___x_46_ = lean_alloc_closure((void*)(lp_ttc_Ttc_TwoCube_sbAtoms___boxed), 4, 3);
lean_closure_set(v___x_46_, 0, v_n_40_);
lean_closure_set(v___x_46_, 1, v_lo_41_);
lean_closure_set(v___x_46_, 2, v_c_42_);
v___x_47_ = l_Sum_elim___redArg(v___x_45_, v___x_46_, v_a_43_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_cubeL_spec__0(lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
if (lean_obj_tag(v_a_48_) == 0)
{
lean_object* v___x_50_; 
v___x_50_ = l_List_reverse___redArg(v_a_49_);
return v___x_50_;
}
else
{
lean_object* v_head_51_; lean_object* v_tail_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_63_; 
v_head_51_ = lean_ctor_get(v_a_48_, 0);
v_tail_52_ = lean_ctor_get(v_a_48_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_a_48_);
if (v_isSharedCheck_63_ == 0)
{
v___x_54_ = v_a_48_;
v_isShared_55_ = v_isSharedCheck_63_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_tail_52_);
lean_inc(v_head_51_);
lean_dec(v_a_48_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_63_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v_head_51_);
v___x_57_ = 1;
v___x_58_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*1, v___x_57_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 1, v_a_49_);
lean_ctor_set(v___x_54_, 0, v___x_58_);
v___x_60_ = v___x_54_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_a_49_);
v___x_60_ = v_reuseFailAlloc_62_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
v_a_48_ = v_tail_52_;
v_a_49_ = v___x_60_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_cubeL(lean_object* v_n_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lp_ttc_Ttc_boxAtomList(v_n_64_);
v___x_66_ = lean_box(0);
v___x_67_ = lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_cubeL_spec__0(v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_cubeR_spec__0(lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
if (lean_obj_tag(v_a_68_) == 0)
{
lean_object* v___x_70_; 
v___x_70_ = l_List_reverse___redArg(v_a_69_);
return v___x_70_;
}
else
{
lean_object* v_head_71_; lean_object* v_tail_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_83_; 
v_head_71_ = lean_ctor_get(v_a_68_, 0);
v_tail_72_ = lean_ctor_get(v_a_68_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_83_ == 0)
{
v___x_74_ = v_a_68_;
v_isShared_75_ = v_isSharedCheck_83_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_tail_72_);
lean_inc(v_head_71_);
lean_dec(v_a_68_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_83_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v_head_71_);
v___x_77_ = 1;
v___x_78_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*1, v___x_77_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v_a_69_);
lean_ctor_set(v___x_74_, 0, v___x_78_);
v___x_80_ = v___x_74_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_a_69_);
v___x_80_ = v_reuseFailAlloc_82_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
v_a_68_ = v_tail_72_;
v_a_69_ = v___x_80_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_cubeR(lean_object* v_n_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lp_ttc_Ttc_boxAtomList(v_n_84_);
v___x_86_ = lean_box(0);
v___x_87_ = lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_cubeR_spec__0(v___x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_twoForm_spec__0(lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
if (lean_obj_tag(v_a_88_) == 0)
{
lean_object* v___x_90_; 
v___x_90_ = l_List_reverse___redArg(v_a_89_);
return v___x_90_;
}
else
{
lean_object* v_head_91_; lean_object* v_tail_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_101_; 
v_head_91_ = lean_ctor_get(v_a_88_, 0);
v_tail_92_ = lean_ctor_get(v_a_88_, 1);
v_isSharedCheck_101_ = !lean_is_exclusive(v_a_88_);
if (v_isSharedCheck_101_ == 0)
{
v___x_94_ = v_a_88_;
v_isShared_95_ = v_isSharedCheck_101_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_tail_92_);
lean_inc(v_head_91_);
lean_dec(v_a_88_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_101_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v_head_91_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v_a_89_);
lean_ctor_set(v___x_94_, 0, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_a_89_);
v___x_98_ = v_reuseFailAlloc_100_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
v_a_88_ = v_tail_92_;
v_a_89_ = v___x_98_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_twoForm_spec__1(lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
if (lean_obj_tag(v_a_102_) == 0)
{
lean_object* v___x_104_; 
v___x_104_ = l_List_reverse___redArg(v_a_103_);
return v___x_104_;
}
else
{
lean_object* v_head_105_; lean_object* v_tail_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_115_; 
v_head_105_ = lean_ctor_get(v_a_102_, 0);
v_tail_106_ = lean_ctor_get(v_a_102_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_a_102_);
if (v_isSharedCheck_115_ == 0)
{
v___x_108_ = v_a_102_;
v_isShared_109_ = v_isSharedCheck_115_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_tail_106_);
lean_inc(v_head_105_);
lean_dec(v_a_102_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_115_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v_head_105_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v_a_103_);
lean_ctor_set(v___x_108_, 0, v___x_110_);
v___x_112_ = v___x_108_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_a_103_);
v___x_112_ = v_reuseFailAlloc_114_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
v_a_102_ = v_tail_106_;
v_a_103_ = v___x_112_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_TwoCube_twoForm(lean_object* v_n_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_117_ = lp_ttc_Ttc_boxAtomList(v_n_116_);
v___x_118_ = lean_box(0);
lean_inc(v___x_117_);
v___x_119_ = lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_twoForm_spec__0(v___x_117_, v___x_118_);
v___x_120_ = lp_ttc_Ttc_conj___redArg(v___x_119_);
v___x_121_ = lp_ttc_List_mapTR_loop___at___00Ttc_TwoCube_twoForm_spec__1(v___x_117_, v___x_118_);
v___x_122_ = lp_ttc_Ttc_conj___redArg(v___x_121_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_120_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
return v___x_123_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_Final(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Witness_TwoCube(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_Final(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
