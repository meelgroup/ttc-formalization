// Lean compiler output
// Module: Ttc.Exec.Geometry
// Imports: public import Init public meta import Init public import Ttc.Lattice.Decomposition public import Ttc.Model.ProblemSetting public import Arlib.Lattice.Basic public import Mathlib.Analysis.Convex.Measure public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__0___boxed(lean_object*);
static lean_once_cell_t lp_ttc_Ttc_degenAtoms___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenAtoms___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__2(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__2___boxed(lean_object*);
static const lean_closure_object lp_ttc_Ttc_degenAtoms___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_ttc_Ttc_degenAtoms___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_ttc_Ttc_degenAtoms___closed__0 = (const lean_object*)&lp_ttc_Ttc_degenAtoms___closed__0_value;
static lean_once_cell_t lp_ttc_Ttc_degenAtoms___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenAtoms___closed__1;
static const lean_closure_object lp_ttc_Ttc_degenAtoms___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_ttc_Ttc_degenAtoms___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_ttc_Ttc_degenAtoms___closed__2 = (const lean_object*)&lp_ttc_Ttc_degenAtoms___closed__2_value;
static lean_once_cell_t lp_ttc_Ttc_degenAtoms___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenAtoms___closed__3;
static const lean_closure_object lp_ttc_Ttc_degenAtoms___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_ttc_Ttc_degenAtoms___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_ttc_Ttc_degenAtoms___closed__4 = (const lean_object*)&lp_ttc_Ttc_degenAtoms___closed__4_value;
static lean_once_cell_t lp_ttc_Ttc_degenAtoms___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenAtoms___closed__5;
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___boxed(lean_object*);
static lean_once_cell_t lp_ttc_Ttc_degenCube___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenCube___closed__0;
static lean_once_cell_t lp_ttc_Ttc_degenCube___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenCube___closed__1;
static lean_once_cell_t lp_ttc_Ttc_degenCube___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenCube___closed__2;
static lean_once_cell_t lp_ttc_Ttc_degenCube___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenCube___closed__3;
static lean_once_cell_t lp_ttc_Ttc_degenCube___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenCube___closed__4;
static lean_once_cell_t lp_ttc_Ttc_degenCube___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenCube___closed__5;
static lean_once_cell_t lp_ttc_Ttc_degenCube___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenCube___closed__6;
static lean_once_cell_t lp_ttc_Ttc_degenCube___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenCube___closed__7;
static lean_once_cell_t lp_ttc_Ttc_degenCube___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenCube___closed__8;
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenCube;
static lean_once_cell_t lp_ttc_Ttc_degenDNF___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenDNF___closed__0;
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenDNF;
static lean_once_cell_t lp_ttc_Ttc_degenForm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenForm___closed__0;
static lean_once_cell_t lp_ttc_Ttc_degenForm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenForm___closed__1;
static lean_once_cell_t lp_ttc_Ttc_degenForm___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenForm___closed__2;
static lean_once_cell_t lp_ttc_Ttc_degenForm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenForm___closed__3;
static lean_once_cell_t lp_ttc_Ttc_degenForm___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_degenForm___closed__4;
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenForm;
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__0(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__0___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_ttc_Ttc_degenAtoms___lam__0(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenAtoms___lam__1___closed__0(void){
_start:
{
lean_object* v___x_5_; lean_object* v___f_6_; 
v___x_5_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_6_, 0, v___x_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__1(lean_object* v_x_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = lean_obj_once(&lp_ttc_Ttc_degenAtoms___lam__1___closed__0, &lp_ttc_Ttc_degenAtoms___lam__1___closed__0_once, _init_lp_ttc_Ttc_degenAtoms___lam__1___closed__0);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__1___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_ttc_Ttc_degenAtoms___lam__1(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__2(lean_object* v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___lam__2___boxed(lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_ttc_Ttc_degenAtoms___lam__2(v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenAtoms___closed__1(void){
_start:
{
lean_object* v___x_16_; lean_object* v___f_17_; lean_object* v___x_18_; 
v___x_16_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_17_ = ((lean_object*)(lp_ttc_Ttc_degenAtoms___closed__0));
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___f_17_);
lean_ctor_set(v___x_18_, 1, v___x_16_);
return v___x_18_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenAtoms___closed__3(void){
_start:
{
lean_object* v___x_20_; lean_object* v___f_21_; lean_object* v___x_22_; 
v___x_20_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_21_ = ((lean_object*)(lp_ttc_Ttc_degenAtoms___closed__2));
v___x_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_22_, 0, v___f_21_);
lean_ctor_set(v___x_22_, 1, v___x_20_);
return v___x_22_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenAtoms___closed__5(void){
_start:
{
lean_object* v___x_24_; lean_object* v___f_25_; lean_object* v___x_26_; 
v___x_24_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_25_ = ((lean_object*)(lp_ttc_Ttc_degenAtoms___closed__4));
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___f_25_);
lean_ctor_set(v___x_26_, 1, v___x_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms(lean_object* v_x_27_){
_start:
{
lean_object* v_zero_28_; uint8_t v_isZero_29_; 
v_zero_28_ = lean_unsigned_to_nat(0u);
v_isZero_29_ = lean_nat_dec_eq(v_x_27_, v_zero_28_);
if (v_isZero_29_ == 1)
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&lp_ttc_Ttc_degenAtoms___closed__1, &lp_ttc_Ttc_degenAtoms___closed__1_once, _init_lp_ttc_Ttc_degenAtoms___closed__1);
return v___x_30_;
}
else
{
lean_object* v_one_31_; lean_object* v_n_32_; uint8_t v_isZero_33_; 
v_one_31_ = lean_unsigned_to_nat(1u);
v_n_32_ = lean_nat_sub(v_x_27_, v_one_31_);
v_isZero_33_ = lean_nat_dec_eq(v_n_32_, v_zero_28_);
if (v_isZero_33_ == 1)
{
lean_object* v___x_34_; 
lean_dec(v_n_32_);
v___x_34_ = lean_obj_once(&lp_ttc_Ttc_degenAtoms___closed__3, &lp_ttc_Ttc_degenAtoms___closed__3_once, _init_lp_ttc_Ttc_degenAtoms___closed__3);
return v___x_34_;
}
else
{
lean_object* v_n_35_; uint8_t v_isZero_36_; lean_object* v___x_37_; 
v_n_35_ = lean_nat_sub(v_n_32_, v_one_31_);
lean_dec(v_n_32_);
v_isZero_36_ = lean_nat_dec_eq(v_n_35_, v_zero_28_);
lean_dec(v_n_35_);
v___x_37_ = lean_obj_once(&lp_ttc_Ttc_degenAtoms___closed__5, &lp_ttc_Ttc_degenAtoms___closed__5_once, _init_lp_ttc_Ttc_degenAtoms___closed__5);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_degenAtoms___boxed(lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_ttc_Ttc_degenAtoms(v_x_38_);
lean_dec(v_x_38_);
return v_res_39_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube___closed__0(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_unsigned_to_nat(3u);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_nat_mod(v___x_41_, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube___closed__1(void){
_start:
{
uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = 1;
v___x_44_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__0, &lp_ttc_Ttc_degenCube___closed__0_once, _init_lp_ttc_Ttc_degenCube___closed__0);
v___x_45_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*1, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube___closed__2(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(3u);
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_mod(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube___closed__3(void){
_start:
{
uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = 1;
v___x_50_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__2, &lp_ttc_Ttc_degenCube___closed__2_once, _init_lp_ttc_Ttc_degenCube___closed__2);
v___x_51_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*1, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube___closed__4(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_unsigned_to_nat(3u);
v___x_53_ = lean_unsigned_to_nat(2u);
v___x_54_ = lean_nat_mod(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube___closed__5(void){
_start:
{
uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = 1;
v___x_56_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__4, &lp_ttc_Ttc_degenCube___closed__4_once, _init_lp_ttc_Ttc_degenCube___closed__4);
v___x_57_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*1, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube___closed__6(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_box(0);
v___x_59_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__5, &lp_ttc_Ttc_degenCube___closed__5_once, _init_lp_ttc_Ttc_degenCube___closed__5);
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube___closed__7(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__6, &lp_ttc_Ttc_degenCube___closed__6_once, _init_lp_ttc_Ttc_degenCube___closed__6);
v___x_62_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__3, &lp_ttc_Ttc_degenCube___closed__3_once, _init_lp_ttc_Ttc_degenCube___closed__3);
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube___closed__8(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__7, &lp_ttc_Ttc_degenCube___closed__7_once, _init_lp_ttc_Ttc_degenCube___closed__7);
v___x_65_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__1, &lp_ttc_Ttc_degenCube___closed__1_once, _init_lp_ttc_Ttc_degenCube___closed__1);
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenCube(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__8, &lp_ttc_Ttc_degenCube___closed__8_once, _init_lp_ttc_Ttc_degenCube___closed__8);
return v___x_67_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenDNF___closed__0(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_box(0);
v___x_69_ = lp_ttc_Ttc_degenCube;
v___x_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenDNF(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_obj_once(&lp_ttc_Ttc_degenDNF___closed__0, &lp_ttc_Ttc_degenDNF___closed__0_once, _init_lp_ttc_Ttc_degenDNF___closed__0);
return v___x_71_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenForm___closed__0(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__0, &lp_ttc_Ttc_degenCube___closed__0_once, _init_lp_ttc_Ttc_degenCube___closed__0);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenForm___closed__1(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__2, &lp_ttc_Ttc_degenCube___closed__2_once, _init_lp_ttc_Ttc_degenCube___closed__2);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenForm___closed__2(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&lp_ttc_Ttc_degenForm___closed__1, &lp_ttc_Ttc_degenForm___closed__1_once, _init_lp_ttc_Ttc_degenForm___closed__1);
v___x_77_ = lean_obj_once(&lp_ttc_Ttc_degenForm___closed__0, &lp_ttc_Ttc_degenForm___closed__0_once, _init_lp_ttc_Ttc_degenForm___closed__0);
v___x_78_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenForm___closed__3(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_obj_once(&lp_ttc_Ttc_degenCube___closed__4, &lp_ttc_Ttc_degenCube___closed__4_once, _init_lp_ttc_Ttc_degenCube___closed__4);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenForm___closed__4(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&lp_ttc_Ttc_degenForm___closed__3, &lp_ttc_Ttc_degenForm___closed__3_once, _init_lp_ttc_Ttc_degenForm___closed__3);
v___x_82_ = lean_obj_once(&lp_ttc_Ttc_degenForm___closed__2, &lp_ttc_Ttc_degenForm___closed__2_once, _init_lp_ttc_Ttc_degenForm___closed__2);
v___x_83_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_lp_ttc_Ttc_degenForm(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_obj_once(&lp_ttc_Ttc_degenForm___closed__4, &lp_ttc_Ttc_degenForm___closed__4_once, _init_lp_ttc_Ttc_degenForm___closed__4);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter___redArg(lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_, lean_object* v_h__3_88_){
_start:
{
lean_object* v_zero_89_; uint8_t v_isZero_90_; 
v_zero_89_ = lean_unsigned_to_nat(0u);
v_isZero_90_ = lean_nat_dec_eq(v_x_85_, v_zero_89_);
if (v_isZero_90_ == 1)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__3_88_);
lean_dec(v_h__2_87_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__1_86_, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_one_93_; lean_object* v_n_94_; uint8_t v_isZero_95_; 
lean_dec(v_h__1_86_);
v_one_93_ = lean_unsigned_to_nat(1u);
v_n_94_ = lean_nat_sub(v_x_85_, v_one_93_);
v_isZero_95_ = lean_nat_dec_eq(v_n_94_, v_zero_89_);
if (v_isZero_95_ == 1)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_n_94_);
lean_dec(v_h__3_88_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_apply_1(v_h__2_87_, v___x_96_);
return v___x_97_;
}
else
{
lean_object* v_n_98_; uint8_t v_isZero_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_h__2_87_);
v_n_98_ = lean_nat_sub(v_n_94_, v_one_93_);
lean_dec(v_n_94_);
v_isZero_99_ = lean_nat_dec_eq(v_n_98_, v_zero_89_);
lean_dec(v_n_98_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_apply_1(v_h__3_88_, v___x_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter___redArg___boxed(lean_object* v_x_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_, lean_object* v_h__3_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter___redArg(v_x_102_, v_h__1_103_, v_h__2_104_, v_h__3_105_);
lean_dec(v_x_102_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter(lean_object* v_motive_107_, lean_object* v_x_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_, lean_object* v_h__3_111_){
_start:
{
lean_object* v_zero_112_; uint8_t v_isZero_113_; 
v_zero_112_ = lean_unsigned_to_nat(0u);
v_isZero_113_ = lean_nat_dec_eq(v_x_108_, v_zero_112_);
if (v_isZero_113_ == 1)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_h__3_111_);
lean_dec(v_h__2_110_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_apply_1(v_h__1_109_, v___x_114_);
return v___x_115_;
}
else
{
lean_object* v_one_116_; lean_object* v_n_117_; uint8_t v_isZero_118_; 
lean_dec(v_h__1_109_);
v_one_116_ = lean_unsigned_to_nat(1u);
v_n_117_ = lean_nat_sub(v_x_108_, v_one_116_);
v_isZero_118_ = lean_nat_dec_eq(v_n_117_, v_zero_112_);
if (v_isZero_118_ == 1)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v_n_117_);
lean_dec(v_h__3_111_);
v___x_119_ = lean_box(0);
v___x_120_ = lean_apply_1(v_h__2_110_, v___x_119_);
return v___x_120_;
}
else
{
lean_object* v_n_121_; uint8_t v_isZero_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_h__2_110_);
v_n_121_ = lean_nat_sub(v_n_117_, v_one_116_);
lean_dec(v_n_117_);
v_isZero_122_ = lean_nat_dec_eq(v_n_121_, v_zero_112_);
lean_dec(v_n_121_);
v___x_123_ = lean_box(0);
v___x_124_ = lean_apply_1(v_h__3_111_, v___x_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter___boxed(lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_, lean_object* v_h__3_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = lp_ttc___private_Ttc_Exec_Geometry_0__Ttc_degenAtoms_match__1_splitter(v_motive_125_, v_x_126_, v_h__1_127_, v_h__2_128_, v_h__3_129_);
lean_dec(v_x_126_);
return v_res_130_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Lattice_Decomposition(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Model_ProblemSetting(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Lattice_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Convex_Measure(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_EqHaar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_Geometry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Lattice_Decomposition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Model_ProblemSetting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Lattice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Convex_Measure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Lebesgue_EqHaar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_ttc_Ttc_degenCube = _init_lp_ttc_Ttc_degenCube();
lean_mark_persistent(lp_ttc_Ttc_degenCube);
lp_ttc_Ttc_degenDNF = _init_lp_ttc_Ttc_degenDNF();
lean_mark_persistent(lp_ttc_Ttc_degenDNF);
lp_ttc_Ttc_degenForm = _init_lp_ttc_Ttc_degenForm();
lean_mark_persistent(lp_ttc_Ttc_degenForm);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
