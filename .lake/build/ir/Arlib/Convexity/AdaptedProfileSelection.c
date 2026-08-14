// Lean compiler output
// Module: Arlib.Convexity.AdaptedProfileSelection
// Imports: public import Init public meta import Init public import Arlib.Convexity.AffineProfileCut public import Arlib.Topology.HamSandwich
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
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00modelWithCornersEuclideanQuadrant_spec__0(lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__0 = (const lean_object*)&lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__0_value;
static const lean_closure_object lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__1 = (const lean_object*)&lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__1_value;
static const lean_ctor_object lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__0_value),((lean_object*)&lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__1_value)}};
static const lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__2 = (const lean_object*)&lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0___boxed(lean_object*);
static lean_once_cell_t lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__0;
static const lean_closure_object lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__1 = (const lean_object*)&lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__1_value;
static lean_once_cell_t lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__2;
static lean_once_cell_t lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__3;
LEAN_EXPORT lean_object* lp_ttc_Arlib_pullEuclideanLinear___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_pullEuclideanLinear(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Arlib_pullEuclideanLinear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg___lam__0(lean_object* v_invFun_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_invFun_1_, v___y_2_, v___y_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4___redArg(lean_object* v_self_5_){
_start:
{
lean_object* v_toLinearMap_6_; lean_object* v_invFun_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_14_; 
v_toLinearMap_6_ = lean_ctor_get(v_self_5_, 0);
v_invFun_7_ = lean_ctor_get(v_self_5_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_self_5_);
if (v_isSharedCheck_14_ == 0)
{
v___x_9_ = v_self_5_;
v_isShared_10_ = v_isSharedCheck_14_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_invFun_7_);
lean_inc(v_toLinearMap_6_);
lean_dec(v_self_5_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_14_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_12_; 
if (v_isShared_10_ == 0)
{
v___x_12_ = v___x_9_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_toLinearMap_6_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_invFun_7_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg(lean_object* v_00_u03c3_15_, lean_object* v_00_u03c3_x27_16_, lean_object* v_e_17_){
_start:
{
lean_object* v_invFun_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_invFun_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_29_; 
v_invFun_18_ = lean_ctor_get(v_e_17_, 1);
lean_inc(v_invFun_18_);
v___x_19_ = lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4___redArg(v_e_17_);
v___x_20_ = lp_mathlib_Equiv_symm___redArg(v___x_19_);
v_invFun_21_ = lean_ctor_get(v___x_20_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_29_ == 0)
{
lean_object* v_unused_30_; 
v_unused_30_ = lean_ctor_get(v___x_20_, 0);
lean_dec(v_unused_30_);
v___x_23_ = v___x_20_;
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_invFun_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___f_25_; lean_object* v___x_27_; 
v___f_25_ = lean_alloc_closure((void*)(lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_25_, 0, v_invFun_18_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v___f_25_);
v___x_27_ = v___x_23_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___f_25_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_invFun_21_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg___boxed(lean_object* v_00_u03c3_31_, lean_object* v_00_u03c3_x27_32_, lean_object* v_e_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg(v_00_u03c3_31_, v_00_u03c3_x27_32_, v_e_33_);
lean_dec(v_00_u03c3_x27_32_);
lean_dec(v_00_u03c3_31_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___lam__1(lean_object* v_ofLp_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_apply_1(v_ofLp_35_, v___y_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___lam__0(lean_object* v_self_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_apply_1(v_self_38_, v___y_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0(lean_object* v_p_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = ((lean_object*)(lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___closed__2));
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0___boxed(lean_object* v_p_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0(v_p_48_);
lean_dec(v_p_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_ttc_WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0(lean_object* v_p_50_){
_start:
{
lean_object* v___x_51_; lean_object* v_toFun_52_; lean_object* v_invFun_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v___x_51_ = lp_ttc_WithLp_addEquiv___at___00WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0_spec__0(v_p_50_);
v_toFun_52_ = lean_ctor_get(v___x_51_, 0);
v_invFun_53_ = lean_ctor_get(v___x_51_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_51_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_invFun_53_);
lean_inc(v_toFun_52_);
lean_dec(v___x_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_toFun_52_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_invFun_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0___boxed(lean_object* v_p_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_ttc_WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0(v_p_61_);
lean_dec(v_p_61_);
return v_res_62_;
}
}
static lean_object* _init_lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__0(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(2u);
v___x_64_ = lp_mathlib_Nat_cast___at___00modelWithCornersEuclideanQuadrant_spec__0(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__2(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_obj_once(&lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__0, &lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__0_once, _init_lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__0);
v___x_67_ = lp_ttc_WithLp_linearEquiv___at___00Arlib_pullEuclideanLinear_spec__0(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___f_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__2, &lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__2_once, _init_lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__2);
v___f_69_ = ((lean_object*)(lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__1));
v___x_70_ = lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg(v___f_69_, v___f_69_, v___x_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_pullEuclideanLinear___redArg(lean_object* v_L_71_){
_start:
{
lean_object* v___x_72_; lean_object* v_toLinearMap_73_; lean_object* v___f_74_; 
v___x_72_ = lean_obj_once(&lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__3, &lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__3_once, _init_lp_ttc_Arlib_pullEuclideanLinear___redArg___closed__3);
v_toLinearMap_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_toLinearMap_73_);
v___f_74_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_74_, 0, v_toLinearMap_73_);
lean_closure_set(v___f_74_, 1, v_L_71_);
return v___f_74_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_pullEuclideanLinear(lean_object* v_m_75_, lean_object* v_L_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lp_ttc_Arlib_pullEuclideanLinear___redArg(v_L_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Arlib_pullEuclideanLinear___boxed(lean_object* v_m_78_, lean_object* v_L_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_ttc_Arlib_pullEuclideanLinear(v_m_78_, v_L_79_);
lean_dec(v_m_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2___redArg(lean_object* v_g_81_){
_start:
{
lean_inc(v_g_81_);
return v_g_81_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2___redArg___boxed(lean_object* v_g_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2___redArg(v_g_82_);
lean_dec(v_g_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2(lean_object* v_00_u03c3_84_, lean_object* v_00_u03c3_x27_85_, lean_object* v_inst_86_, lean_object* v_f_87_, lean_object* v_g_88_, lean_object* v_h_u2081_89_, lean_object* v_h_u2082_90_){
_start:
{
lean_inc(v_g_88_);
return v_g_88_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2___boxed(lean_object* v_00_u03c3_91_, lean_object* v_00_u03c3_x27_92_, lean_object* v_inst_93_, lean_object* v_f_94_, lean_object* v_g_95_, lean_object* v_h_u2081_96_, lean_object* v_h_u2082_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_ttc_LinearMap_inverse___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__2(v_00_u03c3_91_, v_00_u03c3_x27_92_, v_inst_93_, v_f_94_, v_g_95_, v_h_u2081_96_, v_h_u2082_97_);
lean_dec(v_g_95_);
lean_dec(v_f_94_);
lean_dec(v_00_u03c3_x27_92_);
lean_dec(v_00_u03c3_91_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1(lean_object* v_00_u03c3_99_, lean_object* v_00_u03c3_x27_100_, lean_object* v_re_u2081_101_, lean_object* v_re_u2082_102_, lean_object* v_e_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___redArg(v_00_u03c3_99_, v_00_u03c3_x27_100_, v_e_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1___boxed(lean_object* v_00_u03c3_105_, lean_object* v_00_u03c3_x27_106_, lean_object* v_re_u2081_107_, lean_object* v_re_u2082_108_, lean_object* v_e_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_ttc_LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1(v_00_u03c3_105_, v_00_u03c3_x27_106_, v_re_u2081_107_, v_re_u2082_108_, v_e_109_);
lean_dec(v_00_u03c3_x27_106_);
lean_dec(v_00_u03c3_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4(lean_object* v_00_u03c3_111_, lean_object* v_00_u03c3_x27_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_self_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4___redArg(v_self_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03c3_117_, lean_object* v_00_u03c3_x27_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_self_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4(v_00_u03c3_117_, v_00_u03c3_x27_118_, v_inst_119_, v_inst_120_, v_self_121_);
lean_dec(v_00_u03c3_x27_118_);
lean_dec(v_00_u03c3_117_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3___redArg(lean_object* v_00_u03c3_123_, lean_object* v_00_u03c3_x27_124_, lean_object* v_e_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4___redArg(v_e_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3___redArg___boxed(lean_object* v_00_u03c3_127_, lean_object* v_00_u03c3_x27_128_, lean_object* v_e_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3___redArg(v_00_u03c3_127_, v_00_u03c3_x27_128_, v_e_129_);
lean_dec(v_00_u03c3_x27_128_);
lean_dec(v_00_u03c3_127_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3(lean_object* v_00_u03c3_131_, lean_object* v_00_u03c3_x27_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_e_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lp_ttc_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3_spec__4___redArg(v_e_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3___boxed(lean_object* v_00_u03c3_137_, lean_object* v_00_u03c3_x27_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_e_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = lp_ttc_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Arlib_pullEuclideanLinear_spec__1_spec__3(v_00_u03c3_137_, v_00_u03c3_x27_138_, v_inst_139_, v_inst_140_, v_e_141_);
lean_dec(v_00_u03c3_x27_138_);
lean_dec(v_00_u03c3_137_);
return v_res_142_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Convexity_AffineProfileCut(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Topology_HamSandwich(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Convexity_AdaptedProfileSelection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Convexity_AffineProfileCut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Topology_HamSandwich(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
