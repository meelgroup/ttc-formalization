// Lean compiler output
// Module: Ttc.Exec.RuntimeMN4
// Imports: public import Init public meta import Init public import Ttc.Exec.PolyAccuracy public import Ttc.Exec.PricedHeadline
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lp_mathlib_Lean_Elab_throwUnsupportedSyntax___at___00elabSuppressCompilationDecl_spec__0___redArg();
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lp_mathlib_Lean_logInfo___at___00Mathlib_CrossRef_traceCrossRefs_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___closed__0 = (const lean_object*)&lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___closed__0_value;
static const lean_ctor_object lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___closed__0_value)}};
static const lean_object* lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___closed__1 = (const lean_object*)&lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___closed__1_value;
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux(lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___boxed(lean_object*);
static const lean_string_object lp_ttc_command_x23binderProfile___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "command#binderProfile_"};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__0 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__0_value;
static const lean_ctor_object lp_ttc_command_x23binderProfile___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 230, 147, 5, 140, 158, 129, 28)}};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__1 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__1_value;
static const lean_string_object lp_ttc_command_x23binderProfile___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__2 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__2_value;
static const lean_ctor_object lp_ttc_command_x23binderProfile___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__3 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__3_value;
static const lean_string_object lp_ttc_command_x23binderProfile___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "#binderProfile "};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__4 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__4_value;
static const lean_ctor_object lp_ttc_command_x23binderProfile___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__4_value)}};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__5 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__5_value;
static const lean_string_object lp_ttc_command_x23binderProfile___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__6 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__6_value;
static const lean_ctor_object lp_ttc_command_x23binderProfile___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__7 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__7_value;
static const lean_ctor_object lp_ttc_command_x23binderProfile___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__7_value)}};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__8 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__8_value;
static const lean_ctor_object lp_ttc_command_x23binderProfile___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__3_value),((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__5_value),((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__8_value)}};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__9 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__9_value;
static const lean_ctor_object lp_ttc_command_x23binderProfile___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&lp_ttc_command_x23binderProfile___00__closed__9_value)}};
static const lean_object* lp_ttc_command_x23binderProfile___00__closed__10 = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__10_value;
LEAN_EXPORT const lean_object* lp_ttc_command_x23binderProfile__ = (const lean_object*)&lp_ttc_command_x23binderProfile___00__closed__10_value;
static const lean_string_object lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__0 = (const lean_object*)&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__0_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__1;
static const lean_string_object lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 17, .m_data = " raw ∀-binders = "};
static const lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__2 = (const lean_object*)&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__2_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__3;
static const lean_string_object lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " explicit + "};
static const lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__4 = (const lean_object*)&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__4_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__5;
static const lean_string_object lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " implicit + "};
static const lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__6 = (const lean_object*)&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__6_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__7;
static const lean_string_object lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " instance"};
static const lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__8 = (const lean_object*)&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__8_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__9;
static const lean_string_object lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not found: "};
static const lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__10 = (const lean_object*)&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__10_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__11;
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux(lean_object* v_x_6_){
_start:
{
if (lean_obj_tag(v_x_6_) == 7)
{
lean_object* v_body_7_; uint8_t v_binderInfo_8_; lean_object* v___x_9_; lean_object* v_snd_10_; 
v_body_7_ = lean_ctor_get(v_x_6_, 2);
v_binderInfo_8_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*3 + 8);
v___x_9_ = lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux(v_body_7_);
v_snd_10_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_snd_10_);
switch(v_binderInfo_8_)
{
case 0:
{
lean_object* v_fst_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_20_; 
v_fst_11_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_20_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_20_ == 0)
{
lean_object* v_unused_21_; 
v_unused_21_ = lean_ctor_get(v___x_9_, 1);
lean_dec(v_unused_21_);
v___x_13_ = v___x_9_;
v_isShared_14_ = v_isSharedCheck_20_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_fst_11_);
lean_dec(v___x_9_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_20_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_18_; 
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_add(v_fst_11_, v___x_15_);
lean_dec(v_fst_11_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_16_);
v___x_18_ = v___x_13_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v___x_16_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_snd_10_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
}
case 3:
{
lean_object* v_fst_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_40_; 
v_fst_22_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_40_ == 0)
{
lean_object* v_unused_41_; 
v_unused_41_ = lean_ctor_get(v___x_9_, 1);
lean_dec(v_unused_41_);
v___x_24_ = v___x_9_;
v_isShared_25_ = v_isSharedCheck_40_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_fst_22_);
lean_dec(v___x_9_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_40_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v_fst_26_; lean_object* v_snd_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_39_; 
v_fst_26_ = lean_ctor_get(v_snd_10_, 0);
v_snd_27_ = lean_ctor_get(v_snd_10_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v_snd_10_);
if (v_isSharedCheck_39_ == 0)
{
v___x_29_ = v_snd_10_;
v_isShared_30_ = v_isSharedCheck_39_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_snd_27_);
lean_inc(v_fst_26_);
lean_dec(v_snd_10_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_39_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_add(v_snd_27_, v___x_31_);
lean_dec(v_snd_27_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v___x_32_);
v___x_34_ = v___x_29_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_fst_26_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v___x_32_);
v___x_34_ = v_reuseFailAlloc_38_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_36_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v___x_34_);
v___x_36_ = v___x_24_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_fst_22_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
default: 
{
lean_object* v_fst_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_60_; 
v_fst_42_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_60_ == 0)
{
lean_object* v_unused_61_; 
v_unused_61_ = lean_ctor_get(v___x_9_, 1);
lean_dec(v_unused_61_);
v___x_44_ = v___x_9_;
v_isShared_45_ = v_isSharedCheck_60_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_fst_42_);
lean_dec(v___x_9_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_60_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_59_; 
v_fst_46_ = lean_ctor_get(v_snd_10_, 0);
v_snd_47_ = lean_ctor_get(v_snd_10_, 1);
v_isSharedCheck_59_ = !lean_is_exclusive(v_snd_10_);
if (v_isSharedCheck_59_ == 0)
{
v___x_49_ = v_snd_10_;
v_isShared_50_ = v_isSharedCheck_59_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_snd_47_);
lean_inc(v_fst_46_);
lean_dec(v_snd_10_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_59_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_51_ = lean_unsigned_to_nat(1u);
v___x_52_ = lean_nat_add(v_fst_46_, v___x_51_);
lean_dec(v_fst_46_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_52_);
v___x_54_ = v___x_49_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_snd_47_);
v___x_54_ = v_reuseFailAlloc_58_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_56_; 
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___x_54_);
v___x_56_ = v___x_44_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_fst_42_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v___x_54_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_62_; 
v___x_62_ = ((lean_object*)(lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___closed__1));
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux___boxed(lean_object* v_x_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux(v_x_63_);
lean_dec_ref(v_x_63_);
return v_res_64_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__1(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__0));
v___x_90_ = l_Lean_stringToMessageData(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__3(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__2));
v___x_93_ = l_Lean_stringToMessageData(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__5(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__4));
v___x_96_ = l_Lean_stringToMessageData(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__7(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__6));
v___x_99_ = l_Lean_stringToMessageData(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__9(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__8));
v___x_102_ = l_Lean_stringToMessageData(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__11(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__10));
v___x_105_ = l_Lean_stringToMessageData(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1(lean_object* v_x_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(lp_ttc_command_x23binderProfile___00__closed__1));
lean_inc(v_x_106_);
v___x_111_ = l_Lean_Syntax_isOfKind(v_x_106_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
lean_dec(v_x_106_);
v___x_112_ = lp_mathlib_Lean_Elab_throwUnsupportedSyntax___at___00elabSuppressCompilationDecl_spec__0___redArg();
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_113_ = lean_st_ref_get(v_a_108_);
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = l_Lean_Syntax_getArg(v_x_106_, v___x_114_);
lean_dec(v_x_106_);
v___x_116_ = lean_alloc_closure((void*)(l_Lean_realizeGlobalConstNoOverload___boxed), 4, 1);
lean_closure_set(v___x_116_, 0, v___x_115_);
v___x_117_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_116_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v_env_119_; uint8_t v___x_120_; lean_object* v___x_121_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc_n(v_a_118_, 2);
lean_dec_ref_known(v___x_117_, 1);
v_env_119_ = lean_ctor_get(v___x_113_, 0);
lean_inc_ref(v_env_119_);
lean_dec(v___x_113_);
v___x_120_ = 0;
v___x_121_ = l_Lean_Environment_find_x3f(v_env_119_, v_a_118_, v___x_120_);
if (lean_obj_tag(v___x_121_) == 1)
{
lean_object* v_val_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_176_; 
v_val_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_176_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_176_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_val_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_176_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v_snd_128_; lean_object* v_fst_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_175_; 
v___x_126_ = l_Lean_ConstantInfo_type(v_val_122_);
lean_dec(v_val_122_);
v___x_127_ = lp_ttc___private_Ttc_Exec_RuntimeMN4_0__Ttc_Audit_binderProfileAux(v___x_126_);
lean_dec_ref(v___x_126_);
v_snd_128_ = lean_ctor_get(v___x_127_, 1);
v_fst_129_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_175_ == 0)
{
v___x_131_ = v___x_127_;
v_isShared_132_ = v_isSharedCheck_175_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_snd_128_);
lean_inc(v_fst_129_);
lean_dec(v___x_127_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_175_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_fst_133_; lean_object* v_snd_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_174_; 
v_fst_133_ = lean_ctor_get(v_snd_128_, 0);
v_snd_134_ = lean_ctor_get(v_snd_128_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_snd_128_);
if (v_isSharedCheck_174_ == 0)
{
v___x_136_ = v_snd_128_;
v_isShared_137_ = v_isSharedCheck_174_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_snd_134_);
lean_inc(v_fst_133_);
lean_dec(v_snd_128_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_174_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_138_ = l_Lean_MessageData_ofName(v_a_118_);
v___x_139_ = lean_obj_once(&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__1, &lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__1_once, _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__1);
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 7);
lean_ctor_set(v___x_136_, 1, v___x_139_);
lean_ctor_set(v___x_136_, 0, v___x_138_);
v___x_141_ = v___x_136_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_173_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_142_ = lean_nat_add(v_fst_129_, v_fst_133_);
v___x_143_ = lean_nat_add(v___x_142_, v_snd_134_);
lean_dec(v___x_142_);
v___x_144_ = l_Nat_reprFast(v___x_143_);
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 3);
lean_ctor_set(v___x_124_, 0, v___x_144_);
v___x_146_ = v___x_124_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_172_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = l_Lean_MessageData_ofFormat(v___x_146_);
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 7);
lean_ctor_set(v___x_131_, 1, v___x_147_);
lean_ctor_set(v___x_131_, 0, v___x_141_);
v___x_149_ = v___x_131_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_171_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_150_ = lean_obj_once(&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__3, &lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__3_once, _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__3);
v___x_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = l_Nat_reprFast(v_fst_129_);
v___x_153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
v___x_154_ = l_Lean_MessageData_ofFormat(v___x_153_);
v___x_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_151_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_obj_once(&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__5, &lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__5_once, _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__5);
v___x_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = l_Nat_reprFast(v_fst_133_);
v___x_159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___x_160_ = l_Lean_MessageData_ofFormat(v___x_159_);
v___x_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_157_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_obj_once(&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__7, &lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__7_once, _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__7);
v___x_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Nat_reprFast(v_snd_134_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = l_Lean_MessageData_ofFormat(v___x_165_);
v___x_167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_163_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_obj_once(&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__9, &lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__9_once, _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__9);
v___x_169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = lp_mathlib_Lean_logInfo___at___00Mathlib_CrossRef_traceCrossRefs_spec__1(v___x_169_, v_a_107_, v_a_108_);
return v___x_170_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v___x_121_);
v___x_177_ = lean_obj_once(&lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__11, &lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__11_once, _init_lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___closed__11);
v___x_178_ = l_Lean_MessageData_ofName(v_a_118_);
v___x_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(v___x_179_, v_a_107_, v_a_108_);
return v___x_180_;
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec(v___x_113_);
v_a_181_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_117_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_117_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1___boxed(lean_object* v_x_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = lp_ttc___aux__Ttc__Exec__RuntimeMN4______elabRules__command_x23binderProfile____1(v_x_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
return v_res_193_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_PolyAccuracy(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_PricedHeadline(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_RuntimeMN4(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_PolyAccuracy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_PricedHeadline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
