// Lean compiler output
// Module: Ttc.Audit.ClosureCheck
// Imports: public import Init public meta import Init public import Ttc.Model.Pseudocode public import Ttc.Model.Theorem
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lp_mathlib_List_any___at___00Mathlib_Linter_directoryDependencyCheck_spec__10(lean_object*, lean_object*);
lean_object* lp_importGraph_Lean_Environment_getModuleFor_x3f(lean_object*, lean_object*);
lean_object* lp_mathlib_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Mathlib_Tactic_Linter_UpstreamableDecl_0__Lean_Environment_localDefinitionDependencies_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lp_mathlib_Lean_Elab_throwUnsupportedSyntax___at___00elabSuppressCompilationDecl_spec__0___redArg();
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_MutualInductive_0__Lean_Elab_Command_withElaboratedHeaders_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lp_mathlib_Std_DTreeMap_Internal_Impl_erase___at___00__private_Mathlib_Tactic_Linter_MinImports_0__Mathlib_Linter_MinImports_minImportsLinter_spec__2___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Lean_logInfo___at___00Mathlib_CrossRef_traceCrossRefs_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
static const lean_string_object lp_ttc_Ttc_Audit_forbidden___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ttc"};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__0 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbidden___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TtcProb"};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__1 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__1_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__2_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__1_value),LEAN_SCALAR_PTR_LITERAL(146, 200, 237, 232, 32, 106, 68, 121)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__2 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__2_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbidden___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Oracles"};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__3 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__3_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__4_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__3_value),LEAN_SCALAR_PTR_LITERAL(31, 46, 185, 62, 251, 206, 147, 68)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__4 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__4_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbidden___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trajLaw"};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__5 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__5_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__6_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__5_value),LEAN_SCALAR_PTR_LITERAL(163, 122, 236, 97, 166, 136, 11, 130)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__6 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__6_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbidden___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "trajOracles"};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__7 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__7_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__8_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__7_value),LEAN_SCALAR_PTR_LITERAL(147, 38, 16, 48, 57, 170, 231, 92)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__8 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__8_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbidden___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "totalRate"};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__9 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__9_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__10_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__9_value),LEAN_SCALAR_PTR_LITERAL(237, 28, 115, 235, 9, 129, 67, 55)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__10 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__10_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbidden___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MonteCarlo"};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__11 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__11_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__12_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 35, 196, 51, 196, 0, 152, 217)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__12 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__12_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbidden___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "TtcAnalysis"};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__13 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__13_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__14_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__13_value),LEAN_SCALAR_PTR_LITERAL(88, 86, 245, 226, 228, 96, 119, 55)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__14 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__14_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbidden___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "run"};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__15 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__15_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__16_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__15_value),LEAN_SCALAR_PTR_LITERAL(167, 52, 23, 66, 190, 253, 75, 228)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__16 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__16_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__17 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__17_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__14_value),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__17_value)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__18 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__18_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__12_value),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__18_value)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__19 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__19_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__10_value),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__19_value)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__20 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__20_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__8_value),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__20_value)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__21 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__21_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__6_value),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__21_value)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__22 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__22_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__4_value),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__22_value)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__23 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__23_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbidden___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__2_value),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__23_value)}};
static const lean_object* lp_ttc_Ttc_Audit_forbidden___closed__24 = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__24_value;
LEAN_EXPORT const lean_object* lp_ttc_Ttc_Audit_forbidden = (const lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__24_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbiddenModules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Coupling"};
static const lean_object* lp_ttc_Ttc_Audit_forbiddenModules___closed__0 = (const lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__0_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbiddenModules___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbiddenModules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__1_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 234, 180, 106, 106, 241, 235, 209)}};
static const lean_object* lp_ttc_Ttc_Audit_forbiddenModules___closed__1 = (const lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__1_value;
static const lean_string_object lp_ttc_Ttc_Audit_forbiddenModules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Process"};
static const lean_object* lp_ttc_Ttc_Audit_forbiddenModules___closed__2 = (const lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__2_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbiddenModules___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_forbiddenModules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__3_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__2_value),LEAN_SCALAR_PTR_LITERAL(104, 23, 17, 35, 21, 136, 147, 59)}};
static const lean_object* lp_ttc_Ttc_Audit_forbiddenModules___closed__3 = (const lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__3_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbiddenModules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_ttc_Ttc_Audit_forbiddenModules___closed__4 = (const lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__4_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_forbiddenModules___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__1_value),((lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__4_value)}};
static const lean_object* lp_ttc_Ttc_Audit_forbiddenModules___closed__5 = (const lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__5_value;
LEAN_EXPORT const lean_object* lp_ttc_Ttc_Audit_forbiddenModules = (const lean_object*)&lp_ttc_Ttc_Audit_forbiddenModules___closed__5_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_closureAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_object* lp_ttc_Ttc_Audit_closureAux___closed__0 = (const lean_object*)&lp_ttc_Ttc_Audit_closureAux___closed__0_value;
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_closureAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_List_filterTR_loop___at___00Ttc_Audit_forbiddenIn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_forbiddenIn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_forbiddenIn___boxed(lean_object*, lean_object*);
static const lean_string_object lp_ttc_command_x23closure___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "command#closure_"};
static const lean_object* lp_ttc_command_x23closure___00__closed__0 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__0_value;
static const lean_ctor_object lp_ttc_command_x23closure___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closure___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 146, 40, 71, 6, 218, 177, 160)}};
static const lean_object* lp_ttc_command_x23closure___00__closed__1 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__1_value;
static const lean_string_object lp_ttc_command_x23closure___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_ttc_command_x23closure___00__closed__2 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__2_value;
static const lean_ctor_object lp_ttc_command_x23closure___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closure___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_ttc_command_x23closure___00__closed__3 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__3_value;
static const lean_string_object lp_ttc_command_x23closure___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "#closure "};
static const lean_object* lp_ttc_command_x23closure___00__closed__4 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__4_value;
static const lean_ctor_object lp_ttc_command_x23closure___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_ttc_command_x23closure___00__closed__4_value)}};
static const lean_object* lp_ttc_command_x23closure___00__closed__5 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__5_value;
static const lean_string_object lp_ttc_command_x23closure___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* lp_ttc_command_x23closure___00__closed__6 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__6_value;
static const lean_ctor_object lp_ttc_command_x23closure___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closure___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* lp_ttc_command_x23closure___00__closed__7 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__7_value;
static const lean_ctor_object lp_ttc_command_x23closure___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_ttc_command_x23closure___00__closed__7_value)}};
static const lean_object* lp_ttc_command_x23closure___00__closed__8 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__8_value;
static const lean_ctor_object lp_ttc_command_x23closure___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_ttc_command_x23closure___00__closed__3_value),((lean_object*)&lp_ttc_command_x23closure___00__closed__5_value),((lean_object*)&lp_ttc_command_x23closure___00__closed__8_value)}};
static const lean_object* lp_ttc_command_x23closure___00__closed__9 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__9_value;
static const lean_ctor_object lp_ttc_command_x23closure___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_ttc_command_x23closure___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closure___00__closed__9_value)}};
static const lean_object* lp_ttc_command_x23closure___00__closed__10 = (const lean_object*)&lp_ttc_command_x23closure___00__closed__10_value;
LEAN_EXPORT const lean_object* lp_ttc_command_x23closure__ = (const lean_object*)&lp_ttc_command_x23closure___00__closed__10_value;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "FORBIDDEN in closure of "};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__0 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__0_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__1;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__2 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__2_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 16, .m_data = "OK — closure of "};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__4 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__4_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__5;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = " is free of our probability spaces ("};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__6 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__6_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__7;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " Ttc constants)"};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__8 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__8_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not found"};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__10 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__10_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11;
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_ttc_command_x23closureOfType___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "command#closureOfType_"};
static const lean_object* lp_ttc_command_x23closureOfType___00__closed__0 = (const lean_object*)&lp_ttc_command_x23closureOfType___00__closed__0_value;
static const lean_ctor_object lp_ttc_command_x23closureOfType___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closureOfType___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 191, 7, 136, 186, 23, 126, 132)}};
static const lean_object* lp_ttc_command_x23closureOfType___00__closed__1 = (const lean_object*)&lp_ttc_command_x23closureOfType___00__closed__1_value;
static const lean_string_object lp_ttc_command_x23closureOfType___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "#closureOfType "};
static const lean_object* lp_ttc_command_x23closureOfType___00__closed__2 = (const lean_object*)&lp_ttc_command_x23closureOfType___00__closed__2_value;
static const lean_ctor_object lp_ttc_command_x23closureOfType___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_ttc_command_x23closureOfType___00__closed__2_value)}};
static const lean_object* lp_ttc_command_x23closureOfType___00__closed__3 = (const lean_object*)&lp_ttc_command_x23closureOfType___00__closed__3_value;
static const lean_ctor_object lp_ttc_command_x23closureOfType___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_ttc_command_x23closure___00__closed__3_value),((lean_object*)&lp_ttc_command_x23closureOfType___00__closed__3_value),((lean_object*)&lp_ttc_command_x23closure___00__closed__8_value)}};
static const lean_object* lp_ttc_command_x23closureOfType___00__closed__4 = (const lean_object*)&lp_ttc_command_x23closureOfType___00__closed__4_value;
static const lean_ctor_object lp_ttc_command_x23closureOfType___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_ttc_command_x23closureOfType___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closureOfType___00__closed__4_value)}};
static const lean_object* lp_ttc_command_x23closureOfType___00__closed__5 = (const lean_object*)&lp_ttc_command_x23closureOfType___00__closed__5_value;
LEAN_EXPORT const lean_object* lp_ttc_command_x23closureOfType__ = (const lean_object*)&lp_ttc_command_x23closureOfType___00__closed__5_value;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "FORBIDDEN in the statement of "};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__0 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__0_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__1;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 22, .m_data = "OK — the STATEMENT of "};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__2 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__2_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__3;
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_ttc_Ttc_Audit_auditSurface___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Model"};
static const lean_object* lp_ttc_Ttc_Audit_auditSurface___closed__0 = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__0_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_auditSurface___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_auditSurface___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__1_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 16, 206, 66, 111, 220, 7, 64)}};
static const lean_object* lp_ttc_Ttc_Audit_auditSurface___closed__1 = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__1_value;
static const lean_string_object lp_ttc_Ttc_Audit_auditSurface___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Probability"};
static const lean_object* lp_ttc_Ttc_Audit_auditSurface___closed__2 = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__2_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_auditSurface___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_auditSurface___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__3_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 255, 217, 223, 92, 129, 174, 44)}};
static const lean_object* lp_ttc_Ttc_Audit_auditSurface___closed__3 = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__3_value;
static const lean_string_object lp_ttc_Ttc_Audit_auditSurface___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Geometry"};
static const lean_object* lp_ttc_Ttc_Audit_auditSurface___closed__4 = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__4_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_auditSurface___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_Ttc_Audit_forbidden___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 107, 195, 97, 51, 122, 153, 254)}};
static const lean_ctor_object lp_ttc_Ttc_Audit_auditSurface___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__5_value_aux_0),((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__4_value),LEAN_SCALAR_PTR_LITERAL(145, 253, 51, 201, 130, 234, 215, 56)}};
static const lean_object* lp_ttc_Ttc_Audit_auditSurface___closed__5 = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__5_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_auditSurface___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_ttc_Ttc_Audit_auditSurface___closed__6 = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__6_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_auditSurface___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__3_value),((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__6_value)}};
static const lean_object* lp_ttc_Ttc_Audit_auditSurface___closed__7 = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__7_value;
static const lean_ctor_object lp_ttc_Ttc_Audit_auditSurface___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__1_value),((lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__7_value)}};
static const lean_object* lp_ttc_Ttc_Audit_auditSurface___closed__8 = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__8_value;
LEAN_EXPORT const lean_object* lp_ttc_Ttc_Audit_auditSurface = (const lean_object*)&lp_ttc_Ttc_Audit_auditSurface___closed__8_value;
static const lean_string_object lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unknown"};
static const lean_object* lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0___closed__0 = (const lean_object*)&lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0___closed__0_value;
static const lean_ctor_object lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 215, 137, 131, 176, 182, 132, 213)}};
static const lean_object* lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0___closed__1 = (const lean_object*)&lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0___closed__1_value;
LEAN_EXPORT lean_object* lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_ttc_Ttc_Audit_outsideSurface___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_ttc_Ttc_Audit_outsideSurface___closed__0 = (const lean_object*)&lp_ttc_Ttc_Audit_outsideSurface___closed__0_value;
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_outsideSurface(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_outsideSurface___boxed(lean_object*, lean_object*);
static const lean_string_object lp_ttc_command_x23modelClosure___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "command#modelClosure_"};
static const lean_object* lp_ttc_command_x23modelClosure___00__closed__0 = (const lean_object*)&lp_ttc_command_x23modelClosure___00__closed__0_value;
static const lean_ctor_object lp_ttc_command_x23modelClosure___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23modelClosure___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 129, 116, 71, 148, 63, 134, 218)}};
static const lean_object* lp_ttc_command_x23modelClosure___00__closed__1 = (const lean_object*)&lp_ttc_command_x23modelClosure___00__closed__1_value;
static const lean_string_object lp_ttc_command_x23modelClosure___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "#modelClosure "};
static const lean_object* lp_ttc_command_x23modelClosure___00__closed__2 = (const lean_object*)&lp_ttc_command_x23modelClosure___00__closed__2_value;
static const lean_ctor_object lp_ttc_command_x23modelClosure___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_ttc_command_x23modelClosure___00__closed__2_value)}};
static const lean_object* lp_ttc_command_x23modelClosure___00__closed__3 = (const lean_object*)&lp_ttc_command_x23modelClosure___00__closed__3_value;
static const lean_ctor_object lp_ttc_command_x23modelClosure___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_ttc_command_x23closure___00__closed__3_value),((lean_object*)&lp_ttc_command_x23modelClosure___00__closed__3_value),((lean_object*)&lp_ttc_command_x23closure___00__closed__8_value)}};
static const lean_object* lp_ttc_command_x23modelClosure___00__closed__4 = (const lean_object*)&lp_ttc_command_x23modelClosure___00__closed__4_value;
static const lean_ctor_object lp_ttc_command_x23modelClosure___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_ttc_command_x23modelClosure___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&lp_ttc_command_x23modelClosure___00__closed__4_value)}};
static const lean_object* lp_ttc_command_x23modelClosure___00__closed__5 = (const lean_object*)&lp_ttc_command_x23modelClosure___00__closed__5_value;
LEAN_EXPORT const lean_object* lp_ttc_command_x23modelClosure__ = (const lean_object*)&lp_ttc_command_x23modelClosure___00__closed__5_value;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = " is defined entirely under Ttc/Model/, Ttc/Probability/ or Ttc/Geometry/ ("};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__0 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__0_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__1;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "OUTSIDE Model/, Probability/ and Geometry/ in closure of "};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__2 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__2_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__3;
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_ttc_command_x23modelClosureOfType___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "command#modelClosureOfType_"};
static const lean_object* lp_ttc_command_x23modelClosureOfType___00__closed__0 = (const lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__0_value;
static const lean_ctor_object lp_ttc_command_x23modelClosureOfType___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 225, 202, 208, 185, 240, 226, 43)}};
static const lean_object* lp_ttc_command_x23modelClosureOfType___00__closed__1 = (const lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__1_value;
static const lean_string_object lp_ttc_command_x23modelClosureOfType___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "#modelClosureOfType "};
static const lean_object* lp_ttc_command_x23modelClosureOfType___00__closed__2 = (const lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__2_value;
static const lean_ctor_object lp_ttc_command_x23modelClosureOfType___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__2_value)}};
static const lean_object* lp_ttc_command_x23modelClosureOfType___00__closed__3 = (const lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__3_value;
static const lean_ctor_object lp_ttc_command_x23modelClosureOfType___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_ttc_command_x23closure___00__closed__3_value),((lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__3_value),((lean_object*)&lp_ttc_command_x23closure___00__closed__8_value)}};
static const lean_object* lp_ttc_command_x23modelClosureOfType___00__closed__4 = (const lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__4_value;
static const lean_ctor_object lp_ttc_command_x23modelClosureOfType___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__4_value)}};
static const lean_object* lp_ttc_command_x23modelClosureOfType___00__closed__5 = (const lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__5_value;
LEAN_EXPORT const lean_object* lp_ttc_command_x23modelClosureOfType__ = (const lean_object*)&lp_ttc_command_x23modelClosureOfType___00__closed__5_value;
static const lean_string_object lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "OUTSIDE Model/, Probability/ and Geometry/ in the statement of "};
static const lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__0 = (const lean_object*)&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__0_value;
static lean_once_cell_t lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__1;
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_ttc_Ttc_Audit_reportOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " Ttc constants, "};
static const lean_object* lp_ttc_Ttc_Audit_reportOn___closed__0 = (const lean_object*)&lp_ttc_Ttc_Audit_reportOn___closed__0_value;
static lean_once_cell_t lp_ttc_Ttc_Audit_reportOn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_Audit_reportOn___closed__1;
static const lean_string_object lp_ttc_Ttc_Audit_reportOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = " outside Model/ and Probability/, forbidden hits: "};
static const lean_object* lp_ttc_Ttc_Audit_reportOn___closed__2 = (const lean_object*)&lp_ttc_Ttc_Audit_reportOn___closed__2_value;
static lean_once_cell_t lp_ttc_Ttc_Audit_reportOn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_Audit_reportOn___closed__3;
static const lean_string_object lp_ttc_Ttc_Audit_reportOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* lp_ttc_Ttc_Audit_reportOn___closed__4 = (const lean_object*)&lp_ttc_Ttc_Audit_reportOn___closed__4_value;
static const lean_string_object lp_ttc_Ttc_Audit_reportOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " (statement)"};
static const lean_object* lp_ttc_Ttc_Audit_reportOn___closed__5 = (const lean_object*)&lp_ttc_Ttc_Audit_reportOn___closed__5_value;
static const lean_string_object lp_ttc_Ttc_Audit_reportOn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ": not found"};
static const lean_object* lp_ttc_Ttc_Audit_reportOn___closed__6 = (const lean_object*)&lp_ttc_Ttc_Audit_reportOn___closed__6_value;
static lean_once_cell_t lp_ttc_Ttc_Audit_reportOn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ttc_Ttc_Audit_reportOn___closed__7;
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_reportOn(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_reportOn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_ttc_command_x23closureReport___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "command#closureReport_"};
static const lean_object* lp_ttc_command_x23closureReport___00__closed__0 = (const lean_object*)&lp_ttc_command_x23closureReport___00__closed__0_value;
static const lean_ctor_object lp_ttc_command_x23closureReport___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closureReport___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 105, 187, 85, 168, 3, 250, 11)}};
static const lean_object* lp_ttc_command_x23closureReport___00__closed__1 = (const lean_object*)&lp_ttc_command_x23closureReport___00__closed__1_value;
static const lean_string_object lp_ttc_command_x23closureReport___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "#closureReport "};
static const lean_object* lp_ttc_command_x23closureReport___00__closed__2 = (const lean_object*)&lp_ttc_command_x23closureReport___00__closed__2_value;
static const lean_ctor_object lp_ttc_command_x23closureReport___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_ttc_command_x23closureReport___00__closed__2_value)}};
static const lean_object* lp_ttc_command_x23closureReport___00__closed__3 = (const lean_object*)&lp_ttc_command_x23closureReport___00__closed__3_value;
static const lean_ctor_object lp_ttc_command_x23closureReport___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_ttc_command_x23closure___00__closed__3_value),((lean_object*)&lp_ttc_command_x23closureReport___00__closed__3_value),((lean_object*)&lp_ttc_command_x23closure___00__closed__8_value)}};
static const lean_object* lp_ttc_command_x23closureReport___00__closed__4 = (const lean_object*)&lp_ttc_command_x23closureReport___00__closed__4_value;
static const lean_ctor_object lp_ttc_command_x23closureReport___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_ttc_command_x23closureReport___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closureReport___00__closed__4_value)}};
static const lean_object* lp_ttc_command_x23closureReport___00__closed__5 = (const lean_object*)&lp_ttc_command_x23closureReport___00__closed__5_value;
LEAN_EXPORT const lean_object* lp_ttc_command_x23closureReport__ = (const lean_object*)&lp_ttc_command_x23closureReport___00__closed__5_value;
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReport____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReport____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_ttc_command_x23closureReportOfType___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "command#closureReportOfType_"};
static const lean_object* lp_ttc_command_x23closureReportOfType___00__closed__0 = (const lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__0_value;
static const lean_ctor_object lp_ttc_command_x23closureReportOfType___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 59, 232, 160, 206, 126, 136, 138)}};
static const lean_object* lp_ttc_command_x23closureReportOfType___00__closed__1 = (const lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__1_value;
static const lean_string_object lp_ttc_command_x23closureReportOfType___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "#closureReportOfType "};
static const lean_object* lp_ttc_command_x23closureReportOfType___00__closed__2 = (const lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__2_value;
static const lean_ctor_object lp_ttc_command_x23closureReportOfType___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__2_value)}};
static const lean_object* lp_ttc_command_x23closureReportOfType___00__closed__3 = (const lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__3_value;
static const lean_ctor_object lp_ttc_command_x23closureReportOfType___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_ttc_command_x23closure___00__closed__3_value),((lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__3_value),((lean_object*)&lp_ttc_command_x23closure___00__closed__8_value)}};
static const lean_object* lp_ttc_command_x23closureReportOfType___00__closed__4 = (const lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__4_value;
static const lean_ctor_object lp_ttc_command_x23closureReportOfType___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__4_value)}};
static const lean_object* lp_ttc_command_x23closureReportOfType___00__closed__5 = (const lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__5_value;
LEAN_EXPORT const lean_object* lp_ttc_command_x23closureReportOfType__ = (const lean_object*)&lp_ttc_command_x23closureReportOfType___00__closed__5_value;
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReportOfType____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReportOfType____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_closureAux(lean_object* v_env_76_, lean_object* v_x_77_, lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_dec(v_x_77_);
lean_dec_ref(v_env_76_);
return v_x_79_;
}
else
{
lean_object* v_head_80_; lean_object* v_tail_81_; uint8_t v___x_82_; 
v_head_80_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_head_80_);
v_tail_81_ = lean_ctor_get(v_x_78_, 1);
lean_inc(v_tail_81_);
lean_dec_ref_known(v_x_78_, 2);
v___x_82_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_head_80_, v_x_77_);
if (v___x_82_ == 0)
{
lean_object* v_seen_83_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_92_; lean_object* v___x_104_; uint8_t v___x_105_; 
lean_inc(v_head_80_);
v_seen_83_ = l_Lean_NameSet_insert(v_x_77_, v_head_80_);
v___x_104_ = ((lean_object*)(lp_ttc_Ttc_Audit_closureAux___closed__0));
v___x_105_ = l_Lean_Name_isPrefixOf(v___x_104_, v_head_80_);
if (v___x_105_ == 0)
{
v___y_92_ = v_x_79_;
goto v___jp_91_;
}
else
{
lean_object* v___x_106_; 
lean_inc(v_head_80_);
v___x_106_ = l_Lean_NameSet_insert(v_x_79_, v_head_80_);
v___y_92_ = v___x_106_;
goto v___jp_91_;
}
v___jp_84_:
{
lean_object* v_next_88_; lean_object* v___x_89_; 
v_next_88_ = l_List_appendTR___redArg(v___y_85_, v___y_87_);
v___x_89_ = l_List_appendTR___redArg(v_next_88_, v_tail_81_);
v_x_77_ = v_seen_83_;
v_x_78_ = v___x_89_;
v_x_79_ = v___y_86_;
goto _start;
}
v___jp_91_:
{
lean_object* v___x_93_; 
lean_inc_ref(v_env_76_);
v___x_93_ = l_Lean_Environment_find_x3f(v_env_76_, v_head_80_, v___x_82_);
if (lean_obj_tag(v___x_93_) == 0)
{
v_x_77_ = v_seen_83_;
v_x_78_ = v_tail_81_;
v_x_79_ = v___y_92_;
goto _start;
}
else
{
lean_object* v_val_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_val_95_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_val_95_);
lean_dec_ref_known(v___x_93_, 1);
v___x_96_ = l_Lean_ConstantInfo_type(v_val_95_);
v___x_97_ = l_Lean_Expr_getUsedConstants(v___x_96_);
v___x_98_ = lean_array_to_list(v___x_97_);
v___x_99_ = l_Lean_ConstantInfo_value_x3f(v_val_95_, v___x_82_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(0);
v___y_85_ = v___x_98_;
v___y_86_ = v___y_92_;
v___y_87_ = v___x_100_;
goto v___jp_84_;
}
else
{
lean_object* v_val_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_val_101_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_val_101_);
lean_dec_ref_known(v___x_99_, 1);
v___x_102_ = l_Lean_Expr_getUsedConstants(v_val_101_);
v___x_103_ = lean_array_to_list(v___x_102_);
v___y_85_ = v___x_98_;
v___y_86_ = v___y_92_;
v___y_87_ = v___x_103_;
goto v___jp_84_;
}
}
}
}
else
{
lean_dec(v_head_80_);
v_x_78_ = v_tail_81_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_List_filterTR_loop___at___00Ttc_Audit_forbiddenIn_spec__0(lean_object* v_env_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
if (lean_obj_tag(v_a_109_) == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v_env_108_);
v___x_111_ = l_List_reverse___redArg(v_a_110_);
return v___x_111_;
}
else
{
lean_object* v_head_112_; lean_object* v_tail_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_130_; 
v_head_112_ = lean_ctor_get(v_a_109_, 0);
v_tail_113_ = lean_ctor_get(v_a_109_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_a_109_);
if (v_isSharedCheck_130_ == 0)
{
v___x_115_ = v_a_109_;
v_isShared_116_ = v_isSharedCheck_130_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_tail_113_);
lean_inc(v_head_112_);
lean_dec(v_a_109_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_130_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
uint8_t v___y_118_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = ((lean_object*)(lp_ttc_Ttc_Audit_forbidden));
v___x_125_ = lp_mathlib_List_any___at___00Mathlib_Linter_directoryDependencyCheck_spec__10(v_head_112_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_inc_ref(v_env_108_);
v___x_126_ = lp_importGraph_Lean_Environment_getModuleFor_x3f(v_env_108_, v_head_112_);
if (lean_obj_tag(v___x_126_) == 0)
{
v___y_118_ = v___x_125_;
goto v___jp_117_;
}
else
{
lean_object* v_val_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v_val_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_val_127_);
lean_dec_ref_known(v___x_126_, 1);
v___x_128_ = ((lean_object*)(lp_ttc_Ttc_Audit_forbiddenModules));
v___x_129_ = lp_mathlib_List_any___at___00Mathlib_Linter_directoryDependencyCheck_spec__10(v_val_127_, v___x_128_);
lean_dec(v_val_127_);
v___y_118_ = v___x_129_;
goto v___jp_117_;
}
}
else
{
v___y_118_ = v___x_125_;
goto v___jp_117_;
}
v___jp_117_:
{
if (v___y_118_ == 0)
{
lean_del_object(v___x_115_);
lean_dec(v_head_112_);
v_a_109_ = v_tail_113_;
goto _start;
}
else
{
lean_object* v___x_121_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_a_110_);
v___x_121_ = v___x_115_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_head_112_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_a_110_);
v___x_121_ = v_reuseFailAlloc_123_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
v_a_109_ = v_tail_113_;
v_a_110_ = v___x_121_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_forbiddenIn(lean_object* v_env_131_, lean_object* v_cls_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_box(0);
v___x_134_ = lp_mathlib_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Mathlib_Tactic_Linter_UpstreamableDecl_0__Lean_Environment_localDefinitionDependencies_spec__1(v___x_133_, v_cls_132_);
v___x_135_ = lp_ttc_List_filterTR_loop___at___00Ttc_Audit_forbiddenIn_spec__0(v_env_131_, v___x_134_, v___x_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_forbiddenIn___boxed(lean_object* v_env_136_, lean_object* v_cls_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = lp_ttc_Ttc_Audit_forbiddenIn(v_env_136_, v_cls_137_);
lean_dec(v_cls_137_);
return v_res_138_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__1(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__0));
v___x_164_ = l_Lean_stringToMessageData(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__2));
v___x_167_ = l_Lean_stringToMessageData(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__5(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__4));
v___x_170_ = l_Lean_stringToMessageData(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__7(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__6));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__8));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__10));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1(lean_object* v_x_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(lp_ttc_command_x23closure___00__closed__1));
lean_inc(v_x_180_);
v___x_185_ = l_Lean_Syntax_isOfKind(v_x_180_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
lean_dec(v_x_180_);
v___x_186_ = lp_mathlib_Lean_Elab_throwUnsupportedSyntax___at___00elabSuppressCompilationDecl_spec__0___redArg();
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_187_ = lean_st_ref_get(v_a_182_);
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = l_Lean_Syntax_getArg(v_x_180_, v___x_188_);
lean_dec(v_x_180_);
v___x_190_ = lean_alloc_closure((void*)(l_Lean_realizeGlobalConstNoOverload___boxed), 4, 1);
lean_closure_set(v___x_190_, 0, v___x_189_);
v___x_191_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_190_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v_env_193_; uint8_t v___x_194_; lean_object* v___x_195_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc_n(v_a_192_, 2);
lean_dec_ref_known(v___x_191_, 1);
v_env_193_ = lean_ctor_get(v___x_187_, 0);
lean_inc_ref_n(v_env_193_, 2);
lean_dec(v___x_187_);
v___x_194_ = 0;
v___x_195_ = l_Lean_Environment_find_x3f(v_env_193_, v_a_192_, v___x_194_);
if (lean_obj_tag(v___x_195_) == 1)
{
lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_231_; 
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v___x_195_, 0);
lean_dec(v_unused_232_);
v___x_197_ = v___x_195_;
v_isShared_198_ = v_isSharedCheck_231_;
goto v_resetjp_196_;
}
else
{
lean_dec(v___x_195_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_231_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_199_ = lean_box(0);
v___x_200_ = lean_box(1);
lean_inc(v_a_192_);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v_a_192_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_inc_ref(v_env_193_);
v___x_202_ = lp_ttc_Ttc_Audit_closureAux(v_env_193_, v___x_200_, v___x_201_, v___x_200_);
v___x_203_ = lp_mathlib_Std_DTreeMap_Internal_Impl_erase___at___00__private_Mathlib_Tactic_Linter_MinImports_0__Mathlib_Linter_MinImports_minImportsLinter_spec__2___redArg(v_a_192_, v___x_202_);
v___x_204_ = lp_ttc_Ttc_Audit_forbiddenIn(v_env_193_, v___x_203_);
v___x_205_ = l_List_isEmpty___redArg(v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v___x_203_);
lean_del_object(v___x_197_);
v___x_206_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__1, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__1_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__1);
v___x_207_ = l_Lean_MessageData_ofName(v_a_192_);
v___x_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = l_List_mapTR_loop___at___00__private_Lean_Elab_MutualInductive_0__Lean_Elab_Command_withElaboratedHeaders_spec__0(v___x_204_, v___x_199_);
v___x_212_ = l_Lean_MessageData_ofList(v___x_211_);
v___x_213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_210_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(v___x_213_, v_a_181_, v_a_182_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
lean_dec(v___x_204_);
v___x_215_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__5, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__5_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__5);
v___x_216_ = l_Lean_MessageData_ofName(v_a_192_);
v___x_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__7, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__7_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__7);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lp_mathlib_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Mathlib_Tactic_Linter_UpstreamableDecl_0__Lean_Environment_localDefinitionDependencies_spec__1(v___x_199_, v___x_203_);
lean_dec(v___x_203_);
v___x_221_ = l_List_lengthTR___redArg(v___x_220_);
lean_dec(v___x_220_);
v___x_222_ = l_Nat_reprFast(v___x_221_);
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 3);
lean_ctor_set(v___x_197_, 0, v___x_222_);
v___x_224_ = v___x_197_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_230_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_225_ = l_Lean_MessageData_ofFormat(v___x_224_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_219_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lp_mathlib_Lean_logInfo___at___00Mathlib_CrossRef_traceCrossRefs_spec__1(v___x_228_, v_a_181_, v_a_182_);
return v___x_229_;
}
}
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v___x_195_);
lean_dec_ref(v_env_193_);
lean_dec(v_a_192_);
v___x_233_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11);
v___x_234_ = l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(v___x_233_, v_a_181_, v_a_182_);
return v___x_234_;
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v___x_187_);
v_a_235_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_191_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_191_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___boxed(lean_object* v_x_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1(v_x_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
return v_res_247_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__1(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__0));
v___x_265_ = l_Lean_stringToMessageData(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__3(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__2));
v___x_268_ = l_Lean_stringToMessageData(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1(lean_object* v_x_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = ((lean_object*)(lp_ttc_command_x23closureOfType___00__closed__1));
lean_inc(v_x_269_);
v___x_274_ = l_Lean_Syntax_isOfKind(v_x_269_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec(v_x_269_);
v___x_275_ = lp_mathlib_Lean_Elab_throwUnsupportedSyntax___at___00elabSuppressCompilationDecl_spec__0___redArg();
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_276_ = lean_st_ref_get(v_a_271_);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = l_Lean_Syntax_getArg(v_x_269_, v___x_277_);
lean_dec(v_x_269_);
v___x_279_ = lean_alloc_closure((void*)(l_Lean_realizeGlobalConstNoOverload___boxed), 4, 1);
lean_closure_set(v___x_279_, 0, v___x_278_);
v___x_280_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_279_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v_env_282_; uint8_t v___x_283_; lean_object* v___x_284_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_n(v_a_281_, 2);
lean_dec_ref_known(v___x_280_, 1);
v_env_282_ = lean_ctor_get(v___x_276_, 0);
lean_inc_ref_n(v_env_282_, 2);
lean_dec(v___x_276_);
v___x_283_ = 0;
v___x_284_ = l_Lean_Environment_find_x3f(v_env_282_, v_a_281_, v___x_283_);
if (lean_obj_tag(v___x_284_) == 1)
{
lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_323_; 
v_val_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_323_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_323_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_323_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_289_ = lean_box(1);
v___x_290_ = l_Lean_ConstantInfo_type(v_val_285_);
lean_dec(v_val_285_);
v___x_291_ = l_Lean_Expr_getUsedConstants(v___x_290_);
v___x_292_ = lean_array_to_list(v___x_291_);
lean_inc_ref(v_env_282_);
v___x_293_ = lp_ttc_Ttc_Audit_closureAux(v_env_282_, v___x_289_, v___x_292_, v___x_289_);
v___x_294_ = lp_ttc_Ttc_Audit_forbiddenIn(v_env_282_, v___x_293_);
v___x_295_ = l_List_isEmpty___redArg(v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v___x_293_);
lean_del_object(v___x_287_);
v___x_296_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__1, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__1_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__1);
v___x_297_ = l_Lean_MessageData_ofName(v_a_281_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_box(0);
v___x_302_ = l_List_mapTR_loop___at___00__private_Lean_Elab_MutualInductive_0__Lean_Elab_Command_withElaboratedHeaders_spec__0(v___x_294_, v___x_301_);
v___x_303_ = l_Lean_MessageData_ofList(v___x_302_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_300_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(v___x_304_, v_a_270_, v_a_271_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
lean_dec(v___x_294_);
v___x_306_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__3, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__3_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__3);
v___x_307_ = l_Lean_MessageData_ofName(v_a_281_);
v___x_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__7, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__7_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__7);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_box(0);
v___x_312_ = lp_mathlib_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Mathlib_Tactic_Linter_UpstreamableDecl_0__Lean_Environment_localDefinitionDependencies_spec__1(v___x_311_, v___x_293_);
lean_dec(v___x_293_);
v___x_313_ = l_List_lengthTR___redArg(v___x_312_);
lean_dec(v___x_312_);
v___x_314_ = l_Nat_reprFast(v___x_313_);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 3);
lean_ctor_set(v___x_287_, 0, v___x_314_);
v___x_316_ = v___x_287_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_322_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = l_Lean_MessageData_ofFormat(v___x_316_);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_310_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lp_mathlib_Lean_logInfo___at___00Mathlib_CrossRef_traceCrossRefs_spec__1(v___x_320_, v_a_270_, v_a_271_);
return v___x_321_;
}
}
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v___x_284_);
lean_dec_ref(v_env_282_);
lean_dec(v_a_281_);
v___x_324_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11);
v___x_325_ = l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(v___x_324_, v_a_270_, v_a_271_);
return v___x_325_;
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v___x_276_);
v_a_326_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_280_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_280_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___boxed(lean_object* v_x_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1(v_x_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0(lean_object* v_env_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
if (lean_obj_tag(v_a_365_) == 0)
{
lean_object* v___x_367_; 
lean_dec_ref(v_env_364_);
v___x_367_ = lean_array_to_list(v_a_366_);
return v___x_367_;
}
else
{
lean_object* v_head_368_; lean_object* v_tail_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_389_; 
v_head_368_ = lean_ctor_get(v_a_365_, 0);
v_tail_369_ = lean_ctor_get(v_a_365_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v_a_365_);
if (v_isSharedCheck_389_ == 0)
{
v___x_371_ = v_a_365_;
v_isShared_372_ = v_isSharedCheck_389_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_tail_369_);
lean_inc(v_head_368_);
lean_dec(v_a_365_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_389_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v_val_374_; lean_object* v___x_377_; 
lean_inc_ref(v_env_364_);
v___x_377_ = lp_importGraph_Lean_Environment_getModuleFor_x3f(v_env_364_, v_head_368_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = ((lean_object*)(lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0___closed__1));
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 0);
lean_ctor_set(v___x_371_, 1, v___x_378_);
v___x_380_ = v___x_371_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_head_368_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
v_val_374_ = v___x_380_;
goto v___jp_373_;
}
}
else
{
lean_object* v_val_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_val_382_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_val_382_);
lean_dec_ref_known(v___x_377_, 1);
v___x_383_ = ((lean_object*)(lp_ttc_Ttc_Audit_auditSurface));
v___x_384_ = lp_mathlib_List_any___at___00Mathlib_Linter_directoryDependencyCheck_spec__10(v_val_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_386_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 0);
lean_ctor_set(v___x_371_, 1, v_val_382_);
v___x_386_ = v___x_371_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_head_368_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_val_382_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
v_val_374_ = v___x_386_;
goto v___jp_373_;
}
}
else
{
lean_dec(v_val_382_);
lean_del_object(v___x_371_);
lean_dec(v_head_368_);
v_a_365_ = v_tail_369_;
goto _start;
}
}
v___jp_373_:
{
lean_object* v___x_375_; 
v___x_375_ = lean_array_push(v_a_366_, v_val_374_);
v_a_365_ = v_tail_369_;
v_a_366_ = v___x_375_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_outsideSurface(lean_object* v_env_392_, lean_object* v_cls_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = lean_box(0);
v___x_395_ = lp_mathlib_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Mathlib_Tactic_Linter_UpstreamableDecl_0__Lean_Environment_localDefinitionDependencies_spec__1(v___x_394_, v_cls_393_);
v___x_396_ = ((lean_object*)(lp_ttc_Ttc_Audit_outsideSurface___closed__0));
v___x_397_ = lp_ttc_List_filterMapTR_go___at___00Ttc_Audit_outsideSurface_spec__0(v_env_392_, v___x_395_, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_outsideSurface___boxed(lean_object* v_env_398_, lean_object* v_cls_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = lp_ttc_Ttc_Audit_outsideSurface(v_env_398_, v_cls_399_);
lean_dec(v_cls_399_);
return v_res_400_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__1(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__0));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__3(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__2));
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1(lean_object* v_x_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(lp_ttc_command_x23modelClosure___00__closed__1));
lean_inc(v_x_422_);
v___x_427_ = l_Lean_Syntax_isOfKind(v_x_422_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v_x_422_);
v___x_428_ = lp_mathlib_Lean_Elab_throwUnsupportedSyntax___at___00elabSuppressCompilationDecl_spec__0___redArg();
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_429_ = lean_st_ref_get(v_a_424_);
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = l_Lean_Syntax_getArg(v_x_422_, v___x_430_);
lean_dec(v_x_422_);
v___x_432_ = lean_alloc_closure((void*)(l_Lean_realizeGlobalConstNoOverload___boxed), 4, 1);
lean_closure_set(v___x_432_, 0, v___x_431_);
v___x_433_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_432_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v_env_435_; uint8_t v___x_436_; lean_object* v___x_437_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_n(v_a_434_, 2);
lean_dec_ref_known(v___x_433_, 1);
v_env_435_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref_n(v_env_435_, 2);
lean_dec(v___x_429_);
v___x_436_ = 0;
v___x_437_ = l_Lean_Environment_find_x3f(v_env_435_, v_a_434_, v___x_436_);
if (lean_obj_tag(v___x_437_) == 1)
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_472_; 
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v___x_437_, 0);
lean_dec(v_unused_473_);
v___x_439_ = v___x_437_;
v_isShared_440_ = v_isSharedCheck_472_;
goto v_resetjp_438_;
}
else
{
lean_dec(v___x_437_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_472_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_441_ = lean_box(0);
v___x_442_ = lean_box(1);
lean_inc(v_a_434_);
v___x_443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_443_, 0, v_a_434_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_inc_ref(v_env_435_);
v___x_444_ = lp_ttc_Ttc_Audit_closureAux(v_env_435_, v___x_442_, v___x_443_, v___x_442_);
v___x_445_ = lp_mathlib_Std_DTreeMap_Internal_Impl_erase___at___00__private_Mathlib_Tactic_Linter_MinImports_0__Mathlib_Linter_MinImports_minImportsLinter_spec__2___redArg(v_a_434_, v___x_444_);
v___x_446_ = lp_ttc_Ttc_Audit_outsideSurface(v_env_435_, v___x_445_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_447_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__5, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__5_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__5);
v___x_448_ = l_Lean_MessageData_ofName(v_a_434_);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__1, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__1_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__1);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = lp_mathlib_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Mathlib_Tactic_Linter_UpstreamableDecl_0__Lean_Environment_localDefinitionDependencies_spec__1(v___x_441_, v___x_445_);
lean_dec(v___x_445_);
v___x_453_ = l_List_lengthTR___redArg(v___x_452_);
lean_dec(v___x_452_);
v___x_454_ = l_Nat_reprFast(v___x_453_);
if (v_isShared_440_ == 0)
{
lean_ctor_set_tag(v___x_439_, 3);
lean_ctor_set(v___x_439_, 0, v___x_454_);
v___x_456_ = v___x_439_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_462_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_457_ = l_Lean_MessageData_ofFormat(v___x_456_);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_451_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = lp_mathlib_Lean_logInfo___at___00Mathlib_CrossRef_traceCrossRefs_spec__1(v___x_460_, v_a_423_, v_a_424_);
return v___x_461_;
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v___x_445_);
lean_del_object(v___x_439_);
v___x_463_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__3, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__3_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__3);
v___x_464_ = l_Lean_MessageData_ofName(v_a_434_);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(v___x_446_, v___x_441_);
v___x_469_ = l_Lean_MessageData_ofList(v___x_468_);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_467_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(v___x_470_, v_a_423_, v_a_424_);
return v___x_471_;
}
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v___x_437_);
lean_dec_ref(v_env_435_);
lean_dec(v_a_434_);
v___x_474_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11);
v___x_475_ = l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(v___x_474_, v_a_423_, v_a_424_);
return v___x_475_;
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v___x_429_);
v_a_476_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_433_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_433_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___boxed(lean_object* v_x_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1(v_x_484_, v_a_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
return v_res_488_;
}
}
static lean_object* _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__1(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__0));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1(lean_object* v_x_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(lp_ttc_command_x23modelClosureOfType___00__closed__1));
lean_inc(v_x_507_);
v___x_512_ = l_Lean_Syntax_isOfKind(v_x_507_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_x_507_);
v___x_513_ = lp_mathlib_Lean_Elab_throwUnsupportedSyntax___at___00elabSuppressCompilationDecl_spec__0___redArg();
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_514_ = lean_st_ref_get(v_a_509_);
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = l_Lean_Syntax_getArg(v_x_507_, v___x_515_);
lean_dec(v_x_507_);
v___x_517_ = lean_alloc_closure((void*)(l_Lean_realizeGlobalConstNoOverload___boxed), 4, 1);
lean_closure_set(v___x_517_, 0, v___x_516_);
v___x_518_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_517_, v_a_508_, v_a_509_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v_env_520_; uint8_t v___x_521_; lean_object* v___x_522_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc_n(v_a_519_, 2);
lean_dec_ref_known(v___x_518_, 1);
v_env_520_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref_n(v_env_520_, 2);
lean_dec(v___x_514_);
v___x_521_ = 0;
v___x_522_ = l_Lean_Environment_find_x3f(v_env_520_, v_a_519_, v___x_521_);
if (lean_obj_tag(v___x_522_) == 1)
{
lean_object* v_val_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_560_; 
v_val_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_560_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_560_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_val_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_560_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_527_ = lean_box(1);
v___x_528_ = l_Lean_ConstantInfo_type(v_val_523_);
lean_dec(v_val_523_);
v___x_529_ = l_Lean_Expr_getUsedConstants(v___x_528_);
v___x_530_ = lean_array_to_list(v___x_529_);
lean_inc_ref(v_env_520_);
v___x_531_ = lp_ttc_Ttc_Audit_closureAux(v_env_520_, v___x_527_, v___x_530_, v___x_527_);
v___x_532_ = lp_ttc_Ttc_Audit_outsideSurface(v_env_520_, v___x_531_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_533_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__3, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__3_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureOfType____1___closed__3);
v___x_534_ = l_Lean_MessageData_ofName(v_a_519_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__1, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__1_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosure____1___closed__1);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_box(0);
v___x_539_ = lp_mathlib_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Mathlib_Tactic_Linter_UpstreamableDecl_0__Lean_Environment_localDefinitionDependencies_spec__1(v___x_538_, v___x_531_);
lean_dec(v___x_531_);
v___x_540_ = l_List_lengthTR___redArg(v___x_539_);
lean_dec(v___x_539_);
v___x_541_ = l_Nat_reprFast(v___x_540_);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 3);
lean_ctor_set(v___x_525_, 0, v___x_541_);
v___x_543_ = v___x_525_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_549_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_544_ = l_Lean_MessageData_ofFormat(v___x_543_);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_537_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__9);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lp_mathlib_Lean_logInfo___at___00Mathlib_CrossRef_traceCrossRefs_spec__1(v___x_547_, v_a_508_, v_a_509_);
return v___x_548_;
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v___x_531_);
lean_del_object(v___x_525_);
v___x_550_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__1, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__1_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___closed__1);
v___x_551_ = l_Lean_MessageData_ofName(v_a_519_);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_box(0);
v___x_556_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(v___x_532_, v___x_555_);
v___x_557_ = l_Lean_MessageData_ofList(v___x_556_);
v___x_558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_554_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(v___x_558_, v_a_508_, v_a_509_);
return v___x_559_;
}
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_522_);
lean_dec_ref(v_env_520_);
lean_dec(v_a_519_);
v___x_561_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__11);
v___x_562_ = l_Lean_throwError___at___00Lean_Elab_Command_elabDeclaration_spec__0___redArg(v___x_561_, v_a_508_, v_a_509_);
return v___x_562_;
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v___x_514_);
v_a_563_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_518_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_518_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1___boxed(lean_object* v_x_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23modelClosureOfType____1(v_x_571_, v_a_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
return v_res_575_;
}
}
static lean_object* _init_lp_ttc_Ttc_Audit_reportOn___closed__1(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(lp_ttc_Ttc_Audit_reportOn___closed__0));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_lp_ttc_Ttc_Audit_reportOn___closed__3(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(lp_ttc_Ttc_Audit_reportOn___closed__2));
v___x_581_ = l_Lean_stringToMessageData(v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_lp_ttc_Ttc_Audit_reportOn___closed__7(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(lp_ttc_Ttc_Audit_reportOn___closed__6));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_reportOn(lean_object* v_env_587_, lean_object* v_n_588_, uint8_t v_fromTypeOnly_589_){
_start:
{
lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_620_; uint8_t v___x_625_; lean_object* v___x_626_; 
v___x_625_ = 0;
lean_inc(v_n_588_);
lean_inc_ref(v_env_587_);
v___x_626_ = l_Lean_Environment_find_x3f(v_env_587_, v_n_588_, v___x_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref(v_env_587_);
v___x_627_ = l_Lean_MessageData_ofName(v_n_588_);
v___x_628_ = lean_obj_once(&lp_ttc_Ttc_Audit_reportOn___closed__7, &lp_ttc_Ttc_Audit_reportOn___closed__7_once, _init_lp_ttc_Ttc_Audit_reportOn___closed__7);
v___x_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
return v___x_629_;
}
else
{
if (v_fromTypeOnly_589_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec_ref_known(v___x_626_, 1);
v___x_630_ = lean_box(1);
v___x_631_ = lean_box(0);
lean_inc(v_n_588_);
v___x_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_632_, 0, v_n_588_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
lean_inc_ref(v_env_587_);
v___x_633_ = lp_ttc_Ttc_Audit_closureAux(v_env_587_, v___x_630_, v___x_632_, v___x_630_);
v___x_634_ = lp_mathlib_Std_DTreeMap_Internal_Impl_erase___at___00__private_Mathlib_Tactic_Linter_MinImports_0__Mathlib_Linter_MinImports_minImportsLinter_spec__2___redArg(v_n_588_, v___x_633_);
v___y_620_ = v___x_634_;
goto v___jp_619_;
}
else
{
lean_object* v_val_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_val_635_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v___x_626_, 1);
v___x_636_ = lean_box(1);
v___x_637_ = l_Lean_ConstantInfo_type(v_val_635_);
lean_dec(v_val_635_);
v___x_638_ = l_Lean_Expr_getUsedConstants(v___x_637_);
v___x_639_ = lean_array_to_list(v___x_638_);
lean_inc_ref(v_env_587_);
v___x_640_ = lp_ttc_Ttc_Audit_closureAux(v_env_587_, v___x_636_, v___x_639_, v___x_636_);
v___y_620_ = v___x_640_;
goto v___jp_619_;
}
}
v___jp_590_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_inc_ref(v___y_594_);
v___x_595_ = l_Lean_stringToMessageData(v___y_594_);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___y_592_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_obj_once(&lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3, &lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3_once, _init_lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closure____1___closed__3);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_box(0);
v___x_600_ = lp_mathlib_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Mathlib_Tactic_Linter_UpstreamableDecl_0__Lean_Environment_localDefinitionDependencies_spec__1(v___x_599_, v___y_591_);
v___x_601_ = l_List_lengthTR___redArg(v___x_600_);
lean_dec(v___x_600_);
v___x_602_ = l_Nat_reprFast(v___x_601_);
v___x_603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = l_Lean_MessageData_ofFormat(v___x_603_);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_598_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_obj_once(&lp_ttc_Ttc_Audit_reportOn___closed__1, &lp_ttc_Ttc_Audit_reportOn___closed__1_once, _init_lp_ttc_Ttc_Audit_reportOn___closed__1);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_List_lengthTR___redArg(v___y_593_);
lean_dec(v___y_593_);
v___x_609_ = l_Nat_reprFast(v___x_608_);
v___x_610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
v___x_611_ = l_Lean_MessageData_ofFormat(v___x_610_);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_607_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_obj_once(&lp_ttc_Ttc_Audit_reportOn___closed__3, &lp_ttc_Ttc_Audit_reportOn___closed__3_once, _init_lp_ttc_Ttc_Audit_reportOn___closed__3);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lp_ttc_Ttc_Audit_forbiddenIn(v_env_587_, v___y_591_);
lean_dec(v___y_591_);
v___x_616_ = l_List_mapTR_loop___at___00__private_Lean_Elab_MutualInductive_0__Lean_Elab_Command_withElaboratedHeaders_spec__0(v___x_615_, v___x_599_);
v___x_617_ = l_Lean_MessageData_ofList(v___x_616_);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_614_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
return v___x_618_;
}
v___jp_619_:
{
lean_object* v_outside_621_; lean_object* v___x_622_; 
lean_inc_ref(v_env_587_);
v_outside_621_ = lp_ttc_Ttc_Audit_outsideSurface(v_env_587_, v___y_620_);
v___x_622_ = l_Lean_MessageData_ofName(v_n_588_);
if (v_fromTypeOnly_589_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(lp_ttc_Ttc_Audit_reportOn___closed__4));
v___y_591_ = v___y_620_;
v___y_592_ = v___x_622_;
v___y_593_ = v_outside_621_;
v___y_594_ = v___x_623_;
goto v___jp_590_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(lp_ttc_Ttc_Audit_reportOn___closed__5));
v___y_591_ = v___y_620_;
v___y_592_ = v___x_622_;
v___y_593_ = v_outside_621_;
v___y_594_ = v___x_624_;
goto v___jp_590_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc_Ttc_Audit_reportOn___boxed(lean_object* v_env_641_, lean_object* v_n_642_, lean_object* v_fromTypeOnly_643_){
_start:
{
uint8_t v_fromTypeOnly_boxed_644_; lean_object* v_res_645_; 
v_fromTypeOnly_boxed_644_ = lean_unbox(v_fromTypeOnly_643_);
v_res_645_ = lp_ttc_Ttc_Audit_reportOn(v_env_641_, v_n_642_, v_fromTypeOnly_boxed_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReport____1(lean_object* v_x_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = ((lean_object*)(lp_ttc_command_x23closureReport___00__closed__1));
lean_inc(v_x_661_);
v___x_666_ = l_Lean_Syntax_isOfKind(v_x_661_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec(v_x_661_);
v___x_667_ = lp_mathlib_Lean_Elab_throwUnsupportedSyntax___at___00elabSuppressCompilationDecl_spec__0___redArg();
return v___x_667_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_668_ = lean_st_ref_get(v_a_663_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = l_Lean_Syntax_getArg(v_x_661_, v___x_669_);
lean_dec(v_x_661_);
v___x_671_ = lean_alloc_closure((void*)(l_Lean_realizeGlobalConstNoOverload___boxed), 4, 1);
lean_closure_set(v___x_671_, 0, v___x_670_);
v___x_672_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_671_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v_env_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v_env_674_ = lean_ctor_get(v___x_668_, 0);
lean_inc_ref(v_env_674_);
lean_dec(v___x_668_);
v___x_675_ = 0;
v___x_676_ = lp_ttc_Ttc_Audit_reportOn(v_env_674_, v_a_673_, v___x_675_);
v___x_677_ = lp_mathlib_Lean_logInfo___at___00Mathlib_CrossRef_traceCrossRefs_spec__1(v___x_676_, v_a_662_, v_a_663_);
return v___x_677_;
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v___x_668_);
v_a_678_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_672_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_672_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReport____1___boxed(lean_object* v_x_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReport____1(v_x_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReportOfType____1(lean_object* v_x_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = ((lean_object*)(lp_ttc_command_x23closureReportOfType___00__closed__1));
lean_inc(v_x_706_);
v___x_711_ = l_Lean_Syntax_isOfKind(v_x_706_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_dec(v_x_706_);
v___x_712_ = lp_mathlib_Lean_Elab_throwUnsupportedSyntax___at___00elabSuppressCompilationDecl_spec__0___redArg();
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_713_ = lean_st_ref_get(v_a_708_);
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = l_Lean_Syntax_getArg(v_x_706_, v___x_714_);
lean_dec(v_x_706_);
v___x_716_ = lean_alloc_closure((void*)(l_Lean_realizeGlobalConstNoOverload___boxed), 4, 1);
lean_closure_set(v___x_716_, 0, v___x_715_);
v___x_717_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_716_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_env_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v_env_719_ = lean_ctor_get(v___x_713_, 0);
lean_inc_ref(v_env_719_);
lean_dec(v___x_713_);
v___x_720_ = lp_ttc_Ttc_Audit_reportOn(v_env_719_, v_a_718_, v___x_711_);
v___x_721_ = lp_mathlib_Lean_logInfo___at___00Mathlib_CrossRef_traceCrossRefs_spec__1(v___x_720_, v_a_707_, v_a_708_);
return v___x_721_;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v___x_713_);
v_a_722_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_717_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_717_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReportOfType____1___boxed(lean_object* v_x_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = lp_ttc___aux__Ttc__Audit__ClosureCheck______elabRules__command_x23closureReportOfType____1(v_x_730_, v_a_731_, v_a_732_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
return v_res_734_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Model_Pseudocode(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Model_Theorem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Audit_ClosureCheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Model_Pseudocode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Model_Theorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
