// Lean compiler output
// Module: Ttc.Exec.Cleanup
// Imports: public import Init public meta import Init public import Ttc.Exec.Inputs
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
static const lean_ctor_object lp_ttc_Ttc_degenVacDNF___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_ttc_Ttc_degenVacDNF___closed__0 = (const lean_object*)&lp_ttc_Ttc_degenVacDNF___closed__0_value;
static const lean_ctor_object lp_ttc_Ttc_degenVacDNF___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_degenVacDNF___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_ttc_Ttc_degenVacDNF___closed__1 = (const lean_object*)&lp_ttc_Ttc_degenVacDNF___closed__1_value;
static const lean_ctor_object lp_ttc_Ttc_degenVacDNF___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_ttc_Ttc_degenVacDNF___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_ttc_Ttc_degenVacDNF___closed__2 = (const lean_object*)&lp_ttc_Ttc_degenVacDNF___closed__2_value;
LEAN_EXPORT const lean_object* lp_ttc_Ttc_degenVacDNF = (const lean_object*)&lp_ttc_Ttc_degenVacDNF___closed__2_value;
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Exec_Inputs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Exec_Cleanup(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Exec_Inputs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
