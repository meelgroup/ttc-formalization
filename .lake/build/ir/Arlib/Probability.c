// Lean compiler output
// Module: Arlib.Probability
// Imports: public import Init public meta import Init public import Arlib.Probability.TV public import Arlib.Probability.Rejection public import Arlib.Probability.SubgaussianTail public import Arlib.Probability.UniformOn public import Arlib.Probability.RunPlumbing public import Arlib.Probability.Geometric public import Arlib.Probability.RejectionRounds public import Arlib.Probability.TVTensor public import Arlib.Probability.TVKernel public import Arlib.Probability.DeltaIndependence public import Arlib.Probability.DependenceCovariance public import Arlib.Probability.InhomogeneousMarkov public import Arlib.Probability.AccuracyRecursion public import Arlib.Probability.AccuracySecondMoment public import Arlib.Probability.AccuracyLowerRecursion public import Arlib.Probability.TVKernelHeterogeneous public import Arlib.Probability.TVTimeout public import Arlib.Probability.AdaptiveTVTelescope public import Arlib.Probability.AdaptiveTVTelescopeMixture public import Arlib.Probability.NuIndepTensor
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_TV(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_Rejection(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_SubgaussianTail(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_UniformOn(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_RunPlumbing(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_Geometric(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_RejectionRounds(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_TVTensor(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_TVKernel(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_DeltaIndependence(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_DependenceCovariance(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_InhomogeneousMarkov(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_AccuracyRecursion(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_AccuracySecondMoment(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_AccuracyLowerRecursion(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_TVKernelHeterogeneous(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_TVTimeout(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_AdaptiveTVTelescope(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_AdaptiveTVTelescopeMixture(uint8_t builtin);
lean_object* initialize_ttc_Arlib_Probability_NuIndepTensor(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Arlib_Probability(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_TV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_Rejection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_SubgaussianTail(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_UniformOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_RunPlumbing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_Geometric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_RejectionRounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_TVTensor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_TVKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_DeltaIndependence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_DependenceCovariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_InhomogeneousMarkov(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_AccuracyRecursion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_AccuracySecondMoment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_AccuracyLowerRecursion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_TVKernelHeterogeneous(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_TVTimeout(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_AdaptiveTVTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_AdaptiveTVTelescopeMixture(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Arlib_Probability_NuIndepTensor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
