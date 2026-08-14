// Lean compiler output
// Module: Ttc.Dnf
// Imports: public import Init public meta import Init public import Ttc.Model.Prelude
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
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_BForm_holds_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_BForm_holds_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter___redArg(lean_object* v_x_1_, uint8_t v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_, lean_object* v_h__3_5_, lean_object* v_h__4_6_, lean_object* v_h__5_7_, lean_object* v_h__6_8_, lean_object* v_h__7_9_, lean_object* v_h__8_10_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_dec(v_h__8_10_);
lean_dec(v_h__7_9_);
lean_dec(v_h__6_8_);
lean_dec(v_h__5_7_);
lean_dec(v_h__4_6_);
lean_dec(v_h__3_5_);
if (v_x_2_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; 
lean_dec(v_h__1_3_);
v___x_11_ = lean_box(0);
v___x_12_ = lean_apply_1(v_h__2_4_, v___x_11_);
return v___x_12_;
}
else
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_4_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__1_3_, v___x_13_);
return v___x_14_;
}
}
case 1:
{
lean_object* v_a_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_h__8_10_);
lean_dec(v_h__7_9_);
lean_dec(v_h__6_8_);
lean_dec(v_h__5_7_);
lean_dec(v_h__4_6_);
lean_dec(v_h__2_4_);
lean_dec(v_h__1_3_);
v_a_15_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_15_);
lean_dec_ref_known(v_x_1_, 1);
v___x_16_ = lean_box(v_x_2_);
v___x_17_ = lean_apply_2(v_h__3_5_, v_a_15_, v___x_16_);
return v___x_17_;
}
case 2:
{
lean_object* v_a_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_h__8_10_);
lean_dec(v_h__7_9_);
lean_dec(v_h__6_8_);
lean_dec(v_h__5_7_);
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
lean_dec(v_h__1_3_);
v_a_18_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_18_);
lean_dec_ref_known(v_x_1_, 1);
v___x_19_ = lean_box(v_x_2_);
v___x_20_ = lean_apply_2(v_h__4_6_, v_a_18_, v___x_19_);
return v___x_20_;
}
case 3:
{
lean_dec(v_h__8_10_);
lean_dec(v_h__7_9_);
lean_dec(v_h__4_6_);
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
lean_dec(v_h__1_3_);
if (v_x_2_ == 0)
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_23_; 
lean_dec(v_h__5_7_);
v_a_21_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_21_);
v_a_22_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_22_);
lean_dec_ref_known(v_x_1_, 2);
v___x_23_ = lean_apply_2(v_h__6_8_, v_a_21_, v_a_22_);
return v___x_23_;
}
else
{
lean_object* v_a_24_; lean_object* v_a_25_; lean_object* v___x_26_; 
lean_dec(v_h__6_8_);
v_a_24_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_24_);
v_a_25_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_25_);
lean_dec_ref_known(v_x_1_, 2);
v___x_26_ = lean_apply_2(v_h__5_7_, v_a_24_, v_a_25_);
return v___x_26_;
}
}
default: 
{
lean_dec(v_h__6_8_);
lean_dec(v_h__5_7_);
lean_dec(v_h__4_6_);
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
lean_dec(v_h__1_3_);
if (v_x_2_ == 0)
{
lean_object* v_a_27_; lean_object* v_a_28_; lean_object* v___x_29_; 
lean_dec(v_h__7_9_);
v_a_27_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_27_);
v_a_28_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_28_);
lean_dec_ref_known(v_x_1_, 2);
v___x_29_ = lean_apply_2(v_h__8_10_, v_a_27_, v_a_28_);
return v___x_29_;
}
else
{
lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__8_10_);
v_a_30_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_30_);
v_a_31_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_31_);
lean_dec_ref_known(v_x_1_, 2);
v___x_32_ = lean_apply_2(v_h__7_9_, v_a_30_, v_a_31_);
return v___x_32_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter___redArg___boxed(lean_object* v_x_33_, lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_, lean_object* v_h__3_37_, lean_object* v_h__4_38_, lean_object* v_h__5_39_, lean_object* v_h__6_40_, lean_object* v_h__7_41_, lean_object* v_h__8_42_){
_start:
{
uint8_t v_x_78__boxed_43_; lean_object* v_res_44_; 
v_x_78__boxed_43_ = lean_unbox(v_x_34_);
v_res_44_ = lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter___redArg(v_x_33_, v_x_78__boxed_43_, v_h__1_35_, v_h__2_36_, v_h__3_37_, v_h__4_38_, v_h__5_39_, v_h__6_40_, v_h__7_41_, v_h__8_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter(lean_object* v_A_45_, lean_object* v_motive_46_, lean_object* v_x_47_, uint8_t v_x_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_, lean_object* v_h__3_51_, lean_object* v_h__4_52_, lean_object* v_h__5_53_, lean_object* v_h__6_54_, lean_object* v_h__7_55_, lean_object* v_h__8_56_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 0:
{
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
if (v_x_48_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__1_49_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__2_50_, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_50_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__1_49_, v___x_59_);
return v___x_60_;
}
}
case 1:
{
lean_object* v_a_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_a_61_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v_x_47_, 1);
v___x_62_ = lean_box(v_x_48_);
v___x_63_ = lean_apply_2(v_h__3_51_, v_a_61_, v___x_62_);
return v___x_63_;
}
case 2:
{
lean_object* v_a_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_a_64_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_a_64_);
lean_dec_ref_known(v_x_47_, 1);
v___x_65_ = lean_box(v_x_48_);
v___x_66_ = lean_apply_2(v_h__4_52_, v_a_64_, v___x_65_);
return v___x_66_;
}
case 3:
{
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
if (v_x_48_ == 0)
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v___x_69_; 
lean_dec(v_h__5_53_);
v_a_67_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_a_67_);
v_a_68_ = lean_ctor_get(v_x_47_, 1);
lean_inc(v_a_68_);
lean_dec_ref_known(v_x_47_, 2);
v___x_69_ = lean_apply_2(v_h__6_54_, v_a_67_, v_a_68_);
return v___x_69_;
}
else
{
lean_object* v_a_70_; lean_object* v_a_71_; lean_object* v___x_72_; 
lean_dec(v_h__6_54_);
v_a_70_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_a_70_);
v_a_71_ = lean_ctor_get(v_x_47_, 1);
lean_inc(v_a_71_);
lean_dec_ref_known(v_x_47_, 2);
v___x_72_ = lean_apply_2(v_h__5_53_, v_a_70_, v_a_71_);
return v___x_72_;
}
}
default: 
{
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
if (v_x_48_ == 0)
{
lean_object* v_a_73_; lean_object* v_a_74_; lean_object* v___x_75_; 
lean_dec(v_h__7_55_);
v_a_73_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_a_73_);
v_a_74_ = lean_ctor_get(v_x_47_, 1);
lean_inc(v_a_74_);
lean_dec_ref_known(v_x_47_, 2);
v___x_75_ = lean_apply_2(v_h__8_56_, v_a_73_, v_a_74_);
return v___x_75_;
}
else
{
lean_object* v_a_76_; lean_object* v_a_77_; lean_object* v___x_78_; 
lean_dec(v_h__8_56_);
v_a_76_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_a_76_);
v_a_77_ = lean_ctor_get(v_x_47_, 1);
lean_inc(v_a_77_);
lean_dec_ref_known(v_x_47_, 2);
v___x_78_ = lean_apply_2(v_h__7_55_, v_a_76_, v_a_77_);
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter___boxed(lean_object* v_A_79_, lean_object* v_motive_80_, lean_object* v_x_81_, lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_, lean_object* v_h__3_85_, lean_object* v_h__4_86_, lean_object* v_h__5_87_, lean_object* v_h__6_88_, lean_object* v_h__7_89_, lean_object* v_h__8_90_){
_start:
{
uint8_t v_x_128__boxed_91_; lean_object* v_res_92_; 
v_x_128__boxed_91_ = lean_unbox(v_x_82_);
v_res_92_ = lp_ttc___private_Ttc_Dnf_0__Ttc_dnfAux_match__1_splitter(v_A_79_, v_motive_80_, v_x_81_, v_x_128__boxed_91_, v_h__1_83_, v_h__2_84_, v_h__3_85_, v_h__4_86_, v_h__5_87_, v_h__6_88_, v_h__7_89_, v_h__8_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_BForm_holds_match__1_splitter___redArg(lean_object* v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_, lean_object* v_h__3_96_, lean_object* v_h__4_97_, lean_object* v_h__5_98_){
_start:
{
switch(lean_obj_tag(v_x_93_))
{
case 0:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec(v_h__5_98_);
lean_dec(v_h__4_97_);
lean_dec(v_h__3_96_);
lean_dec(v_h__2_95_);
v___x_99_ = lean_box(0);
v___x_100_ = lean_apply_1(v_h__1_94_, v___x_99_);
return v___x_100_;
}
case 1:
{
lean_object* v_a_101_; lean_object* v___x_102_; 
lean_dec(v_h__5_98_);
lean_dec(v_h__4_97_);
lean_dec(v_h__3_96_);
lean_dec(v_h__1_94_);
v_a_101_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_a_101_);
lean_dec_ref_known(v_x_93_, 1);
v___x_102_ = lean_apply_1(v_h__2_95_, v_a_101_);
return v___x_102_;
}
case 2:
{
lean_object* v_a_103_; lean_object* v___x_104_; 
lean_dec(v_h__5_98_);
lean_dec(v_h__4_97_);
lean_dec(v_h__2_95_);
lean_dec(v_h__1_94_);
v_a_103_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v_x_93_, 1);
v___x_104_ = lean_apply_1(v_h__3_96_, v_a_103_);
return v___x_104_;
}
case 3:
{
lean_object* v_a_105_; lean_object* v_a_106_; lean_object* v___x_107_; 
lean_dec(v_h__5_98_);
lean_dec(v_h__3_96_);
lean_dec(v_h__2_95_);
lean_dec(v_h__1_94_);
v_a_105_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_a_105_);
v_a_106_ = lean_ctor_get(v_x_93_, 1);
lean_inc(v_a_106_);
lean_dec_ref_known(v_x_93_, 2);
v___x_107_ = lean_apply_2(v_h__4_97_, v_a_105_, v_a_106_);
return v___x_107_;
}
default: 
{
lean_object* v_a_108_; lean_object* v_a_109_; lean_object* v___x_110_; 
lean_dec(v_h__4_97_);
lean_dec(v_h__3_96_);
lean_dec(v_h__2_95_);
lean_dec(v_h__1_94_);
v_a_108_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_a_108_);
v_a_109_ = lean_ctor_get(v_x_93_, 1);
lean_inc(v_a_109_);
lean_dec_ref_known(v_x_93_, 2);
v___x_110_ = lean_apply_2(v_h__5_98_, v_a_108_, v_a_109_);
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* lp_ttc___private_Ttc_Dnf_0__Ttc_BForm_holds_match__1_splitter(lean_object* v_A_111_, lean_object* v_motive_112_, lean_object* v_x_113_, lean_object* v_h__1_114_, lean_object* v_h__2_115_, lean_object* v_h__3_116_, lean_object* v_h__4_117_, lean_object* v_h__5_118_){
_start:
{
switch(lean_obj_tag(v_x_113_))
{
case 0:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v_h__5_118_);
lean_dec(v_h__4_117_);
lean_dec(v_h__3_116_);
lean_dec(v_h__2_115_);
v___x_119_ = lean_box(0);
v___x_120_ = lean_apply_1(v_h__1_114_, v___x_119_);
return v___x_120_;
}
case 1:
{
lean_object* v_a_121_; lean_object* v___x_122_; 
lean_dec(v_h__5_118_);
lean_dec(v_h__4_117_);
lean_dec(v_h__3_116_);
lean_dec(v_h__1_114_);
v_a_121_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v_x_113_, 1);
v___x_122_ = lean_apply_1(v_h__2_115_, v_a_121_);
return v___x_122_;
}
case 2:
{
lean_object* v_a_123_; lean_object* v___x_124_; 
lean_dec(v_h__5_118_);
lean_dec(v_h__4_117_);
lean_dec(v_h__2_115_);
lean_dec(v_h__1_114_);
v_a_123_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v_x_113_, 1);
v___x_124_ = lean_apply_1(v_h__3_116_, v_a_123_);
return v___x_124_;
}
case 3:
{
lean_object* v_a_125_; lean_object* v_a_126_; lean_object* v___x_127_; 
lean_dec(v_h__5_118_);
lean_dec(v_h__3_116_);
lean_dec(v_h__2_115_);
lean_dec(v_h__1_114_);
v_a_125_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_a_125_);
v_a_126_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_a_126_);
lean_dec_ref_known(v_x_113_, 2);
v___x_127_ = lean_apply_2(v_h__4_117_, v_a_125_, v_a_126_);
return v___x_127_;
}
default: 
{
lean_object* v_a_128_; lean_object* v_a_129_; lean_object* v___x_130_; 
lean_dec(v_h__4_117_);
lean_dec(v_h__3_116_);
lean_dec(v_h__2_115_);
lean_dec(v_h__1_114_);
v_a_128_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_a_128_);
v_a_129_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_a_129_);
lean_dec_ref_known(v_x_113_, 2);
v___x_130_ = lean_apply_2(v_h__5_118_, v_a_128_, v_a_129_);
return v___x_130_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ttc_Ttc_Model_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ttc_Ttc_Dnf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ttc_Ttc_Model_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
