// Lean compiler output
// Module: RH.Paper.ProofI
// Imports: Init RH.Paper.Arith
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
LEAN_EXPORT lean_object* l_RH_Paper_TranslationPair_RL(lean_object*, lean_object*);
extern lean_object* l_RH_Paper_L;
lean_object* l_FirstOrder_Language_BoundedFormula_not(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_FirstOrder_Language_BoundedFormula_iff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_impS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_TranslationPair_RC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_neg(lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_iffS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_neg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_RH_Paper_L;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_FirstOrder_Language_BoundedFormula_not(x_2, lean_box(0), x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_iffS(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_RH_Paper_L;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_FirstOrder_Language_BoundedFormula_iff(x_3, lean_box(0), x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_impS(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_TranslationPair_RL(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_TranslationPair_RC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_RH_Paper_Arith(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RH_Paper_ProofI(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RH_Paper_Arith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
