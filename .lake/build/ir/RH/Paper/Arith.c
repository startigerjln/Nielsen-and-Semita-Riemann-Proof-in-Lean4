// Lean compiler output
// Module: RH.Paper.Arith
// Imports: Init Mathlib.ModelTheory.Semantics
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
LEAN_EXPORT uint8_t l_RH_Paper_mulFunc;
LEAN_EXPORT lean_object* l_RH_Paper_zeroFunc;
LEAN_EXPORT lean_object* l_RH_Paper_L;
LEAN_EXPORT lean_object* l_RH_Paper_natStructure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_leF___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_leF___elambda__1___boxed(lean_object*);
static lean_object* l_RH_Paper_leF___closed__1;
LEAN_EXPORT lean_object* l_RH_Paper_leF(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_succFunc;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_leRel;
LEAN_EXPORT lean_object* l_RH_Paper_natStructure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_RH_Paper_addFunc;
LEAN_EXPORT lean_object* l_RH_Paper_leF___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Paper_leF___elambda__1(lean_object*);
lean_object* l_Matrix_vecCons___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_RH_Paper_L() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_RH_Paper_zeroFunc() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_RH_Paper_succFunc() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_RH_Paper_addFunc() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_RH_Paper_mulFunc() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_RH_Paper_leRel() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_natStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_nat_dec_eq(x_7, x_4);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_unbox(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_3);
x_10 = lean_apply_1(x_3, x_4);
x_11 = lean_apply_1(x_3, x_6);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_3);
x_13 = lean_apply_1(x_3, x_4);
x_14 = lean_apply_1(x_3, x_6);
x_15 = lean_nat_mul(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_apply_1(x_3, x_4);
x_17 = lean_nat_add(x_16, x_6);
lean_dec(x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_unsigned_to_nat(0u);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_RH_Paper_natStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RH_Paper_natStructure(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_leF___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Fin_cases(x_4, lean_box(0), x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_leF___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RH_Paper_leF___elambda__1___rarg___boxed), 3, 0);
return x_2;
}
}
static lean_object* _init_l_RH_Paper_leF___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_leF(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_RH_Paper_leF___closed__1;
x_6 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_alloc_closure((void*)(l_RH_Paper_leF___elambda__1___rarg___boxed), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_RH_Paper_leRel;
x_10 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_leF___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RH_Paper_leF___elambda__1___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_RH_Paper_leF___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RH_Paper_leF___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_ModelTheory_Semantics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RH_Paper_Arith(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_ModelTheory_Semantics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RH_Paper_L = _init_l_RH_Paper_L();
lean_mark_persistent(l_RH_Paper_L);
l_RH_Paper_zeroFunc = _init_l_RH_Paper_zeroFunc();
lean_mark_persistent(l_RH_Paper_zeroFunc);
l_RH_Paper_succFunc = _init_l_RH_Paper_succFunc();
lean_mark_persistent(l_RH_Paper_succFunc);
l_RH_Paper_addFunc = _init_l_RH_Paper_addFunc();
l_RH_Paper_mulFunc = _init_l_RH_Paper_mulFunc();
l_RH_Paper_leRel = _init_l_RH_Paper_leRel();
lean_mark_persistent(l_RH_Paper_leRel);
l_RH_Paper_leF___closed__1 = _init_l_RH_Paper_leF___closed__1();
lean_mark_persistent(l_RH_Paper_leF___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
