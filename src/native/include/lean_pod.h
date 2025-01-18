#pragma once

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <lean/lean.h>

typedef unsigned char* lean_pod_byte_ptr;

/// @param sz must be less than `LEAN_MAX_SMALL_OBJECT_SIZE`
static inline void* lean_pod_alloc(size_t sz) {
#ifdef LEAN_POD_ALLOC_NATIVE
    return malloc(sz);
#else
    return (void*)lean_alloc_small_object(sz);
#endif
}

/// @param sz must be less than `LEAN_MAX_SMALL_OBJECT_SIZE`
static inline void* lean_pod_calloc(size_t sz) {
#ifdef LEAN_POD_ALLOC_NATIVE
    return calloc(1, sz);
#else
    void* p = (void*)lean_alloc_small_object(sz);
    memset(p, 0, sz);
    return p;
#endif
}

static inline void lean_pod_free(void* p) {
#ifdef LEAN_POD_ALLOC_NATIVE
    free(p);
#else
    lean_free_small_object((lean_object*)p);
#endif
}

static void lean_pod_default_finalize(void* br) {}
static void lean_pod_default_foreach(void* br, b_lean_obj_arg f) {}

static inline lean_object* lean_mk_tuple2(lean_object* fst, lean_object* snd) {
    lean_object* result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, fst);
    lean_ctor_set(result, 1, snd);
    return result;
}

static inline lean_object* lean_mk_tuple3(lean_object* first, lean_object* second, lean_object* third) {
    lean_object* pair1 = lean_alloc_ctor(0, 2, 0);
    lean_object* pair2 = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair1, 0, first);
    lean_ctor_set(pair1, 1, pair2);
    lean_ctor_set(pair2, 0, second);
    lean_ctor_set(pair2, 1, third);
    return pair1;
}

static inline lean_object* lean_mk_tuple4(lean_object* first, lean_object* second, lean_object* third, lean_object* fourth) {
    lean_object* pair1 = lean_alloc_ctor(0, 2, 0);
    lean_object* pair2 = lean_alloc_ctor(0, 2, 0);
    lean_object* pair3 = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair1, 0, first);
    lean_ctor_set(pair1, 1, pair2);
    lean_ctor_set(pair2, 0, second);
    lean_ctor_set(pair2, 1, pair3);
    lean_ctor_set(pair3, 0, third);
    lean_ctor_set(pair3, 1, fourth);
    return pair1;
}

static inline lean_object* lean_mk_option_none() {
    return lean_box(0);
}

static inline lean_object* lean_mk_option_some(lean_object* value) {
    lean_object* result = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(result, 0, value);
    return result;
}

static inline int lean_option_is_some(b_lean_obj_arg opt) {
    return !lean_is_scalar(opt);
}

// NOT \0 terminated
static inline const char* lean_pod_Substring_cptr(b_lean_obj_arg ss) {
    return lean_string_cstr(lean_ctor_get(ss, 0)) + lean_usize_of_nat(lean_ctor_get(ss, 1));
}

static inline size_t lean_pod_Substring_utf8_byte_size(b_lean_obj_arg ss) {
    return lean_usize_of_nat(lean_ctor_get(ss, 2)) - lean_usize_of_nat(lean_ctor_get(ss, 1));
}

#define LEAN_POD_EStateM_Result_ok_LAYOUT 0, 2, 0, 0, 0, 0, 0
#define LEAN_POD_EStateM_Result_ok_value BOX, 0, LEAN_POD_EStateM_Result_ok_LAYOUT
#define LEAN_POD_EStateM_Result_ok_state BOX, 1, LEAN_POD_EStateM_Result_ok_LAYOUT
#define LEAN_POD_EStateM_Result_error_LAYOUT 1, 2, 0, 0, 0, 0, 0
#define LEAN_POD_EStateM_Result_error_error BOX, 0, LEAN_POD_EStateM_Result_error_LAYOUT
#define LEAN_POD_EStateM_Result_error_state BOX, 1, LEAN_POD_EStateM_Result_error_LAYOUT

#define LEAN_POD_CTOR_GET_BOX(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i) lean_ctor_get(obj, i)
#define LEAN_POD_CTOR_GET_USIZE(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i) lean_ctor_get_usize(obj, ty_box + i)
#define LEAN_POD_CTOR_GET_U64(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i) lean_ctor_get_uint64(obj, (ty_box + ty_usize) * sizeof(void*) + i * 8)
#define LEAN_POD_CTOR_GET_F64(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i) lean_ctor_get_float(obj, (ty_box + ty_usize) * sizeof(void*) + i * 8)
#define LEAN_POD_CTOR_GET_U32(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i) lean_ctor_get_uint32(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + i * 4)
#define LEAN_POD_CTOR_GET_F32(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i) lean_ctor_get_float32(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + i * 4)
#define LEAN_POD_CTOR_GET_U16(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i) lean_ctor_get_uint16(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + ty_4 * 4 + i * 2)
#define LEAN_POD_CTOR_GET_U8(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i) lean_ctor_get_uint8(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + ty_4 * 4 + ty_2 * 2 + i)

#define LEAN_POD_CTOR_SET_BOX(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i, val) lean_ctor_set(obj, i, val)
#define LEAN_POD_CTOR_SET_USIZE(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i, val) lean_ctor_set_usize(obj, ty_box + i, val)
#define LEAN_POD_CTOR_SET_U64(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i, val) lean_ctor_set_uint64(obj, (ty_box + ty_usize) * sizeof(void*) + i * 8, val)
#define LEAN_POD_CTOR_SET_F64(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i, val) lean_ctor_set_float(obj, (ty_box + ty_usize) * sizeof(void*) + i * 8, val)
#define LEAN_POD_CTOR_SET_U32(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i, val) lean_ctor_set_uint32(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + i * 4, val)
#define LEAN_POD_CTOR_SET_F32(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i, val) lean_ctor_set_float32(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + i * 4, val)
#define LEAN_POD_CTOR_SET_U16(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i, val) lean_ctor_set_uint16(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + ty_4 * 4 + i * 2, val)
#define LEAN_POD_CTOR_SET_U8(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1, obj, i, val) lean_ctor_set_uint8(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + ty_4 * 4 + ty_2 * 2 + i, val)

#define LEAN_POD_CTOR_GET_(obj, typ, i, ...) LEAN_POD_CTOR_GET_##typ(__VA_ARGS__, (obj), (i))
#define LEAN_POD_CTOR_SET_(obj, val, typ, i, ...) LEAN_POD_CTOR_SET_##typ(__VA_ARGS__, (obj), (i), (val))

// `(obj, typ, idx, tag, nbox, nusize, n8, n4, n2, n1)`:
// * `obj`: lean ctor object;
// * `typ`: field's type, one of `BOX` `USIZE` `U8` `U16` `U32` `U64` `F64`;
// * `idx`: field's index among fields of the same type (`F64` and `U64` share indices);
// * `tag`: ctor tag
// * `n..`: number of ctor fields of corresponding type.
// Can be used with a macro defining type's and field's layouts:
// ```
// #define T 0, 1, 2, 3, 4, 5, 6
// #define T_a U32, 2, T
// ...
// LEAN_POD_CTOR_GET(obj, T_a)
// ```
#define LEAN_POD_CTOR_GET(...) LEAN_POD_CTOR_GET_(__VA_ARGS__)

// `(obj, val, typ, idx, tag, nbox, nusize, n8, n4, n2, n1)`:
// * `obj`: lean ctor object;
// * `val`: c value to be set;
// * `typ`: field's type, one of `BOX` `USIZE` `U8` `U16` `U32` `U64` `F64`;
// * `idx`: field's index among fields of the same type (`F64` and `U64` share indices);
// * `tag`: ctor tag
// * `n..`: number of ctor fields of corresponding type.
// Can be used with a macro defining type's and field's layouts:
// ```
// #define T 0, 1, 2, 3, 4, 5, 6
// #define T_a U32, 2, T
// ...
// LEAN_POD_CTOR_SET(obj, 42, T_a)
// ```
#define LEAN_POD_CTOR_SET(...) LEAN_POD_CTOR_SET_(__VA_ARGS__)

#define LEAN_POD_ALLOC_CTOR_(tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1)\
lean_alloc_ctor(tag, ty_box, ty_usize * sizeof(void*) + ty_8 * 8 + ty_4 * 4 + ty_2 * 2 + ty_1)

// `LEAN_POD_ALLOC_CTOR(LAYOUT)`
#define LEAN_POD_ALLOC_CTOR(...) LEAN_POD_ALLOC_CTOR_(__VA_ARGS__)

#define LEAN_POD_IS_(obj, tag, ty_box, ty_usize, ty_8, ty_4, ty_2, ty_1)\
(lean_obj_tag(obj) == tag)

// `LEAN_POD_IS(obj, LAYOUT)`
#define LEAN_POD_IS(...) LEAN_POD_IS_(__VA_ARGS__)

#define LEAN_POD_DECLARE_EXTERNAL_CLASS(name, cty)\
typedef lean_object* lean_##name;\
extern lean_external_class* lean_##name##_class;\
static inline cty lean_##name##_unbox(b_lean_obj_arg lean_value) {\
    return (cty) lean_get_external_data(lean_value);\
}\
static inline cty lean_##name##_fromRepr(b_lean_obj_arg lean_value) {\
    return (cty) lean_##name##_unbox(lean_value);\
}

#define LEAN_POD_DEFINE_EXTERNAL_CLASS(name)\
lean_external_class* lean_##name##_class;

#define LEAN_POD_INITIALIZE_EXTERNAL_CLASS(name, finalize, foreach)\
lean_##name##_class = lean_register_external_class(finalize, foreach);

#define LEAN_POD_INITIALIZE_EXTERNAL_CLASS_S(name)\
LEAN_POD_INITIALIZE_EXTERNAL_CLASS(name, lean_##name##_finalize, lean_##name##_foreach)

#define LEAN_POD_TYPE_ALIAS(name, cType, name2, cType2)\
typedef lean_##name2 lean_##name;\
static inline lean_object* lean_##name##_box(cType cvalue) { return lean_##name2##_box((cType2)cvalue); }\
static inline cType lean_##name##_unbox(b_lean_obj_arg lvalue) { return (cType)lean_##name2##_unbox(lvalue); }\
static inline cType lean_##name##_fromRepr(lean_##name rvalue) { return (cType)lean_##name2##_fromRepr((lean_##name2)rvalue); }\
static inline lean_##name lean_##name##_toRepr(cType cvalue) { return (lean_##name)lean_##name2##_toRepr((cType2)cvalue); }

#define LEAN_POD_PTR_ALIAS(name, cType)\
LEAN_POD_TYPE_ALIAS(name, cType, pod_Ptr, void*)

LEAN_POD_DECLARE_EXTERNAL_CLASS(pod_Ptr, void*) // TODO: represent as USize instead of external class (how?)

#define lean_pod_Ptr_toRepr lean_pod_Ptr_box
static inline lean_object* lean_pod_Ptr_box(void* cvalue) {\
    return lean_alloc_external(lean_pod_Ptr_class, cvalue);\
}


// # Signed integers

#define LEAN_POD_STATIC_INTEGER(bits, lfnsuffix)\
typedef uint##bits##_t lean_pod_Int##bits;\
static inline int##bits##_t lean_pod_Int##bits##_fromRepr(lean_pod_Int##bits x) {  return (int##bits##_t)x; }\
static inline int##bits##_t lean_pod_Int##bits##_unbox(b_lean_obj_arg obj) { return lean_pod_Int##bits##_fromRepr(lean_unbox##lfnsuffix(obj)); }\
static inline uint##bits##_t lean_pod_Int##bits##_toRepr(int##bits##_t x) { return (uint##bits##_t)x; }\
static inline lean_object* lean_pod_Int##bits##_box(int##bits##_t x) { return lean_box##lfnsuffix(lean_pod_Int##bits##_toRepr(x)); }

LEAN_POD_STATIC_INTEGER(8, )
LEAN_POD_STATIC_INTEGER(16, )
LEAN_POD_STATIC_INTEGER(32, _uint32)
LEAN_POD_STATIC_INTEGER(64, _uint64)


// # UFixnum

typedef lean_object* lean_pod_UFixnum;

#define lean_pod_UFixnum_toRepr lean_box
#define lean_pod_UFixnum_box lean_box
#define lean_pod_UFixnum_fromRepr lean_unbox
#define lean_pod_UFixnum_unbox lean_unbox


// # Storable

/// @returns @& Nat
static inline b_lean_obj_res lean_pod_Storable_byteSize(b_lean_obj_arg storable) {
    return lean_ctor_get(storable, 0);
}

/// @returns @& Nat
static inline b_lean_obj_res lean_pod_Storable_alignment(b_lean_obj_arg storable) {
    return lean_ctor_get(storable, 1);
}


// # WriteBytes

#define LEAN_POD_WriteBytes_LAYOUT 0, 6, 0, 0, 0, 0, 0

// Function taking 8 boxed arguments: `0`, `size : Nat`, `align : Nat`, `BytesRef`, `offset : Nat`, `value : α`, `0`, `0`, and returning `EStateM.Result Empty σ Unit`
#define LEAN_POD_WriteBytes_writeBytesRefOffUnal BOX, 0, LEAN_POD_WriteBytes_LAYOUT
// Function taking 5 boxed arguments: `0`, `align : Nat`, `BytesRef`, `value : α`, `0`, and returning `EStateM.Result Empty σ Unit`
#define LEAN_POD_WriteBytes_writeBytesRefUnal BOX, 1, LEAN_POD_WriteBytes_LAYOUT
// Function taking 8 boxed arguments: `0`, `size : Nat`, `align : Nat`, `BytesRef`, `i : Nat`, `value : α`, `0`, `0`, and returning `EStateM.Result Empty σ Unit`
#define LEAN_POD_WriteBytes_writeBytesRefOffElUnal BOX, 2, LEAN_POD_WriteBytes_LAYOUT
// Function taking 9 boxed arguments: `0`, `size : Nat`, `align : Nat`, `BytesRef`, `offset : Nat`, `value : α`, `0`, `0`, `0`, and returning `EStateM.Result Empty σ Unit`
#define LEAN_POD_WriteBytes_writeBytesRefOff BOX, 3, LEAN_POD_WriteBytes_LAYOUT
// Function taking 4 boxed arguments: `0`, `BytesRef`, `value : α`, `0`, and returning `EStateM.Result Empty σ Unit`
#define LEAN_POD_WriteBytes_writeBytesRef BOX, 4, LEAN_POD_WriteBytes_LAYOUT
// Function taking 7 boxed arguments: `0`, `size : Nat`, `BytesRef`, `i : Nat`, `value : α`, `0`, `0`, and returning `EStateM.Result Empty σ Unit`
#define LEAN_POD_WriteBytes_writeBytesRefOffEl BOX, 5, LEAN_POD_WriteBytes_LAYOUT


// # ReadBytes

#define LEAN_POD_ReadBytes_LAYOUT 0, 12, 0, 0, 0, 0, 0

// Function taking 7 boxed arguments: `0`, `size : Nat`, `align : Nat`, `BytesRef`, `offset : Nat`, `0`, `0`, and returning `EStateM.Result Empty σ α`
#define LEAN_POD_ReadBytes_readBytesRefOffUnal BOX, 0, LEAN_POD_ReadBytes_LAYOUT
// Function taking 4 boxed arguments: `0`, `align : Nat`, `BytesRef`, `0`, and returning `EStateM.Result Empty σ α`
#define LEAN_POD_ReadBytes_readBytesRefUnal BOX, 1, LEAN_POD_ReadBytes_LAYOUT
// Function taking 7 boxed arguments: `0`, `size : Nat`, `align : Nat`, `BytesRef`, `i : Nat`, `0`, `0`, and returning `EStateM.Result Empty σ α`
#define LEAN_POD_ReadBytes_readBytesRefOffElUnal BOX, 2, LEAN_POD_ReadBytes_LAYOUT
// Function taking 8 boxed arguments: `0`, `size : Nat`, `align : Nat`, `BytesRef`, `offset : Nat`, `0`, `0`, `0`, and returning `EStateM.Result Empty σ α`
#define LEAN_POD_ReadBytes_readBytesRefOff BOX, 3, LEAN_POD_ReadBytes_LAYOUT
// Function taking 3 boxed arguments: `0`, `BytesRef`, `0`, and returning `EStateM.Result Empty σ α`
#define LEAN_POD_ReadBytes_readBytesRef BOX, 4, LEAN_POD_ReadBytes_LAYOUT
// Function taking 6 boxed arguments: `0`, `size : Nat`, `BytesRef`, `i : Nat`, `0`, `0`, and returning `EStateM.Result Empty σ α`
#define LEAN_POD_ReadBytes_readBytesRefOffEl BOX, 5, LEAN_POD_ReadBytes_LAYOUT
#define LEAN_POD_ReadBytes_readBytesViewOffUnal BOX, 6, LEAN_POD_ReadBytes_LAYOUT
#define LEAN_POD_ReadBytes_readBytesViewUnal BOX, 7, LEAN_POD_ReadBytes_LAYOUT
#define LEAN_POD_ReadBytes_readBytesViewOffElUnal BOX, 8, LEAN_POD_ReadBytes_LAYOUT
#define LEAN_POD_ReadBytes_readBytesViewOff BOX, 9, LEAN_POD_ReadBytes_LAYOUT
#define LEAN_POD_ReadBytes_readBytesView BOX, 10, LEAN_POD_ReadBytes_LAYOUT
#define LEAN_POD_ReadBytes_readBytesViewOffEl BOX, 11, LEAN_POD_ReadBytes_LAYOUT


// # OnFinalize

LEAN_POD_DECLARE_EXTERNAL_CLASS(pod_OnFinalize, lean_object*)
LEAN_POD_DECLARE_EXTERNAL_CLASS(pod_OnFinalizeMut, lean_object*)


// # BytesView

typedef struct {
    lean_object* owner; // NOT NULLABLE
    unsigned char* ptr;
} lean_pod_BytesView_data;

LEAN_POD_DECLARE_EXTERNAL_CLASS(pod_BytesView, lean_pod_BytesView_data*)

static inline lean_obj_res lean_pod_BytesView_box (lean_pod_byte_ptr ptr, lean_obj_arg owner) {
    lean_pod_BytesView_data* bv = (lean_pod_BytesView_data*)lean_pod_alloc(sizeof(lean_pod_BytesView_data));
    bv->owner = owner;
    bv->ptr = ptr;
    return lean_alloc_external(lean_pod_BytesView_class, (void*)bv);
}

#define lean_pod_BytesView_toRepr lean_pod_BytesView_box


// # BytesRef

LEAN_POD_PTR_ALIAS(pod_BytesRef, lean_pod_byte_ptr)


// # Buffer

typedef struct {
    lean_pod_byte_ptr data;
    void(*free)(void*);
} lean_pod_Buffer_data;

LEAN_POD_DECLARE_EXTERNAL_CLASS(pod_Buffer, lean_pod_Buffer_data*)

static inline lean_obj_res lean_pod_Buffer_box(lean_pod_byte_ptr data, void (*freeFn)(void*)) {
    lean_pod_Buffer_data* buf = (lean_pod_Buffer_data*)lean_pod_alloc(sizeof(lean_pod_Buffer_data));
    buf->data = data;
    buf->free = freeFn;
    return lean_alloc_external(lean_pod_Buffer_class, (void*)buf);
}

#define lean_pod_Buffer_toRepr lean_pod_Buffer_box


// # UVector

LEAN_POD_DECLARE_EXTERNAL_CLASS(pod_UVector, lean_pod_byte_ptr)

static inline lean_obj_res lean_pod_UVector_box(lean_pod_byte_ptr data) {
    return lean_alloc_external(lean_pod_UVector_class, (void*)data);
}

#define lean_pod_UVector_toRepr lean_pod_UVector_box


// # FixnumSlotMap

LEAN_POD_DECLARE_EXTERNAL_CLASS(pod_FixnumSlotMap, struct lean_pod_FixnumSlotMap_data*);


// # Deque

LEAN_POD_DECLARE_EXTERNAL_CLASS(pod_Deque, struct lean_pod_Deque_data*);


// # Byte swapping functions

static inline uint16_t lean_pod_bswap16(uint16_t value) {
    return
    #if defined(__GNUC__) || defined(__clang__)
    __builtin_bswap16(value);
    #elif defined(_MSC_VER)
    _byteswap_ushort(value);
    #else
    (value << 8) | (value >> 8);
    #endif
}

static inline uint32_t lean_pod_bswap32(uint32_t value) {
    return
    #if defined(__GNUC__) || defined(__clang__)
    __builtin_bswap32(value);
    #elif defined(_MSC_VER)
    _byteswap_ulong(value);
    #else
    ((value & UINT32_C(0x000000FF)) << 24) |
    ((value & UINT32_C(0x0000FF00)) <<  8) |
    ((value & UINT32_C(0x00FF0000)) >>  8) |
    ((value & UINT32_C(0xFF000000)) >> 24);
    #endif
}

static inline uint64_t lean_pod_bswap64(uint64_t value) {
    return
    #if defined(__GNUC__) || defined(__clang__)
    __builtin_bswap64(value);
    #elif defined(_MSC_VER)
    _byteswap_uint64(value);
    #else
    ((value & UINT64_C(0xFF00000000000000)) >> 56) |
    ((value & UINT64_C(0x00FF000000000000)) >> 40) |
    ((value & UINT64_C(0x0000FF0000000000)) >> 24) |
    ((value & UINT64_C(0x000000FF00000000)) >>  8) |
    ((value & UINT64_C(0x00000000FF000000)) <<  8) |
    ((value & UINT64_C(0x0000000000FF0000)) << 24) |
    ((value & UINT64_C(0x000000000000FF00)) << 40) |
    ((value & UINT64_C(0x00000000000000FF)) << 56);
    #endif
}


#if defined(__GNUC__) || defined(__clang__)
#define LEAN_POD_ASSUME_ALIGNED(p, t) __builtin_assume_aligned(p, _Alignof(t))
#else
#define LEAN_POD_ASSUME_ALIGNED(p, t) p
#endif

#define LEAN_POD_IDENTITY(x) x

#define LEAN_POD_RWBYTES_INST(suffix, cType, abiType, cToObj, cToAbi, cFromAbi)\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefUnal_##suffix(b_lean_obj_arg a, lean_pod_BytesRef br, lean_obj_arg st) {\
    cType value;\
    memcpy(&value, lean_pod_BytesRef_fromRepr(br), sizeof(cType));\
    return lean_io_result_mk_ok(cToObj(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOffUnal_##suffix(b_lean_obj_arg sz, b_lean_obj_arg a, lean_pod_BytesRef br, b_lean_obj_arg i_nat, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    cType value;\
    memcpy(&value, lean_pod_BytesRef_fromRepr(br) + i, sizeof(cType));\
    return lean_io_result_mk_ok(cToObj(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOffElUnal_##suffix(b_lean_obj_arg sz, b_lean_obj_arg a, lean_pod_BytesRef br, b_lean_obj_arg i_nat, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    cType value;\
    memcpy(&value, lean_pod_BytesRef_fromRepr(br) + i * sizeof(cType), sizeof(cType));\
    return lean_io_result_mk_ok(cToObj(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRef_##suffix(lean_pod_BytesRef br, lean_obj_arg st) {\
    cType value;\
    unsigned char* p = lean_pod_BytesRef_fromRepr(br);\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, cType), sizeof(cType));\
    return lean_io_result_mk_ok(cToObj(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOff_##suffix(b_lean_obj_arg sz, b_lean_obj_arg a, lean_pod_BytesRef br, b_lean_obj_arg i_nat, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    cType value;\
    unsigned char* p = lean_pod_BytesRef_fromRepr(br) + i;\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, cType), sizeof(cType));\
    return lean_io_result_mk_ok(cToObj(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOffEl_##suffix(b_lean_obj_arg sz, lean_pod_BytesRef br, b_lean_obj_arg i_nat, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    cType value;\
    unsigned char* p = lean_pod_BytesRef_fromRepr(br) + i * sizeof(cType);\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, cType), sizeof(cType));\
    return lean_io_result_mk_ok(cToObj(value));\
}\
\
LEAN_EXPORT abiType lean_pod_readBytesViewUnal_##suffix(b_lean_obj_arg a, lean_pod_BytesView bv) {\
    cType value;\
    memcpy(&value, lean_pod_BytesView_fromRepr(bv)->ptr, sizeof(cType));\
    return cToAbi(value);\
}\
LEAN_EXPORT abiType lean_pod_readBytesViewOffUnal_##suffix(b_lean_obj_arg sz, b_lean_obj_arg a, lean_pod_BytesView bv, b_lean_obj_arg i_nat) {\
    size_t i = lean_usize_of_nat(i_nat);\
    cType value;\
    memcpy(&value, lean_pod_BytesView_fromRepr(bv)->ptr + i, sizeof(cType));\
    return cToAbi(value);\
}\
LEAN_EXPORT abiType lean_pod_readBytesViewOffElUnal_##suffix(b_lean_obj_arg sz, b_lean_obj_arg a, lean_pod_BytesView bv, b_lean_obj_arg i_nat) {\
    size_t i = lean_usize_of_nat(i_nat);\
    cType value;\
    memcpy(&value, lean_pod_BytesView_fromRepr(bv)->ptr + i * sizeof(cType), sizeof(cType));\
    return cToAbi(value);\
}\
LEAN_EXPORT abiType lean_pod_readBytesView_##suffix(lean_pod_BytesView bv) {\
    cType value;\
    unsigned char* p = lean_pod_BytesView_fromRepr(bv)->ptr;\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, cType), sizeof(cType));\
    return cToAbi(value);\
}\
LEAN_EXPORT abiType lean_pod_readBytesViewOff_##suffix(b_lean_obj_arg sz, b_lean_obj_arg a, lean_pod_BytesView bv, b_lean_obj_arg i_nat) {\
    size_t i = lean_usize_of_nat(i_nat);\
    cType value;\
    unsigned char* p = lean_pod_BytesView_fromRepr(bv)->ptr + i;\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, cType), sizeof(cType));\
    return cToAbi(value);\
}\
LEAN_EXPORT abiType lean_pod_readBytesViewOffEl_##suffix(b_lean_obj_arg sz, lean_pod_BytesView bv, b_lean_obj_arg i_nat) {\
    size_t i = lean_usize_of_nat(i_nat);\
    cType value;\
    unsigned char* p = lean_pod_BytesView_fromRepr(bv)->ptr + i * sizeof(cType);\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, cType), sizeof(cType));\
    return cToAbi(value);\
}\
\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefUnal_##suffix(b_lean_obj_arg a, lean_pod_BytesRef br, abiType value, lean_obj_arg st) {\
    cType valueC = cFromAbi(value);\
    memcpy(lean_pod_BytesRef_fromRepr(br), &valueC, sizeof(cType));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOffUnal_##suffix(b_lean_obj_arg sz, b_lean_obj_arg a, lean_pod_BytesRef br, b_lean_obj_arg i_nat, abiType value, lean_obj_arg st) {\
    cType valueC = cFromAbi(value);\
    size_t i = lean_usize_of_nat(i_nat);\
    memcpy(lean_pod_BytesRef_fromRepr(br) + i, &valueC, sizeof(cType));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOffElUnal_##suffix(b_lean_obj_arg sz, b_lean_obj_arg a, lean_pod_BytesRef br, b_lean_obj_arg i_nat, abiType value, lean_obj_arg st) {\
    cType valueC = cFromAbi(value);\
    size_t i = lean_usize_of_nat(i_nat);\
    memcpy(lean_pod_BytesRef_fromRepr(br) + i * sizeof(cType), &valueC, sizeof(cType));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRef_##suffix(lean_pod_BytesRef br, abiType value, lean_obj_arg st) {\
    cType valueC = cFromAbi(value);\
    memcpy(LEAN_POD_ASSUME_ALIGNED(lean_pod_BytesRef_fromRepr(br), cType), &valueC, sizeof(cType));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOff_##suffix(b_lean_obj_arg sz, b_lean_obj_arg a, lean_pod_BytesRef br, b_lean_obj_arg i_nat, abiType value, lean_obj_arg st) {\
    cType valueC = cFromAbi(value);\
    size_t i = lean_usize_of_nat(i_nat);\
    unsigned char* p = lean_pod_BytesRef_fromRepr(br) + i;\
    memcpy(LEAN_POD_ASSUME_ALIGNED(p, cType), &valueC, sizeof(cType));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOffEl_##suffix(b_lean_obj_arg sz, lean_pod_BytesRef br, b_lean_obj_arg i_nat, abiType value, lean_obj_arg st) {\
    cType valueC = cFromAbi(value);\
    size_t i = lean_usize_of_nat(i_nat);\
    unsigned char* p = lean_pod_BytesRef_fromRepr(br) + i * sizeof(cType);\
    memcpy(LEAN_POD_ASSUME_ALIGNED(p, cType), &valueC, sizeof(cType));\
    return lean_io_result_mk_ok(lean_box(0));\
}
