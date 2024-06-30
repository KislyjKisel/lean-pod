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

#define LEAN_POD_CTOR_GET_BOX_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i) lean_ctor_get(obj, i)
#define LEAN_POD_CTOR_GET_USIZE_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i) lean_ctor_get_usize(obj, ty_box + i)
#define LEAN_POD_CTOR_GET_U64_D_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i, tyn) lean_ctor_get_##tyn(obj, (ty_box + ty_usize) * sizeof(void*) + i * 8)
#define LEAN_POD_CTOR_GET_U32_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i) lean_ctor_get_uint32(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + i * 4)
#define LEAN_POD_CTOR_GET_U16_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i) lean_ctor_get_uint16(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + ty_4 * 4 + i * 2)
#define LEAN_POD_CTOR_GET_U8_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i) lean_ctor_get_uint8(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + ty_4 * 4 + ty_2 * 2 + i)

#define LEAN_POD_CTOR_SET_BOX_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i, val) lean_ctor_set(obj, i, val)
#define LEAN_POD_CTOR_SET_USIZE_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i, val) lean_ctor_set_usize(obj, ty_box + i, val)
#define LEAN_POD_CTOR_SET_U64_D_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i, tyn, val) lean_ctor_get_##tyn(obj, (ty_box + ty_usize) * sizeof(void*) + i * 8, val)
#define LEAN_POD_CTOR_SET_U32_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i, val) lean_ctor_set_uint32(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + i * 4, val)
#define LEAN_POD_CTOR_SET_U16_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i, val) lean_ctor_set_uint16(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + ty_4 * 4 + i * 2, val)
#define LEAN_POD_CTOR_SET_U8_(ty_box, ty_usize, ty_8, ty_4, ty_2, obj, i, val) lean_ctor_set_uint8(obj, (ty_box + ty_usize) * sizeof(void*) + ty_8 * 8 + ty_4 * 4 + ty_2 * 2 + i, val)

#define LEAN_POD_CTOR_GET_BOX(...) LEAN_POD_CTOR_GET_BOX_(__VA_ARGS__)
#define LEAN_POD_CTOR_GET_USIZE(...) LEAN_POD_CTOR_GET_USIZE_(__VA_ARGS__)
#define LEAN_POD_CTOR_GET_U64_D(...) LEAN_POD_CTOR_GET_U64_D_(__VA_ARGS__)
#define LEAN_POD_CTOR_GET_U32(...) LEAN_POD_CTOR_GET_U32_(__VA_ARGS__)
#define LEAN_POD_CTOR_GET_U16(...) LEAN_POD_CTOR_GET_U16_(__VA_ARGS__)
#define LEAN_POD_CTOR_GET_U8(...) LEAN_POD_CTOR_GET_U8_(__VA_ARGS__)

#define LEAN_POD_CTOR_SET_BOX(...) LEAN_POD_CTOR_SET_BOX_(__VA_ARGS__)
#define LEAN_POD_CTOR_SET_USIZE(...) LEAN_POD_CTOR_SET_USIZE_(__VA_ARGS__)
#define LEAN_POD_CTOR_SET_U64_D(...) LEAN_POD_CTOR_SET_U64_D_(__VA_ARGS__)
#define LEAN_POD_CTOR_SET_U32(...) LEAN_POD_CTOR_SET_U32_(__VA_ARGS__)
#define LEAN_POD_CTOR_SET_U16(...) LEAN_POD_CTOR_SET_U16_(__VA_ARGS__)
#define LEAN_POD_CTOR_SET_U8(...) LEAN_POD_CTOR_SET_U8_(__VA_ARGS__)


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

#define LEAN_POD_TYPE_ALIAS(name, cReprType, cType, name2, cReprType2, cType2)\
typedef lean_##name2 lean_##name;\
static inline lean_object* lean_##name##_box(cType cvalue) { return lean_##name2##_box((cType2)cvalue); }\
static inline cType lean_##name##_unbox(b_lean_obj_arg lvalue) { return (cType)lean_##name2##_unbox(lvalue); }\
static inline cType lean_##name##_fromRepr(cReprType rvalue) { return (cType)lean_##name2##_fromRepr((cReprType2)rvalue); }\
static inline cReprType lean_##name##_toRepr(cType cvalue) { return (cReprType)lean_##name2##_toRepr((cType2)cvalue); }

#define LEAN_POD_PTR_ALIAS(name, cType)\
LEAN_POD_TYPE_ALIAS(name, lean_object*, cType, pod_Ptr, lean_object*, void*)

LEAN_POD_DECLARE_EXTERNAL_CLASS(pod_Ptr, void*) // TODO: represent as USize instead of external class (how?)

#define lean_pod_Ptr_toRepr lean_pod_Ptr_box
static inline lean_object* lean_pod_Ptr_box(void* cvalue) {\
    return lean_alloc_external(lean_pod_Ptr_class, cvalue);\
}


// # Float32

static inline uint32_t lean_pod_Float32_toBits(float x) {
    union {
        float f32;
        uint32_t u32;
    } u;
    u.f32 = x;
    return u.u32;
}

static inline lean_obj_res lean_pod_Float32_box(float x) {
    return lean_box_uint32(lean_pod_Float32_toBits(x));
}

static inline float lean_pod_Float32_fromBits(uint32_t x) {
    union {
        uint32_t u32;
        float f32;
    } u;
    u.u32 = x;
    return u.f32;
}

static inline float lean_pod_Float32_unbox(b_lean_obj_arg obj) {
    return lean_pod_Float32_fromBits(lean_unbox_uint32(obj));
}


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

// Returns a function taking 4 boxed args:
// 0, BytesRef, value : A, 0, and returning `ST.Result Unit`
static inline b_lean_obj_res lean_pod_WriteBytes_writeBytesRef(b_lean_obj_arg writeBytes) {
    return lean_ctor_get(writeBytes, 4);
}

// Returns a function taking 7 boxed args:
// 0, size : USize, BytesRef, i : USize, value : A, 0, 0, and returning `ST.Result Unit`.
static inline b_lean_obj_res lean_pod_WriteBytes_writeBytesRefOffEl(b_lean_obj_arg writeBytes) {
    return lean_ctor_get(writeBytes, 5);
}


// # ReadBytes

// Returns a function taking 3 boxed args:
// 0, BytesRef, 0, and returning `ST.Result A`
static inline b_lean_obj_res lean_pod_ReadBytes_readBytesRef(b_lean_obj_arg readBytes) {
    return lean_ctor_get(readBytes, 4);
}


// Returns a function taking 6 boxed args:
// 0, size : USize, BytesRef, i : USize, 0, 0, and returning `ST.Result A`
static inline b_lean_obj_res lean_pod_ReadBytes_readBytesRefOffEl(b_lean_obj_arg readBytes) {
    return lean_ctor_get(readBytes, 5);
}


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
