#pragma once

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <lean/lean.h>

/// @param sz must be divisible by `LEAN_OBJECT_SIZE_DELTA`
static inline void* lean_pod_alloc(size_t sz) {
#ifdef LEAN_POD_ALLOC_NATIVE
    return malloc(sz);
#else
    return (void*)lean_alloc_small_object(sz);
#endif
}

/// @param sz must be divisible by `LEAN_OBJECT_SIZE_DELTA`
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

/// @returns @& Storable
static inline b_lean_obj_res lean_pod_WriteBytes_storable(b_lean_obj_arg writeBytes) {
    return lean_ctor_get(writeBytes, 0);
}

// Returns a function taking 4 boxed args:
// 0, BytesRef, value : A, 0, and returning `ST.Result Unit`
static inline b_lean_obj_res lean_pod_WriteBytes_writeBytesRef(b_lean_obj_arg writeBytes) {
    return lean_ctor_get(writeBytes, 5);
}

// Returns a function taking 7 boxed args:
// 0, size : USize, BytesRef, i : USize, value : A, 0, 0, and returning `ST.Result Unit`.
static inline b_lean_obj_res lean_pod_WriteBytes_writeBytesRefOffEl(b_lean_obj_arg writeBytes) {
    return lean_ctor_get(writeBytes, 6);
}


// # ReadBytes

/// @returns @& Storable
static inline b_lean_obj_res lean_pod_ReadBytes_storable(b_lean_obj_arg readBytes) {
    return lean_ctor_get(readBytes, 0);
}

// Returns a function taking 3 boxed args:
// 0, BytesRef, 0, and returning `ST.Result A`
static inline b_lean_obj_res lean_pod_ReadBytes_readBytesRef(b_lean_obj_arg readBytes) {
    return lean_ctor_get(readBytes, 5);
}


// Returns a function taking 6 boxed args:
// 0, size : USize, BytesRef, i : USize, 0, 0, and returning `ST.Result A`
static inline b_lean_obj_res lean_pod_ReadBytes_readBytesRefOffEl(b_lean_obj_arg readBytes) {
    return lean_ctor_get(readBytes, 6);
}


// # BytesView

typedef struct {
    lean_object* owner; // NOT NULLABLE
    unsigned char* ptr;
} lean_pod_BytesView;

static void lean_pod_BytesView_finalize(void* bytesView) {
    lean_object* owner = ((lean_pod_BytesView*)bytesView)->owner;
    lean_dec(owner);
    lean_pod_free(bytesView);
}

static void lean_pod_BytesView_foreach(void* bytesView, b_lean_obj_arg f) {
    lean_object* owner = ((lean_pod_BytesView*)bytesView)->owner;
    lean_inc_ref(f);
    lean_inc(owner);
    lean_apply_1(f, owner);
}

static inline lean_obj_res lean_pod_BytesView_wrap (unsigned char* ptr, lean_obj_arg owner) {
    static lean_external_class* class_ = NULL;
    if (class_ == NULL) {
        class_ = lean_register_external_class(lean_pod_BytesView_finalize, lean_pod_BytesView_foreach);
    }
    lean_pod_BytesView* bv = (lean_pod_BytesView*)lean_pod_alloc(sizeof(lean_pod_BytesView));
    bv->owner = owner;
    bv->ptr = ptr;
    return lean_alloc_external(class_, (void*)bv);
}

static inline lean_pod_BytesView* lean_pod_BytesView_unwrap (b_lean_obj_arg obj) {
    return (lean_pod_BytesView*) lean_get_external_data(obj);
}


// # BytesRef

typedef unsigned char* lean_pod_BytesRef;

static inline lean_obj_res lean_pod_BytesRef_wrap(lean_pod_BytesRef ptr) {
    static lean_external_class* class_ = NULL;
    if (class_ == NULL) {
        class_ = lean_register_external_class(lean_pod_default_finalize, lean_pod_default_foreach);
    }
    return lean_alloc_external(class_, (void*)ptr);
}

static inline lean_pod_BytesRef lean_pod_BytesRef_unwrap(b_lean_obj_arg ref) {
    return (lean_pod_BytesRef)lean_get_external_data(ref);
}


// # Buffer

typedef struct {
    unsigned char* data;
    void(*free)(void*);
} lean_pod_Buffer;

static void lean_pod_Buffer_finalize(void* obj) {
    lean_pod_Buffer* buf = (lean_pod_Buffer*)obj;
    buf->free(buf->data);
    lean_pod_free(buf);
}

static inline lean_obj_res lean_pod_Buffer_wrap(unsigned char* data, void (*freeFn)(void*)) {
    static lean_external_class* class_ = NULL;
    if (class_ == NULL) {
        class_ = lean_register_external_class(lean_pod_Buffer_finalize, lean_pod_default_foreach);
    }
    lean_pod_Buffer* buf = (lean_pod_Buffer*)lean_pod_alloc(sizeof(lean_pod_Buffer));
    buf->data = data;
    buf->free = freeFn;
    return lean_alloc_external(class_, (void*)buf);
}

static inline lean_pod_Buffer* lean_pod_Buffer_unwrap(b_lean_obj_arg buf) {
    return (lean_pod_Buffer*)lean_get_external_data(buf);
}


// # UVector

// NULL for vectors of size 0.
typedef unsigned char* lean_pod_UVector;

static inline lean_obj_res lean_pod_UVector_wrap(lean_pod_UVector uv)
{
    static lean_external_class* class_ = NULL;
    if (class_ == NULL) {
        class_ = lean_register_external_class(lean_pod_free, lean_pod_default_foreach);
    }
    return lean_alloc_external(class_, (void*)uv);
}

static inline lean_pod_UVector lean_pod_UVector_unwrap(b_lean_obj_arg buf) {
    return (lean_pod_UVector)lean_get_external_data(buf);
}


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

#define LEAN_POD_RWBYTES_INST(ctyp, ltyp, box)\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefUnal_##ltyp(b_lean_obj_arg a, b_lean_obj_arg br, lean_obj_arg st) {\
    ctyp value;\
    memcpy(&value, lean_pod_BytesRef_unwrap(br), sizeof(ctyp));\
    return lean_io_result_mk_ok(box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOffUnal_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg a, b_lean_obj_arg br, b_lean_obj_arg i_nat, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    ctyp value;\
    memcpy(&value, lean_pod_BytesRef_unwrap(br) + i, sizeof(ctyp));\
    return lean_io_result_mk_ok(box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOffElUnal_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg a, b_lean_obj_arg br, b_lean_obj_arg i_nat, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    ctyp value;\
    memcpy(&value, lean_pod_BytesRef_unwrap(br) + i * sizeof(ctyp), sizeof(ctyp));\
    return lean_io_result_mk_ok(box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRef_##ltyp(b_lean_obj_arg br, lean_obj_arg st) {\
    ctyp value;\
    unsigned char* p = lean_pod_BytesRef_unwrap(br);\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return lean_io_result_mk_ok(box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOff_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg a, b_lean_obj_arg br, b_lean_obj_arg i_nat, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    ctyp value;\
    unsigned char* p = lean_pod_BytesRef_unwrap(br) + i;\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return lean_io_result_mk_ok(box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOffEl_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg br, b_lean_obj_arg i_nat, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    ctyp value;\
    unsigned char* p = lean_pod_BytesRef_unwrap(br) + i * sizeof(ctyp);\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return lean_io_result_mk_ok(box(value));\
}\
\
LEAN_EXPORT ctyp lean_pod_readBytesViewUnal_##ltyp(b_lean_obj_arg a, b_lean_obj_arg bv) {\
    ctyp value;\
    memcpy(&value, lean_pod_BytesView_unwrap(bv)->ptr, sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesViewOffUnal_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg a, b_lean_obj_arg bv, b_lean_obj_arg i_nat) {\
    size_t i = lean_usize_of_nat(i_nat);\
    ctyp value;\
    memcpy(&value, lean_pod_BytesView_unwrap(bv)->ptr + i, sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesViewOffElUnal_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg a, b_lean_obj_arg bv, b_lean_obj_arg i_nat) {\
    size_t i = lean_usize_of_nat(i_nat);\
    ctyp value;\
    memcpy(&value, lean_pod_BytesView_unwrap(bv)->ptr + i * sizeof(ctyp), sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesView_##ltyp(b_lean_obj_arg bv) {\
    ctyp value;\
    unsigned char* p = lean_pod_BytesView_unwrap(bv)->ptr;\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesViewOff_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg a, b_lean_obj_arg bv, b_lean_obj_arg i_nat) {\
    size_t i = lean_usize_of_nat(i_nat);\
    ctyp value;\
    unsigned char* p = lean_pod_BytesView_unwrap(bv)->ptr + i;\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesViewOffEl_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg bv, b_lean_obj_arg i_nat) {\
    size_t i = lean_usize_of_nat(i_nat);\
    ctyp value;\
    unsigned char* p = lean_pod_BytesView_unwrap(bv)->ptr + i * sizeof(ctyp);\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return value;\
}\
\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefUnal_##ltyp(b_lean_obj_arg a, b_lean_obj_arg br, ctyp value, lean_obj_arg st) {\
    memcpy(lean_pod_BytesRef_unwrap(br), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOffUnal_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg a, b_lean_obj_arg br, b_lean_obj_arg i_nat, ctyp value, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    memcpy(lean_pod_BytesRef_unwrap(br) + i, &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOffElUnal_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg a, b_lean_obj_arg br, b_lean_obj_arg i_nat, ctyp value, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    memcpy(lean_pod_BytesRef_unwrap(br) + i * sizeof(ctyp), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRef_##ltyp(b_lean_obj_arg br, ctyp value, lean_obj_arg st) {\
    memcpy(LEAN_POD_ASSUME_ALIGNED(lean_pod_BytesRef_unwrap(br), ctyp), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOff_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg a, b_lean_obj_arg br, b_lean_obj_arg i_nat, ctyp value, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    unsigned char* p = lean_pod_BytesRef_unwrap(br) + i;\
    memcpy(LEAN_POD_ASSUME_ALIGNED(p, ctyp), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOffEl_##ltyp(b_lean_obj_arg sz, b_lean_obj_arg br, b_lean_obj_arg i_nat, ctyp value, lean_obj_arg st) {\
    size_t i = lean_usize_of_nat(i_nat);\
    unsigned char* p = lean_pod_BytesRef_unwrap(br) + i * sizeof(ctyp);\
    memcpy(LEAN_POD_ASSUME_ALIGNED(p, ctyp), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}
