#pragma once

#include <stdint.h>
#include <lean/lean.h>

static void lean_pod_default_foreach(void* a, b_lean_obj_arg b) {}

typedef struct {
    lean_object* owner;
    uint8_t* ptr;
} lean_pod_BytesView;

static inline lean_object* lean_pod_BytesView_wrap (lean_pod_BytesView const* obj) {
    static lean_external_class* class_ = NULL;
    if (class_ == NULL) {
        class_ = lean_register_external_class(free, lean_pod_default_foreach);
    }
    return lean_alloc_external(class_, (void*)obj);
}

static inline lean_pod_BytesView* lean_pod_BytesView_unwrap (b_lean_obj_arg obj) {
    return (lean_pod_BytesView*) lean_get_external_data(obj);
}

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
