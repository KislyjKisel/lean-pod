#include <string.h>
#include "include/lean_pod.h"
#include "util.h"

static inline lean_obj_res lean_pod_BytesRef_notStError() {
    return lean_io_result_mk_ok(lean_panic_fn(
        lean_box(0),
        lean_mk_string("Error: `BytesRef` used in multithreaded context or while marked persistent")
    ));
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_getUInt8(b_lean_obj_arg br, size_t i) {
    if (LEAN_LIKELY(lean_is_st(br))) {
        return lean_io_result_mk_ok(lean_pod_BytesView_unwrap(br)->ptr[i]);
    }
    return lean_pod_BytesRef_notStError();
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_getUInt16(b_lean_obj_arg br, size_t i) {
    if (LEAN_LIKELY(lean_is_st(br))) {
        return lean_io_result_mk_ok(lean_pod_BytesView_unwrap(br)->ptr[i]);
    }
    return lean_pod_BytesRef_notStError();
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_setUInt8(b_lean_obj_arg br, size_t i, uint8_t value) {
    if (LEAN_LIKELY(lean_is_st(br))) {
        lean_pod_BytesView_unwrap(br)->ptr[i] = value;
        return lean_io_result_mk_ok(lean_box(0));
    }
    return lean_pod_BytesRef_notStError();
}

#define LEAN_POD_BYTESREF_GET_SET(bw, box)\
LEAN_EXPORT lean_obj_res lean_pod_BytesRef_getUInt##bw##Ne(b_lean_obj_arg br, size_t i) {\
    if (LEAN_LIKELY(lean_is_st(br))) {\
        uint##bw##_t u;\
        memcpy(&u, lean_pod_BytesView_unwrap(br)->ptr + i, sizeof(uint##bw##_t));\
        return lean_io_result_mk_ok(box(u));\
    }\
    return lean_pod_BytesRef_notStError();\
}\
LEAN_EXPORT lean_obj_res LEAN_POD_CONCAT3(lean_pod_BytesRef_getUInt, bw, LEAN_POD_BYTESREF_E_KEEP)(b_lean_obj_arg br, size_t i) {\
    return lean_pod_BytesRef_getUInt##bw##Ne(br, i);\
}\
LEAN_EXPORT lean_obj_res LEAN_POD_CONCAT3(lean_pod_BytesRef_getUInt, bw, LEAN_POD_BYTESREF_E_SWAP)(b_lean_obj_arg br, size_t i) {\
    if (LEAN_LIKELY(lean_is_st(br))) {\
        uint##bw##_t u;\
        memcpy(&u, lean_pod_BytesView_unwrap(br)->ptr + i, sizeof(uint##bw##_t));\
        return lean_io_result_mk_ok(box(lean_pod_bswap##bw(u)));\
    }\
    return lean_pod_BytesRef_notStError();\
}\
LEAN_EXPORT lean_obj_res lean_pod_BytesRef_setUInt##bw##Ne(b_lean_obj_arg br, size_t i, uint##bw##_t value) {\
    if (LEAN_LIKELY(lean_is_st(br))) {\
        memcpy(lean_pod_BytesView_unwrap(br)->ptr + i, &value, sizeof(uint##bw##_t));\
        return lean_io_result_mk_ok(lean_box(0));\
    }\
    return lean_pod_BytesRef_notStError();\
}\
LEAN_EXPORT lean_obj_res LEAN_POD_CONCAT3(lean_pod_BytesRef_setUInt, bw, LEAN_POD_BYTESREF_E_KEEP)(b_lean_obj_arg br, size_t i, uint##bw##_t value) {\
    return lean_pod_BytesRef_setUInt##bw##Ne(br, i, value);\
}\
LEAN_EXPORT lean_obj_res LEAN_POD_CONCAT3(lean_pod_BytesRef_setUInt, bw, LEAN_POD_BYTESREF_E_SWAP)(b_lean_obj_arg br, size_t i, uint##bw##_t value) {\
    if (LEAN_LIKELY(lean_is_st(br))) {\
        uint##bw##_t value_bs = lean_pod_bswap##bw(value);\
        memcpy(lean_pod_BytesView_unwrap(br)->ptr + i, &value_bs, sizeof(uint##bw##_t));\
        return lean_io_result_mk_ok(lean_box(0));\
    }\
    return lean_pod_BytesRef_notStError();\
}

LEAN_POD_BYTESREF_GET_SET(16, lean_box);
LEAN_POD_BYTESREF_GET_SET(32, lean_box_uint32);
LEAN_POD_BYTESREF_GET_SET(64, lean_box_uint64);
