#include <string.h>
#include "include/lean_pod.h"
#include "util.h"

LEAN_EXPORT lean_obj_res lean_pod_ByteArray_ref(lean_obj_arg ba, lean_obj_arg token) {
    lean_object* resba;
    if(LEAN_LIKELY(lean_is_exclusive(ba))) {
        resba = ba;
    }
    else {
        resba = lean_copy_byte_array(ba);
        lean_dec_ref(ba);
    }
    return lean_io_result_mk_ok(lean_pod_BytesView_wrap(lean_sarray_cptr(resba), resba));
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_weaken(uint8_t mut, size_t sz, b_lean_obj_arg a0, b_lean_obj_arg a1, lean_obj_arg bv) {
    return bv;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_imm(uint8_t mut, size_t sz, b_lean_obj_arg a, lean_obj_arg br) {
    return br;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_take(uint8_t mut, size_t size, b_lean_obj_arg a, lean_obj_arg bv, size_t count) {
    return bv;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_drop(uint8_t mut, size_t size, b_lean_obj_arg a, lean_obj_arg bv_w, size_t count) {
    lean_pod_BytesView* bv = lean_pod_BytesView_unwrap(bv_w);
    if(lean_is_exclusive(bv_w)) {
        bv->ptr += count;
        return bv_w;
    }
    return lean_pod_BytesView_wrap(bv->ptr + count, bv->owner);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_slice(uint8_t mut, size_t sz, b_lean_obj_arg a, lean_obj_arg bv_w, size_t start, size_t length) {
    return lean_pod_BytesRef_drop(mut, sz, a, bv_w, start);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_toByteArray(uint8_t mut, size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, lean_obj_arg token) {
    lean_object* arr = lean_alloc_sarray(1, sz, sz);
    memcpy(lean_sarray_cptr(arr), lean_pod_BytesView_unwrap(br)->ptr, sz);
    return lean_io_result_mk_ok(arr);
}

static inline lean_obj_res lean_pod_BytesRef_notStError() {
    return lean_io_result_mk_ok(lean_panic_fn(
        lean_box(0),
        lean_mk_string("Error: `BytesRef` used in multithreaded context or while marked persistent")
    ));
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_getUInt8(uint8_t mut, size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, size_t i, lean_obj_arg token) {
    if (LEAN_LIKELY(lean_is_st(br))) {
        return lean_io_result_mk_ok(lean_pod_BytesView_unwrap(br)->ptr[i]);
    }
    return lean_pod_BytesRef_notStError();
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_setUInt8(size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, size_t i, uint8_t value, lean_obj_arg token) {
    if (LEAN_LIKELY(lean_is_st(br))) {
        lean_pod_BytesView_unwrap(br)->ptr[i] = value;
        return lean_io_result_mk_ok(lean_box(0));
    }
    return lean_pod_BytesRef_notStError();
}

#define LEAN_POD_BYTESREF_GET_SET(bw, box)\
LEAN_EXPORT lean_obj_res lean_pod_BytesRef_getUInt##bw##Ne(uint8_t mut, size_t sz, b_lean_obj_arg br, size_t i, lean_obj_arg token) {\
    if (LEAN_LIKELY(lean_is_st(br))) {\
        uint##bw##_t u;\
        memcpy(&u, lean_pod_BytesView_unwrap(br)->ptr + i, sizeof(uint##bw##_t));\
        return lean_io_result_mk_ok(box(u));\
    }\
    return lean_pod_BytesRef_notStError();\
}\
LEAN_EXPORT lean_obj_res LEAN_POD_CONCAT3(lean_pod_BytesRef_getUInt, bw, LEAN_POD_BYTESREF_E_KEEP)(uint8_t mut, size_t sz, b_lean_obj_arg br, size_t i, lean_obj_arg token) {\
    return lean_pod_BytesRef_getUInt##bw##Ne(mut, sz, br, i, token);\
}\
LEAN_EXPORT lean_obj_res LEAN_POD_CONCAT3(lean_pod_BytesRef_getUInt, bw, LEAN_POD_BYTESREF_E_SWAP)(uint8_t mut, size_t sz, b_lean_obj_arg br, size_t i, lean_obj_arg token) {\
    if (LEAN_LIKELY(lean_is_st(br))) {\
        uint##bw##_t u;\
        memcpy(&u, lean_pod_BytesView_unwrap(br)->ptr + i, sizeof(uint##bw##_t));\
        return lean_io_result_mk_ok(box(lean_pod_bswap##bw(u)));\
    }\
    return lean_pod_BytesRef_notStError();\
}\
LEAN_EXPORT lean_obj_res lean_pod_BytesRef_setUInt##bw##Ne(size_t sz, b_lean_obj_arg br, size_t i, uint##bw##_t value, lean_obj_arg token) {\
    if (LEAN_LIKELY(lean_is_st(br))) {\
        memcpy(lean_pod_BytesView_unwrap(br)->ptr + i, &value, sizeof(uint##bw##_t));\
        return lean_io_result_mk_ok(lean_box(0));\
    }\
    return lean_pod_BytesRef_notStError();\
}\
LEAN_EXPORT lean_obj_res LEAN_POD_CONCAT3(lean_pod_BytesRef_setUInt, bw, LEAN_POD_BYTESREF_E_KEEP)(size_t sz, b_lean_obj_arg br, size_t i, uint##bw##_t value, lean_obj_arg token) {\
    return lean_pod_BytesRef_setUInt##bw##Ne(sz, br, i, value, token);\
}\
LEAN_EXPORT lean_obj_res LEAN_POD_CONCAT3(lean_pod_BytesRef_setUInt, bw, LEAN_POD_BYTESREF_E_SWAP)(size_t sz, b_lean_obj_arg br, size_t i, uint##bw##_t value, lean_obj_arg token) {\
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