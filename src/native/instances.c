#include <string.h>
#include "include/lean_pod.h"

#if defined(__GNUC__) || defined(__clang__)
#define LEAN_POD_ASSUME_ALIGNED(p, t) __builtin_assume_aligned(p, _Alignof(t))
#else
#define LEAN_POD_ASSUME_ALIGNED(p, t) p
#endif

static inline lean_obj_res lean_pod_BytesRef_notStError() {
    return lean_io_result_mk_ok(lean_panic_fn(
        lean_box(0),
        lean_mk_string("Error: `BytesRef` used in multithreaded context or while marked persistent")
    ));
}

#define LEAN_POD_RWBYTES_INST(ctyp, ltyp)\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefUnal_##ltyp(b_lean_obj_arg a, b_lean_obj_arg br, lean_obj_arg st) {\
    ctyp value;\
    memcpy(&value, lean_pod_BytesRef_unwrap(br), sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOffUnal_##ltyp(size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, size_t i, lean_obj_arg st) {\
    ctyp value;\
    memcpy(&value, lean_pod_BytesRef_unwrap(br) + i, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOffElUnal_##ltyp(size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, size_t i, lean_obj_arg st) {\
    ctyp value;\
    memcpy(&value, lean_pod_BytesRef_unwrap(br) + i * sizeof(ctyp), sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRef_##ltyp(b_lean_obj_arg br, lean_obj_arg st) {\
    ctyp value;\
    char* p = lean_pod_BytesRef_unwrap(br);\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOff_##ltyp(size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, size_t i, lean_obj_arg st) {\
    ctyp value;\
    char* p = lean_pod_BytesRef_unwrap(br) + i;\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(value));\
}\
LEAN_EXPORT lean_obj_res lean_pod_readBytesRefOffEl_##ltyp(size_t sz, b_lean_obj_arg br, size_t i, lean_obj_arg st) {\
    ctyp value;\
    char* p = lean_pod_BytesRef_unwrap(br) + i * sizeof(ctyp);\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(value));\
}\
\
LEAN_EXPORT ctyp lean_pod_readBytesViewUnal_##ltyp(b_lean_obj_arg a, b_lean_obj_arg bv) {\
    ctyp value;\
    memcpy(&value, lean_pod_BytesView_unwrap(bv)->ptr, sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesViewOffUnal_##ltyp(size_t sz, b_lean_obj_arg a, b_lean_obj_arg bv, size_t i) {\
    ctyp value;\
    memcpy(&value, lean_pod_BytesView_unwrap(bv)->ptr + i, sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesViewOffElUnal_##ltyp(size_t sz, b_lean_obj_arg a, b_lean_obj_arg bv, size_t i) {\
    ctyp value;\
    memcpy(&value, lean_pod_BytesView_unwrap(bv)->ptr + i * sizeof(ctyp), sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesView_##ltyp(b_lean_obj_arg bv) {\
    ctyp value;\
    char* p = lean_pod_BytesView_unwrap(bv)->ptr;\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesViewOff_##ltyp(size_t sz, b_lean_obj_arg a, b_lean_obj_arg bv, size_t i) {\
    ctyp value;\
    char* p = lean_pod_BytesView_unwrap(bv)->ptr + i;\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return value;\
}\
LEAN_EXPORT ctyp lean_pod_readBytesViewOffEl_##ltyp(size_t sz, b_lean_obj_arg bv, size_t i) {\
    ctyp value;\
    char* p = lean_pod_BytesView_unwrap(bv)->ptr + i * sizeof(ctyp);\
    memcpy(&value, LEAN_POD_ASSUME_ALIGNED(p, ctyp), sizeof(ctyp));\
    return value;\
}\
\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefUnal_##ltyp(b_lean_obj_arg a, b_lean_obj_arg br, ctyp value, lean_obj_arg st) {\
    memcpy(lean_pod_BytesRef_unwrap(br), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOffUnal_##ltyp(size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, size_t i, ctyp value, lean_obj_arg st) {\
    memcpy(lean_pod_BytesRef_unwrap(br) + i, &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOffElUnal_##ltyp(size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, size_t i, ctyp value, lean_obj_arg st) {\
    memcpy(lean_pod_BytesRef_unwrap(br) + i * sizeof(ctyp), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRef_##ltyp(b_lean_obj_arg br, ctyp value, lean_obj_arg st) {\
    memcpy(LEAN_POD_ASSUME_ALIGNED(lean_pod_BytesRef_unwrap(br), ctyp), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOff_##ltyp(size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, size_t i, ctyp value, lean_obj_arg st) {\
    char* p = lean_pod_BytesRef_unwrap(br) + i;\
    memcpy(LEAN_POD_ASSUME_ALIGNED(p, ctyp), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}\
LEAN_EXPORT lean_obj_res lean_pod_writeBytesRefOffEl_##ltyp(size_t sz, b_lean_obj_arg br, size_t i, ctyp value, lean_obj_arg st) {\
    char* p = lean_pod_BytesRef_unwrap(br) + i * sizeof(ctyp);\
    memcpy(LEAN_POD_ASSUME_ALIGNED(p, ctyp), &value, sizeof(ctyp));\
    return lean_io_result_mk_ok(lean_box(0));\
}

LEAN_POD_RWBYTES_INST(uint8_t, UInt8)
LEAN_POD_RWBYTES_INST(uint16_t, UInt16)
LEAN_POD_RWBYTES_INST(uint32_t, UInt32)
LEAN_POD_RWBYTES_INST(uint64_t, UInt64)
LEAN_POD_RWBYTES_INST(size_t, USize)
LEAN_POD_RWBYTES_INST(double, Float)
LEAN_POD_RWBYTES_INST(uint32_t, Float32)
