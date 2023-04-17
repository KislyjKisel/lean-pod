#include <string.h>
#include "include/lean_pod.h"
#include "util.h"

LEAN_EXPORT lean_obj_res lean_pod_BytesView_id(lean_obj_arg bv, size_t count) {
    return bv;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_drop(lean_obj_arg bv_w, size_t count) {
    lean_pod_BytesView* bv = lean_pod_BytesView_unwrap(bv_w);
    if(lean_is_exclusive(bv_w)) {
        bv->ptr += count;
        return bv_w;
    }
    return lean_pod_BytesView_wrap(bv->ptr + count, bv->owner);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_slice(lean_obj_arg bv_w, size_t start, size_t length) {
    return lean_pod_BytesView_drop(bv_w, start);
}

LEAN_EXPORT uint8_t lean_pod_BytesView_getUInt8(lean_obj_arg bv_w, size_t i) {
    return lean_pod_BytesView_unwrap(bv_w)->ptr[i];
}

#define LEAN_POD_BYTESVIEW_GET(bw)\
LEAN_EXPORT uint##bw##_t lean_pod_BytesView_getUInt##bw##Ne(b_lean_obj_arg bv_w, size_t i) {\
    uint##bw##_t u;\
    memcpy(&u, lean_pod_BytesView_unwrap(bv_w)->ptr + i, sizeof(uint##bw##_t));\
    return u;\
}\
LEAN_EXPORT uint##bw##_t LEAN_POD_CONCAT3(lean_pod_BytesView_getUInt,bw,LEAN_POD_BYTESREF_E_KEEP)(b_lean_obj_arg bv_w, size_t i) {\
    return lean_pod_BytesView_getUInt##bw##Ne(bv_w, i);\
}\
LEAN_EXPORT uint##bw##_t LEAN_POD_CONCAT3(lean_pod_BytesView_getUInt,bw,LEAN_POD_BYTESREF_E_SWAP)(b_lean_obj_arg bv_w, size_t i) {\
    return lean_pod_bswap##bw(lean_pod_BytesView_getUInt##bw##Ne(bv_w, i));\
}

LEAN_POD_BYTESVIEW_GET(16);
LEAN_POD_BYTESVIEW_GET(32);
LEAN_POD_BYTESVIEW_GET(64);
