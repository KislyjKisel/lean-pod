#include <string.h>
#include "include/lean_pod.h"
#include "util.h"

LEAN_EXPORT lean_obj_res lean_pod_BytesView_weaken(size_t sz, b_lean_obj_arg a0, b_lean_obj_arg a1, lean_obj_arg bv) {
    return bv;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_take(size_t size, b_lean_obj_arg a, lean_obj_arg bv, size_t count) {
    return bv;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_drop(size_t size, b_lean_obj_arg a, lean_obj_arg bv_w, size_t count) {
    lean_pod_BytesView* bv = lean_pod_BytesView_unwrap(bv_w);
    if(lean_is_exclusive(bv_w)) {
        bv->ptr += count;
        return bv_w;
    }
    return lean_pod_BytesView_wrap(bv->ptr + count, bv->owner);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_slice(size_t sz, b_lean_obj_arg a, lean_obj_arg bv_w, size_t start, size_t length) {
    return lean_pod_BytesView_drop(sz, a, bv_w, start);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_toByteArray(size_t sz, b_lean_obj_arg a, b_lean_obj_arg br) {
    lean_object* arr = lean_alloc_sarray(1, sz, sz);
    memcpy(lean_sarray_cptr(arr), lean_pod_BytesView_unwrap(br)->ptr, sz);
    return arr;
}

LEAN_EXPORT uint8_t lean_pod_BytesView_getUInt8(size_t sz, b_lean_obj_arg a, lean_obj_arg bv_w, size_t i) {
    return lean_pod_BytesView_unwrap(bv_w)->ptr[i];
}

#define LEAN_POD_BYTESVIEW_GET(bw)\
LEAN_EXPORT uint##bw##_t lean_pod_BytesView_getUInt##bw##Ne(size_t sz, b_lean_obj_arg bv_w, size_t i) {\
    uint##bw##_t u;\
    memcpy(&u, lean_pod_BytesView_unwrap(bv_w)->ptr + i, sizeof(uint##bw##_t));\
    return u;\
}\
LEAN_EXPORT uint##bw##_t LEAN_POD_CONCAT3(lean_pod_BytesView_getUInt,bw,LEAN_POD_BYTESREF_E_KEEP)(size_t sz, b_lean_obj_arg bv_w, size_t i) {\
    return lean_pod_BytesView_getUInt##bw##Ne(sz, bv_w, i);\
}\
LEAN_EXPORT uint##bw##_t LEAN_POD_CONCAT3(lean_pod_BytesView_getUInt,bw,LEAN_POD_BYTESREF_E_SWAP)(size_t sz, b_lean_obj_arg bv_w, size_t i) {\
    return lean_pod_bswap##bw(lean_pod_BytesView_getUInt##bw##Ne(sz, bv_w, i));\
}

LEAN_POD_BYTESVIEW_GET(16);
LEAN_POD_BYTESVIEW_GET(32);
LEAN_POD_BYTESVIEW_GET(64);

LEAN_EXPORT size_t lean_pod_BytesView_getUSizeNe(size_t sz, b_lean_obj_arg bv, size_t i) {
    size_t u;
    memcpy(&u, lean_pod_BytesView_unwrap(bv)->ptr + i, sizeof(size_t));
    return u;
}
