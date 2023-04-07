#include "include/lean_pod.h"

LEAN_EXPORT lean_obj_res lean_pod_BytesView_take(lean_obj_arg bv, size_t count) {
    return bv;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_drop(lean_obj_arg bv_w, size_t count) {
    lean_pod_BytesView* bv = lean_pod_BytesView_unwrap(bv_w);
    if(lean_is_exclusive(bv_w)) {
        bv->ptr += count;
        return bv_w;
    }
    lean_pod_BytesView* bv_mod = malloc(sizeof(lean_pod_BytesView));
    bv_mod->owner = bv->owner;
    bv_mod->ptr = bv->ptr + count;
    return lean_pod_BytesView_wrap(bv_mod);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_slice(lean_obj_arg bv_w, size_t start, size_t length) {
    return lean_pod_BytesView_drop(bv_w, start);
}

LEAN_EXPORT uint8_t lean_pod_BytesView_getUInt8(lean_obj_arg bv_w, size_t i) {
    return lean_pod_BytesView_unwrap(bv_w)->ptr[i];
}

#define LEAN_POD_BYTESVIEW_GET_NE(bw)\
LEAN_EXPORT uint##bw##_t lean_pod_BytesView_getUInt##bw##Ne(lean_obj_arg bv_w, size_t i) {\
    return *((uint##bw##_t*)lean_pod_BytesView_unwrap(bv_w)->ptr + i);\
}

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define LEAN_POD_BYTESVIEW_GET(bw)\
LEAN_POD_BYTESVIEW_GET_NE(bw)\
LEAN_EXPORT uint##bw##_t lean_pod_BytesView_getUInt##bw##Le(lean_obj_arg bv_w, size_t i) {\
    return lean_pod_BytesView_getUInt##bw##Ne(bv_w, i);\
}\
LEAN_EXPORT uint##bw##_t lean_pod_BytesView_getUInt##bw##Be(lean_obj_arg bv_w, size_t i) {\
    return lean_pod_bswap##bw(lean_pod_BytesView_getUInt##bw##Ne(bv_w, i));\
}
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define LEAN_POD_BYTESVIEW_GET(bw)\
LEAN_POD_BYTESVIEW_GET_NE(bw)\
LEAN_EXPORT uint##bw##_t lean_pod_BytesView_getUInt##bw##Le(lean_obj_arg bv_w, size_t i) {\
    return lean_pod_bswap##bw(lean_pod_BytesView_getUInt##bw##Ne(bv_w, i));\
}
LEAN_EXPORT uint##bw##_t lean_pod_BytesView_getUInt##bw##Be(lean_obj_arg bv_w, size_t i) {\
    return lean_pod_BytesView_getUInt##bw##Ne(bv_w, i);\
}
#else
unsupported
#endif

LEAN_POD_BYTESVIEW_GET(16);
LEAN_POD_BYTESVIEW_GET(32);
LEAN_POD_BYTESVIEW_GET(64);
