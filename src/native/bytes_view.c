#include <string.h>
#include "include/lean_pod.h"

LEAN_EXPORT lean_obj_res lean_pod_ByteArray_view(lean_obj_arg ba) {
    return lean_pod_BytesView_wrap(lean_sarray_cptr(ba), ba);
}

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
    lean_dec_ref(bv_w);
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
