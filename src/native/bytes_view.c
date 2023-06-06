#include <string.h>
#include "include/lean_pod.h"

LEAN_EXPORT lean_obj_res lean_pod_ByteArray_view(lean_obj_arg ba) {
    return lean_pod_BytesView_wrap(lean_sarray_cptr(ba), ba);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_weaken(
    b_lean_obj_arg sz, b_lean_obj_arg a0, b_lean_obj_arg a1,
    lean_obj_arg bv
) {
    return bv;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_take(
    b_lean_obj_arg sz, b_lean_obj_arg a,
    lean_obj_arg bv, b_lean_obj_arg count
) {
    return bv;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_drop(
    b_lean_obj_arg sz, b_lean_obj_arg a,
    lean_obj_arg bv_w, b_lean_obj_arg count_nat
) {
    size_t count = lean_usize_of_nat(count_nat);
    lean_pod_BytesView* bv = lean_pod_BytesView_unwrap(bv_w);
    if(lean_is_exclusive(bv_w)) {
        bv->ptr += count;
        return bv_w;
    }
    lean_dec_ref(bv_w);
    return lean_pod_BytesView_wrap(bv->ptr + count, bv->owner);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_slice(
    b_lean_obj_arg sz, b_lean_obj_arg a,
    lean_obj_arg bv_w, b_lean_obj_arg start, b_lean_obj_arg length
) {
    return lean_pod_BytesView_drop(sz, a, bv_w, start);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_toByteArray(
    b_lean_obj_arg sz_nat, b_lean_obj_arg a,
    b_lean_obj_arg bv
) {
    size_t sz = lean_usize_of_nat(sz_nat);
    lean_object* arr = lean_alloc_sarray(1, sz, sz);
    memcpy(lean_sarray_cptr(arr), lean_pod_BytesView_unwrap(bv)->ptr, sz);
    return arr;
}
