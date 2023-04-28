#include <string.h>
#include "include/lean_pod.h"

LEAN_EXPORT lean_obj_res lean_pod_ByteArray_withRef(lean_obj_arg ba, lean_obj_arg f) {
    lean_object* resba;
    if(LEAN_LIKELY(lean_is_exclusive(ba))) {
        resba = ba;
    }
    else {
        resba = lean_copy_byte_array(ba);
        lean_dec_ref(ba);
    }
    lean_object* fres = lean_apply_2(f, lean_pod_BytesRef_wrap(lean_sarray_cptr(resba)), lean_box(0));
    lean_dec_ref(fres);
    return resba;
}

LEAN_EXPORT lean_obj_res lean_pod_ByteArray_withRefEx(lean_obj_arg ba, lean_obj_arg f) {
    lean_object* resba;
    if(LEAN_LIKELY(lean_is_exclusive(ba))) {
        resba = ba;
    }
    else {
        resba = lean_copy_byte_array(ba);
        lean_dec_ref(ba);
    }
    lean_object* fres = lean_apply_2(f, lean_pod_BytesRef_wrap(lean_sarray_cptr(resba)), lean_box(0));
    if(lean_ptr_tag(fres) == 1) {
        lean_dec_ref(resba);
        lean_object* exerr = lean_alloc_ctor(0, 1, 0);
        lean_object* err = lean_ctor_get(fres, 0);
        lean_inc(err);
        lean_ctor_set(exerr, 0, err);
        lean_dec_ref(fres);
        return exerr;
    }
    lean_dec_ref(fres);
    lean_object* exok = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(exok, 0, resba);
    return exok;
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
    lean_pod_BytesRef br = lean_pod_BytesRef_unwrap(bv_w);
    if(lean_is_exclusive(bv_w)) {
        lean_to_external(bv_w)->m_data = br + count;
        return bv_w;
    }
    lean_dec_ref(bv_w);
    return lean_pod_BytesRef_wrap(br + count);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_slice(uint8_t mut, size_t sz, b_lean_obj_arg a, lean_obj_arg bv_w, size_t start, size_t length) {
    return lean_pod_BytesRef_drop(mut, sz, a, bv_w, start);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_toByteArray(uint8_t mut, size_t sz, b_lean_obj_arg a, b_lean_obj_arg br, lean_obj_arg token) {
    lean_object* arr = lean_alloc_sarray(1, sz, sz);
    memcpy(lean_sarray_cptr(arr), lean_pod_BytesRef_unwrap(br), sz);
    return lean_io_result_mk_ok(arr);
}
