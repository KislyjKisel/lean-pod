#include <string.h>
#include "include/lean_pod.h"

LEAN_EXPORT lean_obj_res lean_pod_ByteArray_withRef(lean_obj_arg ba, lean_obj_arg f) {
    lean_object* resba;
    if(LEAN_LIKELY(lean_is_exclusive(ba))) {
        resba = ba;
    }
    else {
        resba = lean_copy_byte_array(ba);
    }
    lean_object* fres = lean_apply_3(f, lean_box(0), lean_pod_BytesRef_box(lean_sarray_cptr(resba)), lean_box(0));
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
    }
    lean_object* fres = lean_apply_3(f, lean_box(0), lean_pod_BytesRef_box(lean_sarray_cptr(resba)), lean_box(0));
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

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_weaken(uint8_t mut, size_t sz, b_lean_obj_arg a0, b_lean_obj_arg a1, size_t br) {
    return br;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_imm(uint8_t mut, size_t sz, b_lean_obj_arg a, size_t br) {
    return br;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_take(uint8_t mut, size_t size, b_lean_obj_arg a, size_t br, size_t count) {
    return br;
}

LEAN_EXPORT size_t lean_pod_BytesRef_drop(uint8_t mut, size_t size, b_lean_obj_arg a, size_t br, size_t count) {
    return br + count;
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_slice(uint8_t mut, size_t sz, b_lean_obj_arg a, size_t br, size_t start, size_t length) {
    return lean_pod_BytesRef_drop(mut, sz, a, br, start);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_toByteArray(uint8_t mut, size_t sz, b_lean_obj_arg a, size_t br, lean_obj_arg token) {
    lean_object* arr = lean_alloc_sarray(1, sz, sz);
    memcpy(lean_sarray_cptr(arr), br, sz);
    return lean_io_result_mk_ok(arr);
}
