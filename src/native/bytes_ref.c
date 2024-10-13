#include <string.h>
#include "include/lean_pod.h"

static lean_obj_res lean_pod_ByteArray_withRefM_aux(lean_obj_arg resba, lean_obj_arg x) {
    return lean_mk_tuple2(x, resba);
}

LEAN_EXPORT lean_obj_res lean_pod_ByteArray_withRef(b_lean_obj_arg functor, lean_obj_arg ba, lean_obj_arg f) {
    lean_object* resba;
    if(LEAN_LIKELY(lean_is_exclusive(ba))) {
        resba = ba;
    }
    else {
        resba = lean_copy_byte_array(ba);
        lean_dec_ref(ba);
    }
    lean_object* fres = lean_apply_2(
        f,
        lean_box(0),
        lean_pod_BytesRef_box(lean_sarray_cptr(resba))
    );
    lean_object* fmap = lean_ctor_get(functor, 0);
    lean_inc_ref(fmap);
    lean_object* concat_res = lean_alloc_closure(lean_pod_ByteArray_withRefM_aux, 2, 1);
    lean_closure_arg_cptr(concat_res)[0] = resba;
    return lean_apply_4(fmap, lean_box(0), lean_box(0), concat_res, fres);
}

LEAN_EXPORT lean_obj_res lean_pod_ByteArray_withRefImm(b_lean_obj_arg ba, lean_obj_arg f) {
    return lean_apply_2(
        f,
        lean_box(0),
        lean_pod_BytesRef_box(lean_sarray_cptr(ba))
    );
}

LEAN_EXPORT lean_obj_res lean_pod_BytesView_asRef(
    b_lean_obj_arg sz, b_lean_obj_arg align, lean_pod_BytesView bv, lean_obj_arg f
) {
    return lean_apply_2(
        f,
        lean_box(0),
        lean_pod_BytesRef_box(lean_pod_BytesView_fromRepr(bv)->ptr)
    );
}

LEAN_EXPORT lean_pod_BytesRef lean_pod_BytesRef_weaken(
    uint8_t mut, b_lean_obj_arg sz, b_lean_obj_arg a0, b_lean_obj_arg a1,
    lean_pod_BytesRef br
) {
    return br;
}

LEAN_EXPORT lean_pod_BytesRef lean_pod_BytesRef_imm(
    uint8_t mut, b_lean_obj_arg sz, b_lean_obj_arg a,
    lean_pod_BytesRef br
) {
    return br;
}

LEAN_EXPORT lean_pod_BytesRef lean_pod_BytesRef_take(
    uint8_t mut, b_lean_obj_arg sz, b_lean_obj_arg a,
    lean_pod_BytesRef br, b_lean_obj_arg count
) {
    return br;
}

LEAN_EXPORT lean_pod_BytesRef lean_pod_BytesRef_drop(
    uint8_t mut, b_lean_obj_arg sz, b_lean_obj_arg a,
    lean_pod_BytesRef br, b_lean_obj_arg count_nat
) {
    size_t count = lean_usize_of_nat(count_nat);
    if(lean_is_exclusive(br)) {
        lean_to_external(br)->m_data += count;
        return br;
    }
    lean_dec_ref(br);
    return lean_pod_BytesRef_toRepr(lean_to_external(br)->m_data + count);
}

LEAN_EXPORT lean_pod_BytesRef lean_pod_BytesRef_slice(
    uint8_t mut, b_lean_obj_arg sz, b_lean_obj_arg a,
    lean_pod_BytesRef br, b_lean_obj_arg start, b_lean_obj_arg length
) {
    return lean_pod_BytesRef_drop(mut, sz, a, br, start);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_toByteArray(
    uint8_t mut, b_lean_obj_arg sz_nat, b_lean_obj_arg a,
    lean_pod_BytesRef br, lean_obj_arg token
) {
    size_t sz = lean_usize_of_nat(sz_nat);
    lean_object* arr = lean_alloc_sarray(1, sz, sz);
    memcpy(lean_sarray_cptr(arr), lean_pod_BytesRef_fromRepr(br), sz);
    return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res lean_pod_BytesRef_copy(
    uint8_t mut, b_lean_obj_arg sz_nat, b_lean_obj_arg a1, b_lean_obj_arg a2,
    lean_pod_BytesRef dst, lean_pod_BytesRef src, lean_obj_arg token
) {
    size_t sz = lean_usize_of_nat(sz_nat);
    memcpy(lean_pod_BytesRef_fromRepr(dst), lean_pod_BytesRef_fromRepr(src), sz);
    return lean_io_result_mk_ok(lean_box(0));
}
