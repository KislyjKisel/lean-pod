#include <stdlib.h>
#include <string.h>
#include "include/lean_pod.h"

LEAN_EXPORT lean_obj_res lean_pod_Buffer_allocate(b_lean_obj_arg sz_nat) {
    size_t sz = lean_usize_of_nat(sz_nat);
    return lean_pod_Buffer_wrap(malloc(sz), free);
}

LEAN_EXPORT lean_obj_res lean_pod_Buffer_allocateClear(b_lean_obj_arg sz_nat) {
    size_t sz = lean_usize_of_nat(sz_nat);
    return lean_pod_Buffer_wrap(calloc(1, sz), free);
}

LEAN_EXPORT lean_obj_res lean_pod_Buffer_view(b_lean_obj_arg sz_nat, b_lean_obj_arg align, lean_obj_arg buf) {
    size_t sz = lean_usize_of_nat(sz_nat);
    return lean_pod_BytesView_wrap(lean_pod_Buffer_unwrap(buf)->data, buf);
}

LEAN_EXPORT lean_obj_res lean_pod_Buffer_withRef(b_lean_obj_arg sz_nat, b_lean_obj_arg align, lean_obj_arg buf, lean_obj_arg f) {
    size_t sz = lean_usize_of_nat(sz_nat);
    lean_object* buf_res;
    if(LEAN_LIKELY(lean_is_exclusive(buf))) {
        buf_res = buf;
    }
    else {
        buf_res = lean_pod_Buffer_wrap(malloc(sz), free);
        memcpy(lean_pod_Buffer_unwrap(buf_res)->data, lean_pod_Buffer_unwrap(buf)->data, sz);
        lean_dec_ref(buf);
    }
    lean_object* fres = lean_apply_3(
        f,
        lean_box(0),
        lean_pod_BytesRef_wrap(lean_pod_Buffer_unwrap(buf_res)->data),
        lean_box(0)
    );
    lean_dec_ref(fres);
    return buf_res;
}
