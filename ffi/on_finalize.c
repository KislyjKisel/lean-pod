#include <lean/lean.h>
#include "include/lean_pod.h"

LEAN_EXPORT lean_obj_res lean_pod_touch(b_lean_obj_arg val, lean_obj_arg res) {
    return res;
}

LEAN_EXPORT lean_pod_OnFinalize lean_pod_onFinalize(lean_obj_arg callback) {
    return lean_alloc_external(lean_pod_OnFinalize_class, callback);
}

LEAN_EXPORT lean_obj_res lean_pod_OnFinalize_get(lean_pod_OnFinalize onFinalize, lean_obj_arg io_) {
    lean_object* callback = lean_pod_OnFinalize_fromRepr(onFinalize);
    lean_inc_ref(callback);
    return lean_apply_1(callback, lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_pod_onFinalizeMut(lean_obj_arg callback, lean_obj_arg io_) {
    return lean_io_result_mk_ok(lean_alloc_external(lean_pod_OnFinalizeMut_class, callback));
}

LEAN_EXPORT lean_obj_res lean_pod_OnFinalizeMut_get(lean_pod_OnFinalizeMut onFinalize, lean_obj_arg io_) {
    lean_object* callback = lean_pod_OnFinalize_fromRepr(onFinalize);
    if (callback == NULL) {
        return lean_io_result_mk_ok(lean_mk_option_none());
    }
    lean_inc_ref(callback);
    return lean_io_result_mk_ok(lean_mk_option_some(callback));
}

LEAN_EXPORT lean_obj_res lean_pod_OnFinalizeMut_set(lean_pod_OnFinalizeMut onFinalize, lean_obj_arg newCallback, lean_obj_arg io_) {
    lean_object* callback = lean_pod_OnFinalize_fromRepr(onFinalize);
    if (callback != NULL) {
        lean_dec_ref(callback);
    }
    lean_to_external(onFinalize)->m_data = newCallback;
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_pod_OnFinalizeMut_suppress(lean_pod_OnFinalizeMut onFinalize, lean_obj_arg io_) {
    lean_object* callback = lean_pod_OnFinalize_fromRepr(onFinalize);
    if (callback != NULL) {
        lean_dec_ref(callback);
    }
    lean_to_external(onFinalize)->m_data = NULL;
    return lean_io_result_mk_ok(lean_box(0));
}
