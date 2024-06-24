#include "include/lean_pod.h"

LEAN_POD_DEFINE_EXTERNAL_CLASS(pod_Ptr)
LEAN_POD_DEFINE_EXTERNAL_CLASS(pod_BytesView)
LEAN_POD_DEFINE_EXTERNAL_CLASS(pod_Buffer)
LEAN_POD_DEFINE_EXTERNAL_CLASS(pod_UVector)

static void lean_pod_BytesView_finalize(void* bytesView) {
    lean_object* owner = ((lean_pod_BytesView_data*)bytesView)->owner;
    lean_dec(owner);
    lean_pod_free(bytesView);
}

static void lean_pod_BytesView_foreach(void* bytesView, b_lean_obj_arg f) {
    lean_object* owner = ((lean_pod_BytesView_data*)bytesView)->owner;
    lean_inc_ref(f);
    lean_inc(owner);
    lean_apply_1(f, owner);
}

static void lean_pod_Buffer_finalize(void* obj) {
    lean_pod_Buffer_data* buf = (lean_pod_Buffer_data*)obj;
    buf->free(buf->data);
    lean_pod_free(buf);
}

LEAN_EXPORT lean_obj_res lean_pod_initialize_types(lean_obj_arg io_) {
    LEAN_POD_INITIALIZE_EXTERNAL_CLASS(pod_Ptr, lean_pod_default_finalize, lean_pod_default_foreach)
    LEAN_POD_INITIALIZE_EXTERNAL_CLASS(pod_BytesView, lean_pod_BytesView_finalize, lean_pod_BytesView_foreach)
    LEAN_POD_INITIALIZE_EXTERNAL_CLASS(pod_Buffer, lean_pod_Buffer_finalize, lean_pod_default_foreach)
    LEAN_POD_INITIALIZE_EXTERNAL_CLASS(pod_UVector, lean_pod_free, lean_pod_default_foreach)
    return lean_io_result_mk_ok(lean_box(0));
}
