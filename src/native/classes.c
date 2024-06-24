#include "include/lean_pod.h"

LEAN_POD_DEFINE_EXTERNAL_CLASS(pod_Ptr)
LEAN_POD_DEFINE_EXTERNAL_CLASS(pod_Buffer)

static void lean_pod_Buffer_finalize(void* obj) {
    lean_pod_Buffer_data* buf = (lean_pod_Buffer_data*)obj;
    buf->free(buf->data);
    lean_pod_free(buf);
}

LEAN_EXPORT lean_obj_res lean_pod_initialize_types(lean_obj_arg io_) {
    LEAN_POD_INITIALIZE_EXTERNAL_CLASS(pod_Ptr, lean_pod_default_finalize, lean_pod_default_foreach)
    LEAN_POD_INITIALIZE_EXTERNAL_CLASS(pod_Buffer, lean_pod_Buffer_finalize, lean_pod_default_foreach)
    return lean_io_result_mk_ok(lean_box(0));
}
