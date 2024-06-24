#include "include/lean_pod.h"

LEAN_POD_DEFINE_EXTERNAL_CLASS(pod_Ptr)

LEAN_EXPORT lean_obj_res lean_pod_initialize_types(lean_obj_arg io_) {
    LEAN_POD_INITIALIZE_EXTERNAL_CLASS(pod_Ptr, lean_pod_default_finalize, lean_pod_default_foreach)
    return lean_io_result_mk_ok(lean_box(0));
}
