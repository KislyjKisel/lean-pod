#include <lean/lean.h>

LEAN_EXPORT lean_obj_res lean_pod_UInt64_getAlignment(b_lean_obj_arg unit) {
    return lean_usize_to_nat(_Alignof(uint64_t));
}

LEAN_EXPORT lean_obj_res lean_pod_Float_getAlignment(b_lean_obj_arg unit) {
    return lean_usize_to_nat(_Alignof(double));
}
