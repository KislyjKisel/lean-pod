#include <string.h>
#include "include/lean_pod.h"

static inline lean_obj_res lean_pod_UVector_clone(size_t sizeBytes, b_lean_obj_arg uv_box) {
    lean_pod_byte_ptr uv = lean_pod_UVector_fromRepr(uv_box);
    lean_pod_byte_ptr uv_cloned = lean_pod_alloc(sizeBytes);
    memcpy(
        uv_cloned,
        uv,
        sizeBytes
    );
    return lean_pod_UVector_toRepr(uv_cloned);
}

LEAN_EXPORT lean_obj_res lean_pod_UVector_zero(b_lean_obj_arg n, b_lean_obj_arg sb) {
    size_t count = lean_usize_of_nat(n);
    if (LEAN_UNLIKELY(count == 0)) {
        lean_pod_byte_ptr uv = NULL;
        return lean_pod_UVector_toRepr(uv);
    }
    size_t byteSize = lean_usize_of_nat(lean_pod_Storable_byteSize(sb));
    lean_pod_byte_ptr uv = lean_pod_calloc(count * byteSize);
    return lean_pod_UVector_toRepr(uv);
}

LEAN_EXPORT lean_obj_res lean_pod_UVector_replicate(b_lean_obj_arg n, b_lean_obj_arg sb, b_lean_obj_arg wb, b_lean_obj_arg v)
{
    size_t count = lean_usize_of_nat(n);
    if (LEAN_UNLIKELY(count == 0)) {
        lean_pod_byte_ptr uv = NULL;
        return lean_pod_UVector_toRepr(uv);
    }
    size_t byteSize = lean_usize_of_nat(lean_pod_Storable_byteSize(sb));
    lean_pod_byte_ptr uv = lean_pod_alloc(count * byteSize);
    lean_object* writeBytesRefOffEl = lean_pod_WriteBytes_writeBytesRefOffEl(wb);
    lean_object* byteSizeArray_box = lean_usize_to_nat(count * byteSize);
    lean_object* bytesRef = lean_pod_BytesRef_wrap(uv);
    lean_inc_ref_n(writeBytesRefOffEl, count);
    lean_inc_n(byteSizeArray_box, count - 1);
    lean_inc_ref_n(bytesRef, count - 1);
    lean_inc_n(v, count);
    for(size_t i = 0; i < count; ++i) {
        lean_dec_ref(lean_apply_7(
            writeBytesRefOffEl,
            lean_box(0),
            byteSizeArray_box,
            bytesRef,
            lean_usize_to_nat(i),
            v,
            lean_box(0),
            lean_box(0)
        ));
    }
    return lean_pod_UVector_toRepr(uv);
}

LEAN_EXPORT lean_obj_res lean_pod_UVector_raw(b_lean_obj_arg n, b_lean_obj_arg sb, lean_obj_arg uv) {
    return lean_pod_BytesView_wrap(lean_pod_UVector_fromRepr(uv), uv);
}

static inline lean_obj_res lean_pod_UVector_get_impl(b_lean_obj_arg sb, b_lean_obj_arg rb, b_lean_obj_arg uv, size_t i) {
    size_t byteSize = lean_usize_of_nat(lean_pod_Storable_byteSize(sb));
    lean_object* readBytesRef = lean_pod_ReadBytes_readBytesRef(rb);
    lean_inc_ref(readBytesRef);
    lean_object* res = lean_apply_3(
        readBytesRef,
        lean_box(0),
        lean_pod_BytesRef_wrap(lean_pod_UVector_fromRepr(uv) + i * byteSize),
        lean_box(0)
    );
    lean_object* val = lean_ctor_get(res, 0);
    lean_inc(val);
    lean_dec_ref(res);
    return val;
}

LEAN_EXPORT lean_obj_res lean_pod_UVector_get(
    b_lean_obj_arg n, b_lean_obj_arg sb, b_lean_obj_arg rb, b_lean_obj_arg uv, b_lean_obj_arg i
) {
    return lean_pod_UVector_get_impl(sb, rb, uv, lean_usize_of_nat(i));
}

LEAN_EXPORT lean_obj_res lean_pod_UVector_get_or_panic(
    b_lean_obj_arg n, b_lean_obj_arg def_val, b_lean_obj_arg sb, b_lean_obj_arg rb,
    b_lean_obj_arg uv, b_lean_obj_arg i_nat
) {
    size_t count = lean_usize_of_nat(n);
    size_t i = lean_usize_of_nat(i_nat);
    if(i >= count) {
        lean_inc(def_val);
        return lean_array_get_panic(def_val);
    }
    return lean_pod_UVector_get_impl(sb, rb, uv, i);
}

static inline lean_obj_res lean_pod_UVector_set_impl(
    size_t count, b_lean_obj_arg sb, b_lean_obj_arg wb,
    lean_obj_arg uv_old, size_t i, lean_obj_arg v
) {
    size_t byteSize = lean_usize_of_nat(lean_pod_Storable_byteSize(sb));
    lean_object* uv;
    if(LEAN_LIKELY(lean_is_exclusive(uv_old))) {
        uv = uv_old;
    }
    else {
        uv = lean_pod_UVector_clone(count * byteSize, uv_old);
        lean_dec_ref(uv_old);
    }
    lean_object* writeBytesRef = lean_pod_WriteBytes_writeBytesRef(wb);
    lean_inc_ref(writeBytesRef);
    lean_dec_ref(lean_apply_4(
        writeBytesRef,
        lean_box(0),
        lean_pod_BytesRef_wrap(lean_pod_UVector_fromRepr(uv) + i * byteSize),
        v,
        lean_box(0)
    ));
    return uv;
}

LEAN_EXPORT lean_obj_res lean_pod_UVector_set(
    b_lean_obj_arg n, b_lean_obj_arg sb, b_lean_obj_arg wb,
    lean_obj_arg uv, b_lean_obj_arg i, lean_obj_arg v
) {
    return lean_pod_UVector_set_impl(lean_usize_of_nat(n), sb, wb, uv, lean_usize_of_nat(i), v);
}

LEAN_EXPORT lean_obj_res lean_pod_UVector_set_or_panic(
    b_lean_obj_arg n, b_lean_obj_arg sb, b_lean_obj_arg wb,
    lean_obj_arg uv, b_lean_obj_arg i_nat, lean_obj_arg v
) {
    size_t count = lean_usize_of_nat(n);
    size_t i = lean_usize_of_nat(i_nat);
    if(i >= count) {
        return lean_array_set_panic(uv, v);
    }
    return lean_pod_UVector_set_impl(count, sb, wb, uv, i, v);
}
