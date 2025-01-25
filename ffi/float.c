#include <math.h>
#include <lean/lean.h>
#include "include/lean_pod.h"

#define LEAN_POD_CAST_FLOAT32_FROM(ltyp, abiatyp, fromabi)\
LEAN_EXPORT float lean_pod_##ltyp##_toFloat32(abiatyp x) {\
    return (float)(fromabi(x));\
}

LEAN_POD_CAST_FLOAT32_FROM(UInt8, uint8_t, LEAN_POD_IDENTITY);
LEAN_POD_CAST_FLOAT32_FROM(UInt16, uint16_t, LEAN_POD_IDENTITY);
LEAN_POD_CAST_FLOAT32_FROM(UInt32, uint32_t, LEAN_POD_IDENTITY);
LEAN_POD_CAST_FLOAT32_FROM(USize, size_t, LEAN_POD_IDENTITY);
LEAN_POD_CAST_FLOAT32_FROM(Int8, lean_pod_Int8, lean_pod_Int8_fromRepr);
LEAN_POD_CAST_FLOAT32_FROM(Int16, lean_pod_Int16, lean_pod_Int16_fromRepr);
LEAN_POD_CAST_FLOAT32_FROM(Int32, lean_pod_Int32, lean_pod_Int32_fromRepr);
LEAN_POD_CAST_FLOAT32_FROM(Int64, lean_pod_Int64, lean_pod_Int64_fromRepr);

LEAN_EXPORT lean_obj_arg lean_pod_String_toFloat32(b_lean_obj_arg s) {
    char* retEnd = NULL;
    const char* cstr = lean_string_cstr(s);
    const char* end = cstr + lean_string_size(s) - 1;
    float x = strtof(cstr, &retEnd);
    if (retEnd != end) {
        return lean_mk_option_none();
    }
    return lean_mk_option_some(lean_box_float32(x));
}

LEAN_EXPORT lean_obj_arg lean_pod_Substring_toFloat32(b_lean_obj_arg s) {
    const char* data = lean_string_cstr(lean_ctor_get(s, 0));
    size_t start = lean_usize_of_nat(lean_ctor_get(s, 1));
    size_t stop = lean_usize_of_nat(lean_ctor_get(s, 2));
    char* cpy = malloc(stop - start + 1);
    memcpy(cpy, data + start, stop - start);
    cpy[stop - start] = '\0';
    char* end = NULL;
    float x = strtof(cpy, &end);
    free(cpy);
    if (end != cpy + (stop - start)) {
        return lean_mk_option_none();
    }
    return lean_mk_option_some(lean_box_float32(x));
}

#define LEAN_POD_CAST_FLOAT32_TO(ltyp, ctyp, abirtyp, toabi)\
LEAN_EXPORT abirtyp lean_pod_Float32_to##ltyp(float x) {\
    return toabi((ctyp)x);\
}

LEAN_POD_CAST_FLOAT32_TO(Int8, int8_t, lean_pod_Int8, lean_pod_Int8_toRepr);
LEAN_POD_CAST_FLOAT32_TO(Int16, int16_t, lean_pod_Int16, lean_pod_Int16_toRepr);
LEAN_POD_CAST_FLOAT32_TO(Int32, int32_t, lean_pod_Int32, lean_pod_Int32_toRepr);
LEAN_POD_CAST_FLOAT32_TO(Int64, int64_t, lean_pod_Int64, lean_pod_Int64_toRepr);

LEAN_EXPORT uint8_t lean_pod_Float32_isNormal(float x) {
    return isnormal(x);
}

LEAN_EXPORT uint8_t lean_pod_Float32_isUnordered(float x, float y) {
    return isunordered(x, y);
}
