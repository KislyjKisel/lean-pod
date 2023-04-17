#include <stdint.h>
#include <stdio.h>
#include <math.h>
#include <lean/lean.h>
#include "include/lean_pod.h"

#define LEAN_POD_CAST_FLOAT32_FROM(ltyp, ctyp)\
LEAN_EXPORT uint32_t lean_pod_##ltyp##_toFloat32(ctyp x) {\
    return lean_pod_Float32_toBits((float)x);\
}

LEAN_POD_CAST_FLOAT32_FROM(Float, double);
LEAN_POD_CAST_FLOAT32_FROM(UInt8, uint8_t);
LEAN_POD_CAST_FLOAT32_FROM(UInt16, uint16_t);
LEAN_POD_CAST_FLOAT32_FROM(UInt32, uint32_t);
LEAN_POD_CAST_FLOAT32_FROM(UInt64, uint64_t);
LEAN_POD_CAST_FLOAT32_FROM(USize, size_t);

#define LEAN_POD_CAST_FLOAT32_TO(ltyp, ctyp)\
LEAN_EXPORT ctyp lean_pod_Float32_to##ltyp(uint32_t x) {\
    return (ctyp)lean_pod_Float32_fromBits(x);\
}

LEAN_POD_CAST_FLOAT32_TO(Float, double);
LEAN_POD_CAST_FLOAT32_TO(UInt8, uint8_t);
LEAN_POD_CAST_FLOAT32_TO(UInt16, uint16_t);
LEAN_POD_CAST_FLOAT32_TO(UInt32, uint32_t);
LEAN_POD_CAST_FLOAT32_TO(UInt64, uint64_t);
LEAN_POD_CAST_FLOAT32_TO(USize, size_t);

LEAN_EXPORT lean_obj_res lean_pod_Float32_toString(uint32_t x) {
    static char buf[64];
    snprintf(buf, sizeof(buf), "%g", lean_pod_Float32_fromBits(x));
    return lean_mk_string(buf);
}

#define LEAN_POD_FLOAT32_OP2(lop, cop)\
LEAN_EXPORT uint32_t lean_pod_Float32_##lop(uint32_t x, uint32_t y) {\
    return lean_pod_Float32_toBits(\
        lean_pod_Float32_fromBits(x) cop lean_pod_Float32_fromBits(y)\
    );\
}

LEAN_POD_FLOAT32_OP2(add, +);
LEAN_POD_FLOAT32_OP2(sub, -);
LEAN_POD_FLOAT32_OP2(mul, *);
LEAN_POD_FLOAT32_OP2(div, /);

LEAN_EXPORT uint32_t lean_pod_Float32_neg(uint32_t x) {
    return lean_pod_Float32_toBits(
        -lean_pod_Float32_fromBits(x)
    );
}

LEAN_EXPORT uint8_t lean_pod_Float32_beq(uint32_t x, uint32_t y) {
    return lean_pod_Float32_fromBits(x) == lean_pod_Float32_fromBits(y);
}

LEAN_EXPORT uint8_t lean_pod_Float32_blt(uint32_t x, uint32_t y) {
    return lean_pod_Float32_fromBits(x) < lean_pod_Float32_fromBits(y);
}

LEAN_EXPORT uint8_t lean_pod_Float32_ble(uint32_t x, uint32_t y) {
    return lean_pod_Float32_fromBits(x) <= lean_pod_Float32_fromBits(y);
}

LEAN_EXPORT uint32_t lean_pod_Float32_min(uint32_t x, uint32_t y) {
    return lean_pod_Float32_toBits(
        fminf(lean_pod_Float32_fromBits(x), lean_pod_Float32_fromBits(y))
    );
}

LEAN_EXPORT uint32_t lean_pod_Float32_max(uint32_t x, uint32_t y) {
    return lean_pod_Float32_toBits(
        fmaxf(lean_pod_Float32_fromBits(x), lean_pod_Float32_fromBits(y))
    );
}

#define LEAN_POD_FLOAT32_IS(ln, cn)\
LEAN_EXPORT uint8_t lean_pod_Float32_is##ln(uint32_t x) {\
    return (bool)is##cn(lean_pod_Float32_fromBits(x));\
}

LEAN_POD_FLOAT32_IS(NaN, nan);
LEAN_POD_FLOAT32_IS(Finite, finite);
LEAN_POD_FLOAT32_IS(Inf, inf);
LEAN_POD_FLOAT32_IS(Normal, normal);

LEAN_EXPORT uint8_t lean_pod_Float32_isUnordered(uint32_t x, uint32_t y) {
    return (bool)isunordered(
        lean_pod_Float32_fromBits(x),
        lean_pod_Float32_fromBits(y)
    );
}

LEAN_EXPORT lean_obj_res lean_pod_Float32_frExp(uint32_t x_w) {
    float x = lean_pod_Float32_fromBits(x_w);
    lean_object* result = lean_alloc_ctor(0, 2, 0);
    int exp;
    lean_ctor_set(result, 0, lean_pod_Float32_box(frexpf(x, &exp)));
    lean_ctor_set(result, 1, isfinite(x) ? lean_int_to_int(exp) : lean_box(0));
    return result;
}

#define LEAN_POD_FLOAT32_F1(fn)\
LEAN_EXPORT uint32_t lean_pod_Float32_##fn(uint32_t x) {\
    return lean_pod_Float32_toBits(fn##f(lean_pod_Float32_fromBits(x)));\
}

LEAN_POD_FLOAT32_F1(sin);
LEAN_POD_FLOAT32_F1(cos);
LEAN_POD_FLOAT32_F1(tan);
LEAN_POD_FLOAT32_F1(asin);
LEAN_POD_FLOAT32_F1(acos);
LEAN_POD_FLOAT32_F1(atan);
LEAN_POD_FLOAT32_F1(sinh);
LEAN_POD_FLOAT32_F1(cosh);
LEAN_POD_FLOAT32_F1(tanh);
LEAN_POD_FLOAT32_F1(asinh);
LEAN_POD_FLOAT32_F1(acosh);
LEAN_POD_FLOAT32_F1(atanh);
LEAN_POD_FLOAT32_F1(exp);
LEAN_POD_FLOAT32_F1(exp2);
LEAN_POD_FLOAT32_F1(log);
LEAN_POD_FLOAT32_F1(log2);
LEAN_POD_FLOAT32_F1(log10);
LEAN_POD_FLOAT32_F1(sqrt);
LEAN_POD_FLOAT32_F1(cbrt);
LEAN_POD_FLOAT32_F1(ceil);
LEAN_POD_FLOAT32_F1(floor);
LEAN_POD_FLOAT32_F1(round);

LEAN_EXPORT uint32_t lean_pod_Float32_abs(uint32_t x) {
    return lean_pod_Float32_toBits(fabsf(lean_pod_Float32_fromBits(x)));
}

LEAN_EXPORT uint32_t lean_pod_Float32_atan2(uint32_t y, uint32_t x) {
    return lean_pod_Float32_toBits(atan2f(lean_pod_Float32_fromBits(y), lean_pod_Float32_fromBits(x)));
}

LEAN_EXPORT uint32_t lean_pod_Float32_pow(uint32_t x, uint32_t y) {
    return lean_pod_Float32_toBits(powf(lean_pod_Float32_fromBits(x), lean_pod_Float32_fromBits(y)));
}

LEAN_EXPORT uint32_t lean_pod_Float32_scaleB(uint32_t x_w, b_lean_obj_arg i) {
    float x = lean_pod_Float32_fromBits(x_w);
    if (lean_is_scalar(i)) {
        return lean_pod_Float32_toBits(scalbnf(x, lean_scalar_to_int(i)));
    } else if (x == 0.0 || lean_int_big_lt(i, lean_int_to_int(0))) {
        // ^ todo: use mpz_value(i).is_neg() (req cpp?)
        return lean_pod_Float32_toBits(0.0);
    } else {
        return lean_pod_Float32_toBits(x * (1.0f / 0.0f));
    }
}

LEAN_EXPORT uint64_t lean_pod_Float_bits(double x) {
    union {
        double d;
        uint64_t b;
    } u;
    u.d = x;
    return u.b;
}
