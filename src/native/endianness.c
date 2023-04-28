#include <lean/lean.h>

LEAN_EXPORT uint8_t lean_pod_getEndianness(lean_obj_arg unit) {
    #if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
        return 0;
    #elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
        return 1;
    #else
        #error unsupported
    #endif
}
