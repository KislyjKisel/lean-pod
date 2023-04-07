#include "include/lean_pod.h"

LEAN_EXPORT uint16_t lean_pod_UInt16_bswap(uint16_t x) {
    return lean_pod_bswap16(x);
}

LEAN_EXPORT uint32_t lean_pod_UInt32_bswap(uint32_t x) {
    return lean_pod_bswap32(x);
}

LEAN_EXPORT uint64_t lean_pod_UInt64_bswap(uint64_t x) {
    return lean_pod_bswap64(x);
}
