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

LEAN_EXPORT size_t lean_pod_USize_bswap(size_t x) {
    #if INTPTR_MAX == INT32_MAX
        return lean_pod_bswap32(x);
    #elif INTPTR_MAX == INT64_MAX
        return lean_pod_bswap64(x);
    #else
        #error Unsupported
    #endif
}

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
LEAN_EXPORT uint16_t lean_pod_UInt16_toLittleEndian(uint16_t x) { return x; }
LEAN_EXPORT uint32_t lean_pod_UInt32_toLittleEndian(uint32_t x) { return x; }
LEAN_EXPORT uint64_t lean_pod_UInt64_toLittleEndian(uint64_t x) { return x; }
LEAN_EXPORT size_t lean_pod_USize_toLittleEndian(size_t x) { return x; }
LEAN_EXPORT uint16_t lean_pod_UInt16_toBigEndian(uint16_t x) { return lean_pod_bswap16(x); }
LEAN_EXPORT uint32_t lean_pod_UInt32_toBigEndian(uint32_t x) { return lean_pod_bswap32(x); }
LEAN_EXPORT uint64_t lean_pod_UInt64_toBigEndian(uint64_t x) { return lean_pod_bswap64(x); }
LEAN_EXPORT size_t lean_pod_USize_toBigEndian(size_t x) { return lean_pod_USize_bswap(x); }
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
LEAN_EXPORT uint16_t lean_pod_UInt16_toLittleEndian(uint16_t x) { return lean_pod_bswap16(x); }
LEAN_EXPORT uint32_t lean_pod_UInt32_toLittleEndian(uint32_t x) { return lean_pod_bswap32(x); }
LEAN_EXPORT uint64_t lean_pod_UInt64_toLittleEndian(uint64_t x) { return lean_pod_bswap64(x); }
LEAN_EXPORT size_t lean_pod_USize_toLittleEndian(size_t x) { return lean_pod_USize_bswap(x); }
LEAN_EXPORT uint16_t lean_pod_UInt16_toBigEndian(uint16_t x) { return x; }
LEAN_EXPORT uint32_t lean_pod_UInt32_toBigEndian(uint32_t x) { return x; }
LEAN_EXPORT uint64_t lean_pod_UInt64_toBigEndian(uint64_t x) { return x; }
LEAN_EXPORT size_t lean_pod_USize_toBigEndian(size_t x) { return x; }
#else
#error unsupported
#endif
