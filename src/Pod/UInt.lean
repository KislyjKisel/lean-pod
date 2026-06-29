module

import Alloy.C
import Pod.Endianness

open scoped Alloy.C

alloy c include <lean/lean.h>

public section

namespace Pod

alloy c section

LEAN_EXPORT uint16_t lean_pod_UInt16_bswap(uint16_t value) {
  #if defined(__GNUC__) || defined(__clang__)
    return __builtin_bswap16(value);
  /**/
  #elif defined(_MSC_VER)
    return _byteswap_ushort(value);
  /**/
  #else
    return (value << 8) | (value >> 8);
  /**/
  #endif
}

LEAN_EXPORT uint32_t lean_pod_UInt32_bswap(uint32_t value) {
  #if defined(__GNUC__) || defined(__clang__)
    return __builtin_bswap32(value);
  /**/
  #elif defined(_MSC_VER)
    return _byteswap_ulong(value);
  /**/
  #else
    return
      ((value & UINT32_C(0x000000FF)) << 24) |
      ((value & UINT32_C(0x0000FF00)) <<  8) |
      ((value & UINT32_C(0x00FF0000)) >>  8) |
      ((value & UINT32_C(0xFF000000)) >> 24);
  /**/
  #endif
}

LEAN_EXPORT uint64_t lean_pod_UInt64_bswap(uint64_t value) {
  #if defined(__GNUC__) || defined(__clang__)
    return __builtin_bswap64(value);
  /**/
  #elif defined(_MSC_VER)
    return _byteswap_uint64(value);
  /**/
  #else
    return
      ((value & UINT64_C(0xFF00000000000000)) >> 56) |
      ((value & UINT64_C(0x00FF000000000000)) >> 40) |
      ((value & UINT64_C(0x0000FF0000000000)) >> 24) |
      ((value & UINT64_C(0x000000FF00000000)) >>  8) |
      ((value & UINT64_C(0x00000000FF000000)) <<  8) |
      ((value & UINT64_C(0x0000000000FF0000)) << 24) |
      ((value & UINT64_C(0x000000000000FF00)) << 40) |
      ((value & UINT64_C(0x00000000000000FF)) << 56);
  /**/
  #endif
}

LEAN_EXPORT size_t lean_pod_USize_bswap(size_t x) {
  #if INTPTR_MAX == INT32_MAX
    return lean_pod_UInt32_bswap(x);
  /**/
  #elif INTPTR_MAX == INT64_MAX
    return lean_pod_UInt64_bswap(x);
  /**/
  #else
    #error Unsupported target with USize being neither 32-bit nor 64-bit.
  /**/
  #endif
}

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  LEAN_EXPORT uint16_t lean_pod_UInt16_toLittleEndian(uint16_t x) { return x; }
  LEAN_EXPORT uint32_t lean_pod_UInt32_toLittleEndian(uint32_t x) { return x; }
  LEAN_EXPORT uint64_t lean_pod_UInt64_toLittleEndian(uint64_t x) { return x; }
  LEAN_EXPORT size_t lean_pod_USize_toLittleEndian(size_t x) { return x; }
  LEAN_EXPORT uint16_t lean_pod_UInt16_toBigEndian(uint16_t x) { return lean_pod_UInt16_bswap(x); }
  LEAN_EXPORT uint32_t lean_pod_UInt32_toBigEndian(uint32_t x) { return lean_pod_UInt32_bswap(x); }
  LEAN_EXPORT uint64_t lean_pod_UInt64_toBigEndian(uint64_t x) { return lean_pod_UInt64_bswap(x); }
  LEAN_EXPORT size_t lean_pod_USize_toBigEndian(size_t x) { return lean_pod_USize_bswap(x); }
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  LEAN_EXPORT uint16_t lean_pod_UInt16_toLittleEndian(uint16_t x) { return lean_pod_UInt16_bswap(x); }
  LEAN_EXPORT uint32_t lean_pod_UInt32_toLittleEndian(uint32_t x) { return lean_pod_UInt32_bswap(x); }
  LEAN_EXPORT uint64_t lean_pod_UInt64_toLittleEndian(uint64_t x) { return lean_pod_UInt64_bswap(x); }
  LEAN_EXPORT size_t lean_pod_USize_toLittleEndian(size_t x) { return lean_pod_USize_bswap(x); }
  LEAN_EXPORT uint16_t lean_pod_UInt16_toBigEndian(uint16_t x) { return x; }
  LEAN_EXPORT uint32_t lean_pod_UInt32_toBigEndian(uint32_t x) { return x; }
  LEAN_EXPORT uint64_t lean_pod_UInt64_toBigEndian(uint64_t x) { return x; }
  LEAN_EXPORT size_t lean_pod_USize_toBigEndian(size_t x) { return x; }
#else
  #error Unsupported target with byte order neither little endian nor big endian.
#endif

end

@[extern "lean_pod_UInt16_bswap"]
def UInt16.bswap (value : UInt16) : UInt16 :=
  (value <<< 8) ||| (value >>> 8)

@[extern "lean_pod_UInt16_toBigEndian"]
def UInt16.toBigEndian (value : UInt16) :=
  if Pod.endianness = .big
    then value
    else bswap value

@[extern "lean_pod_UInt16_toLittleEndian"]
def UInt16.toLittleEndian (value : UInt16) :=
  if Pod.endianness = .little
    then value
    else bswap value

@[extern "lean_pod_UInt32_bswap"]
def UInt32.bswap (value : UInt32) : UInt32 :=
  ((value &&& 0x000000FF) <<< 24) |||
  ((value &&& 0x0000FF00) <<<  8) |||
  ((value &&& 0x00FF0000) >>>  8) |||
  ((value &&& 0xFF000000) >>> 24)

@[extern "lean_pod_UInt32_toBigEndian"]
def UInt32.toBigEndian (value : UInt32) :=
  if Pod.endianness = .big
    then value
    else bswap value

@[extern "lean_pod_UInt32_toLittleEndian"]
def UInt32.toLittleEndian (value : UInt32) :=
  if Pod.endianness = .little
    then value
    else bswap value

@[extern "lean_pod_UInt64_bswap"]
def UInt64.bswap (value : UInt64) : UInt64 :=
  ((value &&& 0xFF00000000000000) >>> 56) |||
  ((value &&& 0x00FF000000000000) >>> 40) |||
  ((value &&& 0x0000FF0000000000) >>> 24) |||
  ((value &&& 0x000000FF00000000) >>>  8) |||
  ((value &&& 0x00000000FF000000) <<<  8) |||
  ((value &&& 0x0000000000FF0000) <<< 24) |||
  ((value &&& 0x000000000000FF00) <<< 40) |||
  ((value &&& 0x00000000000000FF) <<< 56)

@[extern "lean_pod_UInt64_toBigEndian"]
def UInt64.toBigEndian (value : UInt64) :=
  if Pod.endianness = .big
    then value
    else bswap value

@[extern "lean_pod_UInt64_toLittleEndian"]
def UInt64.toLittleEndian (value : UInt64) :=
  if Pod.endianness = .little
    then value
    else bswap value

@[extern "lean_pod_USize_bswap"]
opaque USize.bswap (value : USize) : USize

@[extern "lean_pod_USize_toBigEndian"]
def USize.toBigEndian (value : USize) :=
  if Pod.endianness = .big
    then value
    else bswap value

@[extern "lean_pod_USize_toLittleEndian"]
def USize.toLittleEndian (value : USize) :=
  if Pod.endianness = .little
    then value
    else bswap value
