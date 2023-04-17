#pragma once

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define LEAN_POD_BYTESREF_E_KEEP Le
#define LEAN_POD_BYTESREF_E_SWAP Be
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define LEAN_POD_BYTESREF_E_KEEP Be
#define LEAN_POD_BYTESREF_E_SWAP Le
#else
#error unsupported
#endif

#define LEAN_POD_CONCAT3_IMPL(x, y, z) x ## y ## z
#define LEAN_POD_CONCAT3(x, y, z) LEAN_POD_CONCAT3_IMPL(x, y, z)
