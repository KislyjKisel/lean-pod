#include <string.h>
#include "include/lean_pod.h"

LEAN_POD_RWBYTES_INST(uint8_t, UInt8, lean_box)
LEAN_POD_RWBYTES_INST(uint16_t, UInt16, lean_box)
LEAN_POD_RWBYTES_INST(uint32_t, UInt32, lean_box_uint32)
LEAN_POD_RWBYTES_INST(uint64_t, UInt64, lean_box_uint64)
LEAN_POD_RWBYTES_INST(size_t, USize, lean_box_usize)
LEAN_POD_RWBYTES_INST(double, Float, lean_box_float)
LEAN_POD_RWBYTES_INST(uint32_t, Float32, lean_box_uint32)
