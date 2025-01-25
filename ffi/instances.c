#include <string.h>
#include "include/lean_pod.h"

LEAN_POD_RWBYTES_INST(UInt8, uint8_t, uint8_t, lean_box, LEAN_POD_IDENTITY, LEAN_POD_IDENTITY)
LEAN_POD_RWBYTES_INST(UInt16, uint16_t, uint16_t, lean_box, LEAN_POD_IDENTITY, LEAN_POD_IDENTITY)
LEAN_POD_RWBYTES_INST(UInt32, uint32_t, uint32_t, lean_box_uint32, LEAN_POD_IDENTITY, LEAN_POD_IDENTITY)
LEAN_POD_RWBYTES_INST(UInt64, uint64_t, uint64_t, lean_box_uint64, LEAN_POD_IDENTITY, LEAN_POD_IDENTITY)
LEAN_POD_RWBYTES_INST(USize, size_t, size_t, lean_box_usize, LEAN_POD_IDENTITY, LEAN_POD_IDENTITY)
LEAN_POD_RWBYTES_INST(Float, double, double, lean_box_float, LEAN_POD_IDENTITY, LEAN_POD_IDENTITY)
LEAN_POD_RWBYTES_INST(Pod_UFixnum, size_t, lean_pod_UFixnum, lean_pod_UFixnum_box, lean_pod_UFixnum_toRepr, lean_pod_UFixnum_fromRepr)
LEAN_POD_RWBYTES_INST(Int8, int8_t, lean_pod_Int8, lean_pod_Int8_box, lean_pod_Int8_toRepr, lean_pod_Int8_fromRepr)
LEAN_POD_RWBYTES_INST(Int16, int16_t, lean_pod_Int16, lean_pod_Int16_box, lean_pod_Int16_toRepr, lean_pod_Int16_fromRepr)
LEAN_POD_RWBYTES_INST(Int32, int32_t, lean_pod_Int32, lean_pod_Int32_box, lean_pod_Int32_toRepr, lean_pod_Int32_fromRepr)
LEAN_POD_RWBYTES_INST(Int64, int64_t, lean_pod_Int64, lean_pod_Int64_box, lean_pod_Int64_toRepr, lean_pod_Int64_fromRepr)
LEAN_POD_RWBYTES_INST(Float32, float, float, lean_box_float32, LEAN_POD_IDENTITY, LEAN_POD_IDENTITY)
