import Pod.UInt

set_option autoImplicit false

namespace Pod

opaque BytesRefPointed (σ : Type) (size : USize) (alignment : Nat) : NonemptyType
def BytesRef (σ : Type) (size : USize) (alignment : Nat) : Type := (BytesRefPointed σ size alignment).type
instance {σ size alignment} : Nonempty (BytesRef σ size alignment) := (BytesRefPointed σ size alignment).property

@[extern "lean_pod_BytesView_id"]
opaque weaken {σ size alignment0 alignment1} (h : alignment1 ≤ alignment0) :
  BytesRef σ size alignment0 → BytesRef σ size alignment1

@[extern "lean_pod_BytesView_id"]
opaque take {σ size alignment} (bv : BytesRef σ size alignment) (count : USize) (h : count ≤ size) : BytesRef σ count alignment

@[extern "lean_pod_BytesView_drop"]
opaque drop {σ size alignment} (bv : BytesRef σ size alignment) (count : USize) (h : count ≤ size) : BytesRef σ (size - count) (alignment.gcd count.toNat)

/--
Read a `UInt8`.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt8"]
opaque getUInt8 {σ size alignment} (bv : @& BytesRef σ size alignment) (i : USize) (h : i < size) : ST σ UInt8

/--
Read a `UInt16` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt16Ne"]
opaque getUInt16Ne {σ size} (bv : @& BytesRef σ size UInt16.alignment) (i : USize) (h : i + 1 < size) : ST σ UInt16

/--
Read a `UInt16` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt16Le"]
opaque getUInt16Le {σ size} (bv : @& BytesRef σ size UInt16.alignment) (i : USize) (h : i + 1 < size) : ST σ UInt16

/--
Read a `UInt16` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt16Be"]
opaque getUInt16Be {σ size} (bv : @& BytesRef σ size UInt16.alignment) (i : USize) (h : i + 1 < size) : ST σ UInt16

/--
Read a `UInt32` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt32Ne"]
opaque getUInt32Ne {σ size} (bv : @& BytesRef σ size UInt32.alignment) (i : USize) (h : i + 3 < size) : ST σ UInt32

/--
Read a `UInt32` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt32Le"]
opaque getUInt32Le {σ size} (bv : @& BytesRef σ size UInt32.alignment) (i : USize) (h : i + 3 < size) : ST σ UInt32

/--
Read a `UInt32` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt32Be"]
opaque getUInt32Be {σ size} (bv : @& BytesRef σ size UInt32.alignment) (i : USize) (h : i + 3 < size) : ST σ UInt32

/--
Read a `UInt64` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt64Ne"]
opaque getUInt64Ne {σ size} (bv : @& BytesRef σ size UInt64.alignment) (i : USize) (h : i + 7 < size) : ST σ UInt64

/--
Read a `UInt64` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt64Le"]
opaque getUInt64Le {σ size} (bv : @& BytesRef σ size UInt64.alignment) (i : USize) (h : i + 7 < size) : ST σ UInt64

/--
Read a `UInt64` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt64Be"]
opaque getUInt64Be {σ size} (bv : @& BytesRef σ size UInt64.alignment) (i : USize) (h : i + 7 < size) : ST σ UInt64

/--
Write to a `UInt8`.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt8"]
opaque setUInt8 {σ size alignment} (bv : @& BytesRef σ size alignment) (i : USize) (h : i < size) (value : UInt8) : ST σ Unit

/--
Write to a `UInt16` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt16Ne"]
opaque setUInt16Ne {σ size} (bv : @& BytesRef σ size UInt16.alignment) (i : USize) (h : i + 1 < size) (value : UInt16) : ST σ Unit

/--
Write to a `UInt16` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt16Le"]
opaque setUInt16Le {σ size} (bv : @& BytesRef σ size UInt16.alignment) (i : USize) (h : i + 1 < size) (value : UInt16) : ST σ Unit

/--
Write to a `UInt16` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt16Be"]
opaque setUInt16Be {σ size} (bv : @& BytesRef σ size UInt16.alignment) (i : USize) (h : i + 1 < size) (value : UInt16) : ST σ Unit

/--
Write to a `UInt32` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt32Ne"]
opaque setUInt32Ne {σ size} (bv : @& BytesRef σ size UInt32.alignment) (i : USize) (h : i + 3 < size) (value : UInt32) : ST σ Unit

/--
Write to a `UInt32` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt32Le"]
opaque setUInt32Le {σ size} (bv : @& BytesRef σ size UInt32.alignment) (i : USize) (h : i + 3 < size) (value : UInt32) : ST σ Unit

/--
Write to a `UInt32` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt32Be"]
opaque setUInt32Be {σ size} (bv : @& BytesRef σ size UInt32.alignment) (i : USize) (h : i + 3 < size) (value : UInt32) : ST σ Unit

/--
Write to a `UInt64` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt64Ne"]
opaque setUInt64Ne {σ size} (bv : @& BytesRef σ size UInt64.alignment) (i : USize) (h : i + 7 < size) (value : UInt64) : ST σ Unit

/--
Write to a `UInt64` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt64Le"]
opaque setUInt64Le {σ size} (bv : @& BytesRef σ size UInt64.alignment) (i : USize) (h : i + 7 < size) (value : UInt64) : ST σ Unit

/--
Write to a `UInt64` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt64Be"]
opaque setUInt64Be {σ size} (bv : @& BytesRef σ size UInt64.alignment) (i : USize) (h : i + 7 < size) (value : UInt64) : ST σ Unit

end Pod
