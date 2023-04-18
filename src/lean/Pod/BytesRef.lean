import Pod.Lemmas
import Pod.Util
import Pod.UInt

set_option autoImplicit false

namespace Pod

inductive Mutability where
  | Mutable
  -- can't mutate by itself, but content can be mutated through other ptrs
  | Immutable

variable {σ : Type}

opaque BytesRefPointed (σ : Type) (mutab : Mutability) (size : USize) (align : Nat) : NonemptyType

def BytesRef (σ : Type) (mutab : Mutability) (size : USize) (align : Nat) : Type :=
  (BytesRefPointed σ mutab size align).type

abbrev BytesRefMut (σ : Type) := BytesRef σ .Mutable
abbrev BytesRefImm (σ : Type) := BytesRef σ .Immutable

instance {size mutab align} : Nonempty (BytesRef σ mutab size align) := (BytesRefPointed σ mutab size align).property

/-- Clones array if it is shared. -/
@[extern "lean_pod_ByteArray_ref"]
opaque _root_.ByteArray.ref (ba : ByteArray) : ST σ (BytesRefMut σ ba.size.toUSize 1)

namespace BytesRef

@[extern "lean_pod_BytesRef_drop"]
opaque weaken {mutab size} {align0 align1 : @& Nat} (h : align1 ≤ align0) :
  BytesRef σ mutab size align0 → BytesRef σ mutab size align1

@[extern "lean_pod_BytesRef_imm"]
opaque imm {mutab size} {align : @& Nat} : BytesRef σ mutab size align → BytesRefImm σ size align

@[extern "lean_pod_BytesRef_take"]
opaque take {mutab size} {align : @& Nat} (bv : BytesRef σ mutab size align)
  (count : USize) (h : count ≤ size) : BytesRef σ mutab count align

@[extern "lean_pod_BytesRef_drop"]
opaque drop {mutab size} {align : @& Nat} (bv : BytesRef σ mutab size align)
  (count : USize) (h : count ≤ size) : BytesRef σ mutab (size - count) (align.gcd count.toNat)

@[extern "lean_pod_BytesRef_slice"]
opaque slice {mutab size} {align : @& Nat} (bv : BytesRef σ mutab size align) (start length : USize)
  (bounded : start.toNat + length.toNat ≤ size.toNat) : BytesRef σ mutab length (align.gcd start.toNat) :=
  let «start≤size» : start ≤ size := by
    apply Nat.le_trans $ Nat.le_sub_of_add_le bounded
    exact Nat.sub_le size.toNat length.toNat
  (bv.drop start «start≤size»).take length $ by
    show length.val ≤ (size.val - start.val).val
    rw [Fin.toNat_sub_distrib size.val start.val «start≤size»]
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    exact bounded

/--
Read all bytes into a `ByteArray`.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_toByteArray"]
opaque toByteArray {mutab size} {align : @& Nat} (bv : @& BytesRef σ mutab size align) : ST σ ByteArray

/--
Read a `UInt8`.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt8"]
opaque getUInt8 {mutab size} {align : @& Nat} (bv : @& BytesRef σ mutab size align) (i : USize) (h : i < size) : ST σ UInt8

/--
Read a `UInt16` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt16Ne"]
opaque getUInt16Ne {mutab size} (bv : @& BytesRef σ mutab size UInt16.alignment) (i : USize) (h : i + 1 < size) : ST σ UInt16

/--
Read a `UInt16` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt16Le"]
opaque getUInt16Le {mutab size} (bv : @& BytesRef σ mutab size UInt16.alignment) (i : USize) (h : i + 1 < size) : ST σ UInt16

/--
Read a `UInt16` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt16Be"]
opaque getUInt16Be {mutab size} (bv : @& BytesRef σ mutab size UInt16.alignment) (i : USize) (h : i + 1 < size) : ST σ UInt16

/--
Read a `UInt32` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt32Ne"]
opaque getUInt32Ne {mutab size} (bv : @& BytesRef σ mutab size UInt32.alignment) (i : USize) (h : i + 3 < size) : ST σ UInt32

/--
Read a `UInt32` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt32Le"]
opaque getUInt32Le {mutab size} (bv : @& BytesRef σ mutab size UInt32.alignment) (i : USize) (h : i + 3 < size) : ST σ UInt32

/--
Read a `UInt32` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt32Be"]
opaque getUInt32Be {mutab size} (bv : @& BytesRef σ mutab size UInt32.alignment) (i : USize) (h : i + 3 < size) : ST σ UInt32

/--
Read a `UInt64` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt64Ne"]
opaque getUInt64Ne {mutab size} (bv : @& BytesRef σ mutab size UInt64.alignment) (i : USize) (h : i + 7 < size) : ST σ UInt64

/--
Read a `UInt64` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt64Le"]
opaque getUInt64Le {mutab size} (bv : @& BytesRef σ mutab size UInt64.alignment) (i : USize) (h : i + 7 < size) : ST σ UInt64

/--
Read a `UInt64` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_getUInt64Be"]
opaque getUInt64Be {mutab size} (bv : @& BytesRef σ mutab size UInt64.alignment) (i : USize) (h : i + 7 < size) : ST σ UInt64

/--
Write to a `UInt8`.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt8"]
opaque setUInt8 {σ size align} (bv : @& BytesRefMut σ size align) (i : USize) (h : i < size) (value : UInt8) : ST σ Unit

/--
Write to a `UInt16` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt16Ne"]
opaque setUInt16Ne {size} (bv : @& BytesRefMut σ size UInt16.alignment) (i : USize) (h : i + 1 < size) (value : UInt16) : ST σ Unit

/--
Write to a `UInt16` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt16Le"]
opaque setUInt16Le {size} (bv : @& BytesRefMut σ size UInt16.alignment) (i : USize) (h : i + 1 < size) (value : UInt16) : ST σ Unit

/--
Write to a `UInt16` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt16Be"]
opaque setUInt16Be {size} (bv : @& BytesRefMut σ size UInt16.alignment) (i : USize) (h : i + 1 < size) (value : UInt16) : ST σ Unit

/--
Write to a `UInt32` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt32Ne"]
opaque setUInt32Ne {size} (bv : @& BytesRefMut σ size UInt32.alignment) (i : USize) (h : i + 3 < size) (value : UInt32) : ST σ Unit

/--
Write to a `UInt32` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt32Le"]
opaque setUInt32Le {size} (bv : @& BytesRefMut σ size UInt32.alignment) (i : USize) (h : i + 3 < size) (value : UInt32) : ST σ Unit

/--
Write to a `UInt32` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt32Be"]
opaque setUInt32Be {size} (bv : @& BytesRefMut σ size UInt32.alignment) (i : USize) (h : i + 3 < size) (value : UInt32) : ST σ Unit

/--
Write to a `UInt64` stored in native-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt64Ne"]
opaque setUInt64Ne {size} (bv : @& BytesRefMut σ size UInt64.alignment) (i : USize) (h : i + 7 < size) (value : UInt64) : ST σ Unit

/--
Write to a `UInt64` stored in little-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt64Le"]
opaque setUInt64Le {size} (bv : @& BytesRefMut σ size UInt64.alignment) (i : USize) (h : i + 7 < size) (value : UInt64) : ST σ Unit

/--
Write to a `UInt64` stored in big-endian order.
**Panics** when used in multithreaded context or if the `ByteRef` was marked persistent.
-/
@[extern "lean_pod_BytesRef_setUInt64Be"]
opaque setUInt64Be {size} (bv : @& BytesRefMut σ size UInt64.alignment) (i : USize) (h : i + 7 < size) (value : UInt64) : ST σ Unit

end Pod.BytesRef
