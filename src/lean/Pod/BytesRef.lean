import Pod.Lemmas
import Pod.UInt

namespace Pod

inductive Mutability where
  | Mutable
  -- can't mutate by itself, but content can be mutated through other ptrs
  | Immutable

variable {σ : Type}

opaque BytesRefPointed (σ : Type) (mutab : Mutability) (size : USize) (align : Nat) : NonemptyType
def BytesRef (σ : Type) (mutab : Mutability) (size : USize) (align : Nat) : Type := (BytesRefPointed σ mutab size align).type
instance {σ mutab size align} : Nonempty (BytesRef σ mutab size align) := (BytesRefPointed σ mutab size align).property

abbrev BytesRefMut (σ : Type) := BytesRef σ .Mutable
abbrev BytesRefImm (σ : Type) := BytesRef σ .Immutable

/-- Clones array if it is shared. -/
@[extern "lean_pod_ByteArray_withRef"]
opaque _root_.ByteArray.withRef (ba : ByteArray) (f : ∀{σ}, BytesRefMut σ ba.size.toUSize 1 → ST σ Unit) : ByteArray

/-- Clones array if it is shared. -/
@[extern "lean_pod_ByteArray_withRefEx"]
opaque _root_.ByteArray.withRefEx (ba : ByteArray) (f : ∀{σ}, BytesRefMut σ ba.size.toUSize 1 → EST ε σ Unit) : Except ε ByteArray

namespace BytesRef

@[extern "lean_pod_BytesRef_weaken"]
opaque weaken {mutab size} {align0 align1 : @& Nat} (h : ∃ k, align1 * k = align0) :
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
-/
@[extern "lean_pod_BytesRef_toByteArray"]
opaque toByteArray {mutab size} {align : @& Nat} (bv : @& BytesRef σ mutab size align) : ST σ ByteArray

end Pod.BytesRef
