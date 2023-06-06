import Pod.Lemmas
import Pod.UInt
import Pod.BytesView

namespace Pod

inductive Mutability where
  | Mutable
  /-- The referenced data can still be mutated through other references -/
  | Immutable

variable {σ : Type}

opaque BytesRefPointed (σ : Type) (mutab : Mutability) (size align : Nat) : NonemptyType
def BytesRef (σ : Type) (mutab : Mutability) (size align : Nat) : Type := (BytesRefPointed σ mutab size align).type
instance {σ mutab size align} : Nonempty (BytesRef σ mutab size align) := (BytesRefPointed σ mutab size align).property

abbrev BytesRefMut (σ : Type) := BytesRef σ .Mutable
abbrev BytesRefImm (σ : Type) := BytesRef σ .Immutable

/-- Clones array if it is shared. -/
@[extern "lean_pod_ByteArray_withRef"]
opaque _root_.ByteArray.withRef (ba : ByteArray) (f : ∀{σ}, BytesRefMut σ ba.size 1 → ST σ Unit) : ByteArray

/-- Clones array if it is shared. -/
@[extern "lean_pod_ByteArray_withRefEx"]
opaque _root_.ByteArray.withRefEx (ba : ByteArray) (f : ∀{σ}, BytesRefMut σ ba.size 1 → EST ε σ Unit) : Except ε ByteArray

namespace BytesRef

@[extern "lean_pod_BytesRef_weaken"]
opaque weaken {mutab} {size align0 align1 : @& Nat} (h : ∃ k, align1 * k = align0) :
  BytesRef σ mutab size align0 → BytesRef σ mutab size align1

@[extern "lean_pod_BytesRef_imm"]
opaque imm {mutab} {size align : @& Nat} : BytesRef σ mutab size align → BytesRefImm σ size align

@[extern "lean_pod_BytesRef_take"]
opaque take {mutab} {size align : @& Nat} (bv : BytesRef σ mutab size align)
  (count : @& Nat) (h : count ≤ size) : BytesRef σ mutab count align

@[extern "lean_pod_BytesRef_drop"]
opaque drop {mutab size} {align : @& Nat} (bv : BytesRef σ mutab size align)
  (count : @& Nat) (h : count ≤ size) : BytesRef σ mutab (size - count) (align.gcd count)

@[extern "lean_pod_BytesRef_slice"]
opaque slice {mutab} {size align : @& Nat} (bv : BytesRef σ mutab size align) (start length : @& Nat)
  (bounded : start + length ≤ size) : BytesRef σ mutab length (align.gcd start) := by
    apply (bv.drop start _).take length 
    · apply Nat.le_sub_of_add_le
      rw [Nat.add_comm]
      exact bounded
    · apply Nat.le_trans $ Nat.le_sub_of_add_le bounded
      exact Nat.sub_le size length

/--
Read all bytes into a `ByteArray`.
-/
@[extern "lean_pod_BytesRef_toByteArray"]
opaque toByteArray {mutab} {size align : @& Nat} (bv : @& BytesRef σ mutab size align) : ST σ ByteArray

@[extern "lean_pod_BytesRef_copyView"]
opaque copyView {size a1 a2 : @& Nat} (dst : @& BytesRefMut σ size a1) (src : @& BytesView size a2) : ST σ Unit

end Pod.BytesRef
