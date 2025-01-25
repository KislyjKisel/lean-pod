import Pod.Meta
import Pod.Initialization
import Pod.Lemmas
import Pod.UInt
import Pod.BytesView

namespace Pod

inductive Mutability where
  | Mutable
  /-- The referenced data can still be mutated through other references -/
  | Immutable

variable {σ : Type}

define_foreign_type BytesRef (σ : Type) (mutab : Mutability) (size align : Nat)

abbrev BytesRefMut (σ : Type) := BytesRef σ .Mutable
abbrev BytesRefImm (σ : Type) := BytesRef σ .Immutable

/-- Clones array if it is shared. -/
@[extern "lean_pod_ByteArray_withRef"]
opaque _root_.ByteArray.withRef
  {σ α} {m : Type → Type → Type} [Nonempty (m σ (α × ByteArray))] [@& Functor (m σ)]
  (ba : ByteArray) (f : ∀{σ}, BytesRefMut σ ba.size 1 → m σ α) : m σ (α × ByteArray)

@[extern "lean_pod_ByteArray_withRefImm"]
opaque _root_.ByteArray.withRefImm
  {σ α} {m : Type → Type → Type} [Nonempty (m σ α)]
  (ba : @& ByteArray) (f : ∀{σ}, BytesRefImm σ ba.size 1 → m σ α) : m σ α

@[extern "lean_pod_BytesView_asRef"]
opaque BytesView.asRef
  {σ α} {m : Type → Type → Type} [Nonempty (m σ α)]
  {sz align : @& Nat} (bv : @& BytesView sz align) (f : ∀{σ}, BytesRefImm σ sz align → m σ α) : m σ α

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

@[extern "lean_pod_BytesRef_copy"]
opaque copy {mutab} {size a1 a2 : @& Nat} (dst : @& BytesRefMut σ size a1) (src : @& BytesRef σ mutab size a2) : ST σ Unit

end Pod.BytesRef
