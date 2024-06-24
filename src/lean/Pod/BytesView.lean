import Pod.Meta
import Pod.Initialization
import Pod.Lemmas
import Pod.UInt

namespace Pod

/-- Pointer to immutable foreign memory. Keeps it alive. -/
define_foreign_type BytesView (size align : Nat)

@[extern "lean_pod_ByteArray_view"]
opaque _root_.ByteArray.view (ba : ByteArray) : BytesView ba.size 1

namespace BytesView

@[extern "lean_pod_BytesView_weaken"]
opaque weaken {size align0 align1 : @& Nat} (h : ∃ k, align1 * k = align0) :
  BytesView size align0 → BytesView size align1

@[extern "lean_pod_BytesView_take"]
opaque take {size align : @& Nat} (bv : BytesView size align) (count : @& Nat) (h : count ≤ size) :
  BytesView count align

@[extern "lean_pod_BytesView_drop"]
opaque drop {size align : @& Nat} (bv : BytesView size align) (count : @& Nat) (h : count ≤ size) :
  BytesView (size - count) (align.gcd count)

@[extern "lean_pod_BytesView_slice"]
opaque slice {size align : @& Nat}
  (bv : BytesView size align) (start length : @& Nat)
  (bounded : start + length ≤ size) : BytesView length (align.gcd start) := by
    apply (bv.drop start _).take length
    · apply Nat.le_sub_of_add_le
      rw [Nat.add_comm]
      exact bounded
    · apply Nat.le_trans $ Nat.le_sub_of_add_le bounded
      exact Nat.sub_le size length

@[extern "lean_pod_BytesView_toByteArray"]
opaque toByteArray {size align : @& Nat} (bv : @& BytesView size align) : ByteArray

end BytesView

end Pod
