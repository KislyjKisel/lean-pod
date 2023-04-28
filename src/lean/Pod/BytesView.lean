import Pod.Lemmas
import Pod.UInt

namespace Pod

opaque BytesViewPointed (size : USize) (alignment : Nat) : NonemptyType
def BytesView (size : USize) (alignment : Nat) : Type := (BytesViewPointed size alignment).type
instance {size alignment} : Nonempty (BytesView size alignment) := (BytesViewPointed size alignment).property

@[extern "lean_pod_ByteArray_view"]
opaque _root_.ByteArray.view (ba : ByteArray) : BytesView ba.size.toUSize 1

namespace BytesView

@[extern "lean_pod_BytesView_weaken"]
opaque weaken {size} {alignment0 alignment1 : @& Nat} (h : ∃ k, alignment1 * k = alignment0) : BytesView size alignment0 → BytesView size alignment1

@[extern "lean_pod_BytesView_take"]
opaque take {size} {alignment : @& Nat} (bv : BytesView size alignment) (count : USize) (h : count ≤ size) : BytesView count alignment

@[extern "lean_pod_BytesView_drop"]
opaque drop {size} {alignment : @& Nat} (bv : BytesView size alignment) (count : USize) (h : count ≤ size) : BytesView (size - count) (alignment.gcd count.toNat)

@[extern "lean_pod_BytesView_slice"]
opaque slice {size} {alignment : @& Nat}
  (bv : BytesView size alignment) (start length : USize)
  (bounded : start.toNat + length.toNat ≤ size.toNat) : BytesView length (alignment.gcd start.toNat) :=
  let «start≤size» : start ≤ size := by
    apply Nat.le_trans $ Nat.le_sub_of_add_le bounded
    exact Nat.sub_le size.toNat length.toNat
  (bv.drop start «start≤size»).take length $ by
    show length.val ≤ (size.val - start.val).val
    rw [Fin.toNat_sub_distrib size.val start.val «start≤size»]
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    exact bounded

@[extern "lean_pod_BytesView_toByteArray"]
opaque toByteArray {size} {align : @& Nat} (bv : @& BytesView size align) : ByteArray

end BytesView

end Pod
