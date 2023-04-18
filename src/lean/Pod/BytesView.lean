import Pod.Lemmas
import Pod.Util
import Pod.UInt

namespace Pod

opaque BytesViewPointed (size : USize) (alignment : Nat) : NonemptyType
def BytesView (size : USize) (alignment : Nat) : Type := (BytesViewPointed size alignment).type
instance {size alignment} : Nonempty (BytesView size alignment) := (BytesViewPointed size alignment).property

@[extern "lean_pod_ByteArray_view"]
opaque _root_.ByteArray.view (ba : ByteArray) : BytesView ba.size.toUSize 1

namespace BytesView

@[extern "lean_pod_BytesView_weaken"]
opaque weaken {size} {alignment0 alignment1 : @& Nat} (h : alignment1 ≤ alignment0) : BytesView size alignment0 → BytesView size alignment1

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

@[extern "lean_pod_BytesView_getUInt8"]
opaque getUInt8 {size} {alignment : @& Nat} (bv : @& BytesView size alignment) (i : USize) (h : i < size) : UInt8

@[extern "lean_pod_BytesView_getUInt16Ne"]
opaque getUInt16Ne {size} (bv : @& BytesView size UInt16.alignment) (i : USize) (h : i + 1 < size) : UInt16

@[extern "lean_pod_BytesView_getUInt16Le"]
opaque getUInt16Le {size} (bv : @& BytesView size UInt16.alignment) (i : USize) (h : i + 1 < size) : UInt16

@[extern "lean_pod_BytesView_getUInt16Be"]
opaque getUInt16Be {size} (bv : @& BytesView size UInt16.alignment) (i : USize) (h : i + 1 < size) : UInt16

@[extern "lean_pod_BytesView_getUInt32Ne"]
opaque getUInt32Ne {size} (bv : @& BytesView size UInt32.alignment) (i : USize) (h : i + 3 < size) : UInt32

@[extern "lean_pod_BytesView_getUInt32Le"]
opaque getUInt32Le {size} (bv : @& BytesView size UInt32.alignment) (i : USize) (h : i + 3 < size) : UInt32

@[extern "lean_pod_BytesView_getUInt32Be"]
opaque getUInt32Be {size} (bv : @& BytesView size UInt32.alignment) (i : USize) (h : i + 3 < size) : UInt32

@[extern "lean_pod_BytesView_getUInt64Ne"]
opaque getUInt64Ne {size} (bv : @& BytesView size UInt64.alignment) (i : USize) (h : i + 7 < size) : UInt64

@[extern "lean_pod_BytesView_getUInt64Le"]
opaque getUInt64Le {size} (bv : @& BytesView size UInt64.alignment) (i : USize) (h : i + 7 < size) : UInt64

@[extern "lean_pod_BytesView_getUInt64Be"]
opaque getUInt64Be {size} (bv : @& BytesView size UInt64.alignment) (i : USize) (h : i + 7 < size) : UInt64

@[extern "lean_pod_BytesView_getUSizeNe"]
opaque getUSizeNe {size} (bv : @& BytesView size USize.alignment) (i : USize)
  (h : i + (USize.byteWidth - 1).toUSize < size) : USize

def getUInt8? {size alignment} (bv : BytesView size alignment) (i : USize) : Option UInt8 := mb? $ bv.getUInt8 i
def getUInt16Ne? {size} (bv : BytesView size UInt16.alignment) (i : USize) : Option UInt16 := mb? $ bv.getUInt16Ne i
def getUInt16Le? {size} (bv : BytesView size UInt16.alignment) (i : USize) : Option UInt16 := mb? $ bv.getUInt16Le i
def getUInt16Be? {size} (bv : BytesView size UInt16.alignment) (i : USize) : Option UInt16 := mb? $ bv.getUInt16Be i
def getUInt32Ne? {size} (bv : BytesView size UInt32.alignment) (i : USize) : Option UInt32 := mb? $ bv.getUInt32Ne i
def getUInt32Le? {size} (bv : BytesView size UInt32.alignment) (i : USize) : Option UInt32 := mb? $ bv.getUInt32Le i
def getUInt32Be? {size} (bv : BytesView size UInt32.alignment) (i : USize) : Option UInt32 := mb? $ bv.getUInt32Be i
def getUInt64Ne? {size} (bv : BytesView size UInt64.alignment) (i : USize) : Option UInt64 := mb? $ bv.getUInt64Ne i
def getUInt64Le? {size} (bv : BytesView size UInt64.alignment) (i : USize) : Option UInt64 := mb? $ bv.getUInt64Le i
def getUInt64Be? {size} (bv : BytesView size UInt64.alignment) (i : USize) : Option UInt64 := mb? $ bv.getUInt64Be i
-- def getUSizeNe? {size} (bv : BytesView size USize.alignment) (i : USize) : Option USize :=
--   if h : 1 + (USize.byteWidth - 1).toUSize < size then some $ bv.getUSizeNe i h else none

private
abbrev mkGet! := @mb! "Index out of bounds"

def getUInt8! {size alignment} (bv : BytesView size alignment) (i : USize) : UInt8 := mkGet! $ bv.getUInt8 i
def getUInt16Ne! {size} (bv : BytesView size UInt16.alignment) (i : USize) : UInt16 := mkGet! $ bv.getUInt16Ne i
def getUInt16Le! {size} (bv : BytesView size UInt16.alignment) (i : USize) : UInt16 := mkGet! $ bv.getUInt16Le i
def getUInt16Be! {size} (bv : BytesView size UInt16.alignment) (i : USize) : UInt16 := mkGet! $ bv.getUInt16Be i
def getUInt32Ne! {size} (bv : BytesView size UInt32.alignment) (i : USize) : UInt32 := mkGet! $ bv.getUInt32Ne i
def getUInt32Le! {size} (bv : BytesView size UInt32.alignment) (i : USize) : UInt32 := mkGet! $ bv.getUInt32Le i
def getUInt32Be! {size} (bv : BytesView size UInt32.alignment) (i : USize) : UInt32 := mkGet! $ bv.getUInt32Be i
def getUInt64Ne! {size} (bv : BytesView size UInt64.alignment) (i : USize) : UInt64 := mkGet! $ bv.getUInt64Ne i
def getUInt64Le! {size} (bv : BytesView size UInt64.alignment) (i : USize) : UInt64 := mkGet! $ bv.getUInt64Le i
def getUInt64Be! {size} (bv : BytesView size UInt64.alignment) (i : USize) : UInt64 := mkGet! $ bv.getUInt64Be i
-- def getUSizeNe! {size} (bv : BytesView size USize.alignment) (i : USize) : USize := sorry

end BytesView

end Pod

instance {size alignment} : GetElem (Pod.BytesView size alignment) USize UInt8 λ _ i ↦ i < size where
  getElem := Pod.BytesView.getUInt8

instance {size alignment} : GetElem (Pod.BytesView size alignment) Nat UInt8 λ _ i ↦ i < size.toNat where
  getElem := λ bp i h ↦ bp.getUInt8 i.toUSize $ by
    show i % USize.size < size.toNat
    rw [Nat.mod_eq_of_lt $ Nat.lt_trans h size.val.isLt]
    apply Nat.lt_of_lt_of_eq
    · exact h
    · rfl

instance {size alignment} : GetElem (Pod.BytesView size alignment) (Fin size.toNat) UInt8 λ _ _ ↦ True where
  getElem := λ bp i _ ↦ bp[i.val]'i.isLt
