import Pod.Lemmas
import Pod.Util

opaque BytesViewPointed (size : USize) : NonemptyType
def BytesView (size : USize) : Type := (BytesViewPointed size).type
instance {size} : Nonempty (BytesView size) := (BytesViewPointed size).property

namespace BytesView

@[extern "lean_pod_BytesView_take"]
opaque take {size} (bv : @& BytesView size) (count : USize) (h : count ≤ size) : BytesView count

@[extern "lean_pod_BytesView_drop"]
opaque drop {size} (bv : BytesView size) (count : USize) (h : count ≤ size) : BytesView (size - count)

@[extern "lean_pod_BytesView_slice"]
opaque BytesView.slice {size}
  (bv : BytesView size) (start : USize) (length : USize)
  (bounded : start.toNat + length.toNat ≤ size.toNat) : BytesView length :=
  let «start≤size» : start ≤ size := by
    apply Nat.le_trans $ Nat.le_sub_of_add_le bounded
    exact Nat.sub_le size.toNat length.toNat
  (bv.drop start «start≤size»).take length $ by
    show length.val ≤ (size.val - start.val).val
    rw [Fin.toNat_sub_distrib size.val start.val «start≤size»]
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    exact bounded

@[extern "lean_pod_BytesView_getUInt8"]
opaque getUInt8 {size} (bv : @& BytesView size) (i : USize) (h : i < size) : UInt8

@[extern "lean_pod_BytesView_getUInt16Ne"]
opaque getUInt16Ne {size} (bv : @& BytesView size) (i : USize) (h : i + 1 < size) : UInt16

@[extern "lean_pod_BytesView_getUInt16Le"]
opaque getUInt16Le {size} (bv : @& BytesView size) (i : USize) (h : i + 1 < size) : UInt16

@[extern "lean_pod_BytesView_getUInt16Be"]
opaque getUInt16Be {size} (bv : @& BytesView size) (i : USize) (h : i + 1 < size) : UInt16

@[extern "lean_pod_BytesView_getUInt32Ne"]
opaque getUInt32Ne {size} (bv : @& BytesView size) (i : USize) (h : i + 3 < size) : UInt32

@[extern "lean_pod_BytesView_getUInt32Le"]
opaque getUInt32Le {size} (bv : @& BytesView size) (i : USize) (h : i + 3 < size) : UInt32

@[extern "lean_pod_BytesView_getUInt32Be"]
opaque getUInt32Be {size} (bv : @& BytesView size) (i : USize) (h : i + 3 < size) : UInt32

@[extern "lean_pod_BytesView_getUInt64Ne"]
opaque getUInt64Ne {size} (bv : @& BytesView size) (i : USize) (h : i + 7 < size) : UInt64

@[extern "lean_pod_BytesView_getUInt64Le"]
opaque getUInt64Le {size} (bv : @& BytesView size) (i : USize) (h : i + 7 < size) : UInt64

@[extern "lean_pod_BytesView_getUInt64Be"]
opaque getUInt64Be {size} (bv : @& BytesView size) (i : USize) (h : i + 7 < size) : UInt64

def getUInt8? {size} (bv : BytesView size) (i : USize) : Option UInt8 := mb? $ bv.getUInt8 i
def getUInt16Ne? {size} (bv : BytesView size) (i : USize) : Option UInt16 := mb? $ bv.getUInt16Ne i
def getUInt16Le? {size} (bv : BytesView size) (i : USize) : Option UInt16 := mb? $ bv.getUInt16Le i
def getUInt16Be? {size} (bv : BytesView size) (i : USize) : Option UInt16 := mb? $ bv.getUInt16Be i
def getUInt32Ne? {size} (bv : BytesView size) (i : USize) : Option UInt32 := mb? $ bv.getUInt32Ne i
def getUInt32Le? {size} (bv : BytesView size) (i : USize) : Option UInt32 := mb? $ bv.getUInt32Le i
def getUInt32Be? {size} (bv : BytesView size) (i : USize) : Option UInt32 := mb? $ bv.getUInt32Be i
def getUInt64Ne? {size} (bv : BytesView size) (i : USize) : Option UInt64 := mb? $ bv.getUInt64Ne i
def getUInt64Le? {size} (bv : BytesView size) (i : USize) : Option UInt64 := mb? $ bv.getUInt64Le i
def getUInt64Be? {size} (bv : BytesView size) (i : USize) : Option UInt64 := mb? $ bv.getUInt64Be i

private
abbrev mkGet! := @mb! "Index out of bounds"

def getUInt8! {size} (bv : BytesView size) (i : USize) : UInt8 := mkGet! $ bv.getUInt8 i
def getUInt16Ne! {size} (bv : BytesView size) (i : USize) : UInt16 := mkGet! $ bv.getUInt16Ne i
def getUInt16Le! {size} (bv : BytesView size) (i : USize) : UInt16 := mkGet! $ bv.getUInt16Le i
def getUInt16Be! {size} (bv : BytesView size) (i : USize) : UInt16 := mkGet! $ bv.getUInt16Be i
def getUInt32Ne! {size} (bv : BytesView size) (i : USize) : UInt32 := mkGet! $ bv.getUInt32Ne i
def getUInt32Le! {size} (bv : BytesView size) (i : USize) : UInt32 := mkGet! $ bv.getUInt32Le i
def getUInt32Be! {size} (bv : BytesView size) (i : USize) : UInt32 := mkGet! $ bv.getUInt32Be i
def getUInt64Ne! {size} (bv : BytesView size) (i : USize) : UInt64 := mkGet! $ bv.getUInt64Ne i
def getUInt64Le! {size} (bv : BytesView size) (i : USize) : UInt64 := mkGet! $ bv.getUInt64Le i
def getUInt64Be! {size} (bv : BytesView size) (i : USize) : UInt64 := mkGet! $ bv.getUInt64Be i

end BytesView

instance {size} : GetElem (BytesView size) USize UInt8 λ _ i ↦ i < size where
  getElem := BytesView.getUInt8

instance {size} : GetElem (BytesView size) Nat UInt8 λ _ i ↦ i < size.toNat where
  getElem := λ bp i h ↦ bp.getUInt8 i.toUSize $ by
    show i % USize.size < size.toNat
    rw [Nat.mod_eq_of_lt $ Nat.lt_trans h size.val.isLt]
    apply Nat.lt_of_lt_of_eq
    · exact h
    · rfl

instance {size} : GetElem (BytesView size) (Fin size.toNat) UInt8 λ _ _ ↦ True where
  getElem := λ bp i _ ↦ bp[i.val]'i.isLt