import Pod.Meta
import Pod.Fixnum

variable {α : Type _}

namespace Pod

private
define_foreign_type FixnumSlotMapImpl.{u} (idxW : Nat) (genW : Nat) (α : Type u) : Type u

/--
Sparse slot map with `UFixnum` keys.
Each key is a combination of two integers with bit widths `idxW` and `genW`.
One specifies maximum number of stored values (`2^idxW`), the other - maximum number of generations per value (`2^genW`).
For keys to be stored as `UFixnum`, `idxW + genW ≤ UFixnum.bitWidth` must be true.
-/
abbrev FixnumSlotMap (i g : Nat) (α : Type _) :=
  { _data : FixnumSlotMapImpl i g α // i + g ≤ UFixnum.bitWidth }

namespace FixnumSlotMap

@[extern "lean_pod_FixnumSlotMap_mk"] private
opaque mkImpl {idxW genW : @& Nat} (capacity : @& Nat) : FixnumSlotMapImpl idxW genW α

@[inline]
def mkEmpty (capacity idxW genW : Nat)
  (h : idxW + genW ≤ UFixnum.bitWidth := by apply Nat.lt_of_lt_of_le _ Pod.UFixnum.bitWidth_ge; decide) :
    FixnumSlotMap idxW genW α :=
      ⟨mkImpl capacity, h⟩

@[inline]
def empty (idxW genW : Nat)
  (h : idxW + genW ≤ UFixnum.bitWidth := by apply Nat.lt_of_lt_of_le _ Pod.UFixnum.bitWidth_ge; decide) :
  FixnumSlotMap idxW genW α :=
    mkEmpty 0 idxW genW h

@[extern "lean_pod_FixnumSlotMap_size"]
opaque size {idxW genW : @& Nat} (data : @& FixnumSlotMap idxW genW α) : Fin (2 ^ idxW) :=
  ⟨0, Nat.pow_pos (by decide)⟩

@[inline]
def isEmpty {idxW genW} (data : FixnumSlotMap idxW genW α) : Bool :=
  data.size.1 == 0

/--
The key that will be used on the next insertion operation, given the data will remain unchanged.
-/
@[extern "lean_pod_FixnumSlotMap_top"]
opaque top {idxW genW : @& Nat} (data : @& FixnumSlotMap idxW genW α) : UFixnum

@[extern "lean_pod_FixnumSlotMap_isValid"]
opaque isValid {idxW genW : @& Nat} (data : @& FixnumSlotMap idxW genW α) (key : @& UFixnum) : Bool

@[extern "lean_pod_FixnumSlotMap_firstValid"]
opaque firstValid' {idxW genW : @& Nat} (data : @& FixnumSlotMap idxW genW α) :
  { k : UFixnum // k = UFixnum.maximum ∨ data.isValid k } :=
    ⟨UFixnum.maximum, .inl rfl⟩

@[inline]
def firstValid {idxW genW} (data : FixnumSlotMap idxW genW α) : Option { k : UFixnum // data.isValid k } :=
  let key' := data.firstValid'
  if h: key' = UFixnum.maximum
    then none
    else some ⟨key'.1, Or.elim key'.2 (λ h' ↦ (h h').elim) id⟩

@[extern "lean_pod_FixnumSlotMap_nextValid"]
opaque nextValid' {idxW genW : @& Nat} (data : @& FixnumSlotMap idxW genW α) (key : @& UFixnum) :
  { k : UFixnum // k = 0 ∨ data.isValid k } :=
    ⟨0, .inl rfl⟩

@[inline]
def nextValid {idxW genW} (data : FixnumSlotMap idxW genW α) (key : UFixnum) : Option { k : UFixnum // data.isValid k } :=
  let key' := data.nextValid' key
  if h: key'.1 = 0
    then none
    else some ⟨key'.1, Or.elim key'.2 (λ h' ↦ (h h').elim) id⟩

@[extern "lean_pod_FixnumSlotMap_insert"]
opaque insert' {idxW genW : @& Nat} (data : FixnumSlotMap idxW genW α) (value : α) : FixnumSlotMap idxW genW α :=
  data

@[inline]
def insert {idxW genW} (data : FixnumSlotMap idxW genW α) (value : α) : UFixnum × FixnumSlotMap idxW genW α :=
  let key := data.top
  (key, data.insert' value)

@[extern "lean_pod_FixnumSlotMap_erase"]
opaque erase' {idxW genW : @& Nat}
  (data : FixnumSlotMap idxW genW α) (key : @& UFixnum) (h : isValid data key) :
    FixnumSlotMap idxW genW α :=
      data

@[inline]
def erase {idxW genW}
  (data : FixnumSlotMap idxW genW α) (key : @& UFixnum) : FixnumSlotMap idxW genW α :=
    if h: data.isValid key
      then erase' data key h
      else data

@[extern "lean_pod_FixnumSlotMap_get"]
opaque get {idxW genW : @& Nat} [Nonempty α]
  (data : @& FixnumSlotMap idxW genW α) (key : @& UFixnum) (h : data.isValid key) : α

@[inline]
def get? {idxW genW} [Nonempty α]
  (data : @& FixnumSlotMap idxW genW α) (key : @& UFixnum) : Option α :=
    if h: data.isValid key
      then data.get key h
      else none

@[extern "lean_pod_FixnumSlotMap_set"]
opaque set {idxW genW : @& Nat}
  (data : FixnumSlotMap idxW genW α) (key : @& UFixnum) (h : data.isValid key) (value : α) :
    FixnumSlotMap idxW genW α :=
      data

def setD {idxW genW} (data : FixnumSlotMap idxW genW α) (key : @& UFixnum) (value : α) : FixnumSlotMap idxW genW α :=
  if h: data.isValid key
    then data.set key h value
    else data

private unsafe
def modifyMImpl
  {idxW genW m} [Monad m]
  (data : FixnumSlotMap idxW genW α) (key : @& UFixnum)
  (h : data.isValid key) (f : α → m α) : m (FixnumSlotMap idxW genW α) := do
    let x := @get _ _ _ lcProof data key h
    let data := data.set key h (unsafeCast ())
    let x ← f x
    pure <| data.set key lcProof x

@[implemented_by modifyMImpl]
opaque modifyM
  {idxW genW m} [Monad m]
  (data : FixnumSlotMap idxW genW α) (key : @& UFixnum)
  (h : data.isValid key) (f : α → m α) : m (FixnumSlotMap idxW genW α) :=
    pure data

@[inline]
def modify
  {idxW genW}
  (data : FixnumSlotMap idxW genW α) (key : @& UFixnum)
  (h : data.isValid key) (f : α → α) : FixnumSlotMap idxW genW α :=
    Id.run <| data.modifyM key h f

end FixnumSlotMap
