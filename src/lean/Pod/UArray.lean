import Pod.Storable
import Pod.ReadBytes
import Pod.WriteBytes

set_option autoImplicit false

namespace Pod

variable {α : Type} [ReadBytes α] [WriteBytes α]

/-- Dynamic array with elements stored unboxed. -/
structure UArray (α : Type) [ReadBytes α] [WriteBytes α] where
  data : List α

attribute [extern "lean_pod_UArray_mk"] UArray.mk
attribute [extern "lean_pod_UArray_data"] UArray.data

namespace UArray

@[extern "lean_pod_UArray_mkEmpty"]
def mkEmpty (c : @& Nat) : UArray α := .mk []

def empty : UArray α := mkEmpty 0

instance : Inhabited (UArray α) := ⟨empty⟩

@[extern "lean_pod_UArray_replicate"]
def replicate (n : Nat) (v : α) : UArray α := .mk (List.replicate n v)

def singleton (v : α) : UArray α := replicate 1 v

@[extern "lean_pod_UArray_toArray"]
def toArray (a : UArray α) : Array α := a.data.toArray

@[extern "lean_pod_UArray_ofArray"]
def ofArray (a : Array α) : UArray α := .mk a.data

@[reducible, extern "lean_pod_UArray_size"]
def size (a : @& UArray α) : Nat := a.data.length

def isEmpty (a : UArray α) : Bool := a.size = 0

@[extern "lean_pod_UArray_view"]
opaque view (a : UArray α) : BytesView (a.size.toUSize * byteSize α) (alignment α)

@[extern "lean_pod_UArray_get"]
def get (a : @& UArray α) (i : @& Fin a.size) : α := a.data.get i

instance : GetElem (UArray α) Nat α (λ a i ↦ i < a.size) where
  getElem a i h := a.get (Fin.mk i h)

@[inline]
abbrev getD (a : UArray α) (i : Nat) (v₀ : α) : α :=
  if h: i < a.size then a.get (Fin.mk i h) else v₀

@[extern "lean_pod_UArray_get_or_panic"]
def get! [Inhabited α] (a : @& UArray α) (i : @& Nat) : α := a.getD i default

@[extern "lean_pod_UArray_push"]
def push (a : UArray α) (v : α) : UArray α := .mk (a.data.concat v)

@[extern "lean_pod_UArray_set"]
def set (a : UArray α) (i : @& Fin a.size) (v : α) : UArray α := .mk (a.data.set i v)

@[inline]
def setD (a : UArray α) (i : Nat) (v : α) : UArray α :=
  if h: i < a.size then a.set (Fin.mk i h) v else a

@[extern "lean_pod_UArray_set_or_panic"]
def set! (a : UArray α) (i : @& Nat) (v : α) : UArray α := a.setD i v

@[extern "lean_pod_UArray_uget"]
def uget (a : @& UArray α) (i : USize) (h : i.toNat < a.size) : α := a.get (Fin.mk i.toNat h)

instance : GetElem (UArray α) USize α (λ a i ↦ i.toNat < a.size) where
  getElem a i h := a.uget i h

def get? (a : UArray α) (i : Nat) : Option α :=
  if h: i < a.size then some (a.get (Fin.mk i h)) else none

def back! [Inhabited α] (a : UArray α) : α := a.get! (a.size - 1)

def back? (a : UArray α) : Option α := a.get? (a.size - 1)

@[simp] theorem size_set (a : UArray α) (i : Fin a.size) (v : α) : (set a i v).size = a.size :=
  List.length_set ..

@[simp] theorem size_push (a : UArray α) (v : α) : (push a v).size = a.size + 1 :=
  List.length_concat ..

@[extern "lean_pod_UArray_uset"]
def uset (a : UArray α) (i : USize) (v : α) (h : i.toNat < a.size) : UArray α := a.set (Fin.mk i.toNat h) v

@[extern "lean_pod_UArray_swap"]
def swap (a : UArray α) (i j : @& Fin a.size) : UArray α :=
  let v₁ := a.get i
  let v₂ := a.get i
  let a' := a.set i v₂
  a'.set (size_set a i v₂ ▸ j) v₁

@[extern "lean_pod_UArray_swap_or_panic"]
def swap! (a : UArray α) (i j : @& Nat) : UArray α :=
  if h₁ : i < a.size
    then
      if h₂ : j < a.size
        then swap a (Fin.mk i h₁) (Fin.mk j h₂)
        else panic! "index out of bounds"
    else panic! "index out of bounds"



end UArray
