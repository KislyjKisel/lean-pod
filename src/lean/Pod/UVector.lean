import Pod.Storable
import Pod.ReadBytes
import Pod.WriteBytes

namespace Pod

variable {α : Type}

opaque UVectorPointed (α : Type) (size : Nat) : NonemptyType
/-- Static array with elements stored unboxed. -/
def UVector (α : Type) (size : Nat) : Type := (UVectorPointed α size).type
instance {α size} : Nonempty (UVector α size) := (UVectorPointed α size).property

namespace UVector

@[extern "lean_pod_UVector_replicate"]
opaque replicate {n : @& Nat} [@& WriteBytes α] (v : @& α) : UVector α n

def mk {n} [Inhabited α] [WriteBytes α] : UVector α n := replicate default

@[extern "lean_pod_UVector_raw"]
opaque raw {n : @& Nat} [@& Storable α] (uv : UVector α n) : Pod.BytesView (byteSizeArray α n) (alignment α)

@[extern "lean_pod_UVector_get"]
opaque get {n : @& Nat} [Nonempty α] [@& ReadBytes α] (a : @& UVector α n) (i : @& Fin n) : α

@[inline]
abbrev getD {n : @& Nat} [Nonempty α] [@& ReadBytes α] (a : UVector α n) (i : Nat) (v₀ : α) : α :=
  if h: i < n then a.get (Fin.mk i h) else v₀

@[extern "lean_pod_UVector_get_or_panic"]
def get! {n : @& Nat} [@& Inhabited α] [@& ReadBytes α] (a : @& UVector α n) (i : @& Nat) : α := a.getD i default

@[extern "lean_pod_UVector_set"]
opaque set {n : @& Nat} [@& WriteBytes α] (a : UVector α n) (i : @& Fin n) (v : α) : UVector α n

@[inline]
def setD {n} [WriteBytes α] (a : UVector α n) (i : Nat) (v : α) : UVector α n :=
  if h: i < n then a.set (Fin.mk i h) v else a

@[extern "lean_pod_UVector_set_or_panic"]
def set! {n : @& Nat} [@& WriteBytes α] (a : UVector α n) (i : @& Nat) (v : α) : UVector α n := a.setD i v

instance {n} [Nonempty α]  [ReadBytes α] : GetElem (UVector α n) Nat α (λ _ i ↦ i < n) where
  getElem a i h := a.get (Fin.mk i h)
