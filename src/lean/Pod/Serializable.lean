import Pod.ReadBytes
import Pod.WriteBytes

namespace Pod

universe u

inductive DeserializationResult (size : Nat) (α : Type u) where
| ok (val : α) (offset : Nat) (h : offset ≤ size)
| error

def DeserializationResult.toOption {size α} :
  DeserializationResult size α → Option α
| .ok val _ _ => some val
| .error => none

def DeserializationResult.toExcept {size α} :
  DeserializationResult size α → Except Unit α
| .ok val _ _ => .ok val
| .error => .error ()

def DeserializationResult.toExcept' {size α} :
  DeserializationResult size α → Except Unit (α × Σ n, PLift $ n ≤ size)
| .ok val offset h => .ok (val, .mk offset $ .up h)
| .error => .error ()

instance {size} : Functor (DeserializationResult size) where
  map f
  | .ok val offset h => .ok (f val) offset h
  | .error => .error

structure DeserializationM (α : Type u) where
  run : ∀ {size}, BytesView size 1 → (offset : Nat) → offset ≤ size  → DeserializationResult size α

def DeserializationM.isEof : DeserializationM Bool :=
  .mk λ {size} _ offset h ↦ .ok (offset == size) offset h

instance : Monad DeserializationM where
  pure x := .mk λ _ o h ↦ .ok x o h
  map f x := .mk λ bv o h ↦ f <$> x.run bv o h
  bind x f := .mk λ bv o h ↦
    match x.run bv o h with
    | .ok x o h => (f x).run bv o h
    | .error => .error

instance : MonadExcept Unit DeserializationM where
  throw _ := .mk λ _ _ _ ↦ .error
  tryCatch x f := .mk λ bv offset h ↦
    match x.run bv offset h with
    | .ok val offset h => .ok val offset h
    | .error => (f ()).run bv offset h

class Serializable (α : Type u) where
  size : Sum Nat (α → Nat)
  size' : α → Nat := λ x ↦ match size with | .inl n => n | .inr f => f x
  serialize : ∀ {σ offset sz}, (val : α) → BytesRefMut σ sz 1 → offset + size' val ≤ sz → ST σ Unit
  deserialize : DeserializationM α

export Serializable (serialize)

def deserialize (α : Type u) [ser : Serializable α] : DeserializationM α :=
  ser.deserialize

instance [Storable α] [ReadBytes α] [WriteBytes α] : Serializable α where
  size := .inl (byteSize α)
  serialize := λ {_ offset _} val br h ↦ br.setOffUnal offset val h
  deserialize := .mk λ {size} bv offset _ ↦
    let n := byteSize α
    let i := offset + n
    if h: i ≤ size
      then .ok (bv.getOffUnal offset $ by have : i = offset + byteSize α := rfl; exact this ▸ h) i h
      else .error
