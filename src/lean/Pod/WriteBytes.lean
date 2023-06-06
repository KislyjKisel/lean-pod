import Pod.Storable
import Pod.BytesRef

namespace Pod

class WriteBytes (α : Type) extends Storable α where
  writeBytesRefOffUnal {σ size align} : BytesRefMut σ size align → (i : Nat) → α →
    i + byteSize ≤ size → ST σ Unit

  writeBytesRefUnal {σ align} (br : BytesRefMut σ byteSize align) (value : α) : ST σ Unit :=
    writeBytesRefOffUnal br 0 value (Nat.le_of_eq $ Nat.zero_add _)

  writeBytesRefOffElUnal {σ size align} (br : BytesRefMut σ size align) (i : Nat) (value : α)
    (h : i * byteSize + byteSize ≤ size) : ST σ Unit :=
      writeBytesRefOffUnal br (i * byteSize) value h

  writeBytesRefOff {σ size align} : BytesRefMut σ size align → (i : Nat) → α →
    i + byteSize ≤ size →
    (∀ m, ∃ n, align * m + i = alignment * n) → ST σ Unit

  writeBytesRef {σ} (br : BytesRefMut σ byteSize alignment) (value : α) : ST σ Unit :=
    writeBytesRefOff br 0 value (Nat.le_of_eq $ Nat.zero_add _) λ m ↦
      Exists.intro m (by rw [Nat.add_comm]; exact Nat.zero_add _)

  writeBytesRefOffEl {σ size} (br : BytesRefMut σ size alignment) (i : Nat) (value : α)
    (h : i * byteSize + byteSize ≤ size) : ST σ Unit :=
      writeBytesRefOff br (i * byteSize) value h (offEl_aligned i)

def BytesRef.setUnal {α σ align} [WriteBytes α] (br : BytesRefMut σ (byteSize α) align) (value : α) : ST σ Unit :=
  WriteBytes.writeBytesRefUnal br value

def BytesRef.setOffUnal {α σ size align} [WriteBytes α]
  (br : BytesRefMut σ size align) (i : Nat) (value : α)
  (h₁ : i + (byteSize α) ≤ size) : ST σ Unit :=
    WriteBytes.writeBytesRefOffUnal br i value h₁

def BytesRef.setOffElUnal {α σ size align} [WriteBytes α]
  (br : BytesRefMut σ size align) (i : Nat) (value : α)
  (h : i * (byteSize α) + (byteSize α) ≤ size) : ST σ Unit :=
    WriteBytes.writeBytesRefOffElUnal br i value h

def BytesRef.set {α σ} [WriteBytes α] (br : BytesRefMut σ (byteSize α) (alignment α)) (value : α) : ST σ Unit :=
  WriteBytes.writeBytesRef br value

def BytesRef.setOff {α σ size align} [WriteBytes α]
  (br : BytesRefMut σ size align) (i : Nat) (value : α)
  (h₁ : i + (byteSize α) ≤ size)
  (h₂ : ∀ m, ∃ n, align * m + i = alignment α * n) : ST σ Unit :=
    WriteBytes.writeBytesRefOff br i value h₁ h₂

def BytesRef.setOffEl {α σ size} [WriteBytes α]
  (br : BytesRefMut σ size (alignment α)) (i : Nat) (value : α)
  (h : i * (byteSize α) + (byteSize α) ≤ size) : ST σ Unit :=
    WriteBytes.writeBytesRefOffEl br i value h
