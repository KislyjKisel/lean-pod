import Pod.Storable
import Pod.BytesRef

namespace Pod

class WriteBytes (α : Type) extends Storable α where
  writeBytesRefOffUnal {σ size align} : BytesRefMut σ size align → (i : USize) →
    i.toNat + byteSize.toNat ≤ size.toNat → α → ST σ Unit

  writeBytesRefUnal {σ align} (br : BytesRefMut σ byteSize align) : α → ST σ Unit :=
    writeBytesRefOffUnal br 0 (Nat.le_of_eq $ Nat.zero_add _)

  writeBytesRefOffElUnal {σ size align} (br : BytesRefMut σ size align) (i : USize)
    (h : i.toNat * byteSize.toNat + byteSize.toNat ≤ size.toNat) : α → ST σ Unit :=
      writeBytesRefOffUnal br (i * byteSize) (by rw [offEl_no_overflow i h]; exact h)

  writeBytesRefOff {σ size align} : BytesRefMut σ size align → (i : USize) →
    i.toNat + byteSize.toNat ≤ size.toNat →
    (∀ m, ∃ n, align * m + i.toNat = alignment * n) → α → ST σ Unit

  writeBytesRef {σ} (br : BytesRefMut σ byteSize alignment) : α → ST σ Unit :=
    writeBytesRefOff br 0 (Nat.le_of_eq $ Nat.zero_add _) λ m ↦
      Exists.intro m (by rw [Nat.add_comm]; exact Nat.zero_add _)

  writeBytesRefOffEl {σ size} (br : BytesRefMut σ size alignment) (i : USize)
    (h : i.toNat * byteSize.toNat + byteSize.toNat ≤ size.toNat) : α → ST σ Unit :=
      writeBytesRefOff br (i * byteSize) (by rw [offEl_no_overflow i h]; exact h) (offEl_aligned i h)

def BytesRef.setUnal {α σ align} [WriteBytes α] (br : BytesRefMut σ (byteSize α) align) (value : α) : ST σ Unit :=
  WriteBytes.writeBytesRefUnal br value

def BytesRef.usetOffUnal {α σ size align} [WriteBytes α] (br : BytesRefMut σ size align) (i : USize)
  (h₁ : i.toNat + (byteSize α).toNat ≤ size.toNat) (value : α) : ST σ Unit :=
    WriteBytes.writeBytesRefOffUnal br i h₁ value

def BytesRef.setOffUnal {α σ size align} [WriteBytes α] (br : BytesRefMut σ size align) (i : Nat)
  (h₁ : i + (byteSize α).toNat ≤ size.toNat) (value : α) : ST σ Unit :=
    WriteBytes.writeBytesRefOffUnal br ⟨i, off_lt_usize_size i h₁⟩ h₁ value

def BytesRef.usetOffElUnal {α σ size align} [WriteBytes α] (br : BytesRefMut σ size align)
  (i : USize) (h : i.toNat * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) (value : α) : ST σ Unit :=
    WriteBytes.writeBytesRefOffElUnal br i h value

def BytesRef.setOffElUnal {α σ size align} [WriteBytes α] (br : BytesRefMut σ size align)
  (i : Nat) (h : i * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) (value : α) : ST σ Unit :=
    WriteBytes.writeBytesRefOffElUnal br ⟨i, offEl_lt_usize_size i h⟩ h value

def BytesRef.set {α σ} [WriteBytes α] (br : BytesRefMut σ (byteSize α) (alignment α)) (value : α) : ST σ Unit :=
  WriteBytes.writeBytesRef br value

def BytesRef.usetOff {α σ size align} [WriteBytes α] (br : BytesRefMut σ size align) (i : USize)
  (h₁ : i.toNat + (byteSize α).toNat ≤ size.toNat)
  (h₂ : ∀ m, ∃ n, align * m + i.toNat = alignment α * n) (value : α) : ST σ Unit :=
    WriteBytes.writeBytesRefOff br i h₁ h₂ value

def BytesRef.setOff {α σ size align} [WriteBytes α] (br : BytesRefMut σ size align) (i : Nat)
  (h₁ : i + (byteSize α).toNat ≤ size.toNat)
  (h₂ : ∀ m, ∃ n, align * m + i = alignment α * n) (value : α) : ST σ Unit :=
    WriteBytes.writeBytesRefOff br ⟨i, off_lt_usize_size i h₁⟩ h₁ h₂ value

def BytesRef.usetOffEl {α σ size} [WriteBytes α] (br : BytesRefMut σ size (alignment α))
  (i : USize) (h : i.toNat * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) (value : α) : ST σ Unit :=
    WriteBytes.writeBytesRefOffEl br i h value

def BytesRef.setOffEl {α σ size} [WriteBytes α] (br : BytesRefMut σ size (alignment α))
  (i : Nat) (h : i * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) (value : α) : ST σ Unit :=
    WriteBytes.writeBytesRefOffEl br ⟨i, offEl_lt_usize_size i h⟩ h value
