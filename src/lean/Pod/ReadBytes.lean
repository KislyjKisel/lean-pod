import Pod.Storable
import Pod.BytesRef
import Pod.BytesView

namespace Pod

class ReadBytes (α : Type) extends Storable α where
  readBytesRefOffUnal {σ size align} : BytesRefImm σ size align → (i : USize) →
    i.toNat + byteSize.toNat ≤ size.toNat → ST σ α

  readBytesRefUnal {σ align} (br : BytesRefImm σ byteSize align) : ST σ α :=
    readBytesRefOffUnal br 0 (Nat.le_of_eq $ Nat.zero_add _)

  readBytesRefOffElUnal {σ size align} (br : BytesRefImm σ size align) (i : USize)
    (h : i.toNat * byteSize.toNat + byteSize.toNat ≤ size.toNat) : ST σ α :=
      readBytesRefOffUnal br (i * byteSize) (by rw [offEl_no_overflow i h]; exact h)

  readBytesRefOff {σ size align} (br : BytesRefImm σ size align) (i : USize)
    (h₁ : i.toNat + byteSize.toNat ≤ size.toNat)
    (h₂ : (∀ m, ∃ n, align * m + i.toNat = alignment * n)) : ST σ α :=
      readBytesRefOffUnal br i h₁

  readBytesRef {σ} (br : BytesRefImm σ byteSize alignment) : ST σ α :=
    readBytesRefOff br 0 (Nat.le_of_eq $ Nat.zero_add _) λ m ↦
      Exists.intro m (by rw [Nat.add_comm]; exact Nat.zero_add _)

  readBytesRefOffEl {σ size} (br : BytesRefImm σ size alignment) (i : USize)
    (h : i.toNat * byteSize.toNat + byteSize.toNat ≤ size.toNat) : ST σ α :=
      readBytesRefOff br (i * byteSize) (by rw [offEl_no_overflow i h]; exact h) (offEl_aligned i h)

  readBytesViewOffUnal {size align} : BytesView size align → (i : USize) →
    i.toNat + byteSize.toNat ≤ size.toNat → α

  readBytesViewUnal {align} (bv : BytesView byteSize align) : α :=
    readBytesViewOffUnal bv 0 (Nat.le_of_eq $ Nat.zero_add _)

  readBytesViewOffElUnal {size align} (bv : BytesView size align)
    (i : USize) (h : i.toNat * byteSize.toNat + byteSize.toNat ≤ size.toNat) : α :=
      readBytesViewOffUnal bv (i * byteSize) (by rw [offEl_no_overflow i h]; exact h)

  readBytesViewOff {size align} : BytesView size align → (i : USize) →
    i.toNat + byteSize.toNat ≤ size.toNat →
    (∀ m, ∃ n, align * m + i.toNat = alignment * n) → α

  readBytesView (bv : BytesView byteSize alignment) : α :=
    readBytesViewOff bv 0 (Nat.le_of_eq $ Nat.zero_add _) λ m ↦
      Exists.intro m (by rw [Nat.add_comm]; exact Nat.zero_add _)

  readBytesViewOffEl {size} (bv : BytesView size alignment)
    (i : USize) (h : i.toNat * byteSize.toNat + byteSize.toNat ≤ size.toNat) : α :=
      readBytesViewOff bv (i * byteSize) (by rw [offEl_no_overflow i h]; exact h) (offEl_aligned i h)


def BytesRef.getUnal {α σ align} [ReadBytes α] (br : BytesRefImm σ (byteSize α) align) : ST σ α :=
  ReadBytes.readBytesRefUnal br

def BytesRef.ugetOffUnal {α σ size align} [ReadBytes α] (br : BytesRefImm σ size align) (i : USize)
  (h₁ : i.toNat + (byteSize α).toNat ≤ size.toNat) : ST σ α :=
    ReadBytes.readBytesRefOffUnal br i h₁

def BytesRef.getOffUnal {α σ size align} [ReadBytes α] (br : BytesRefImm σ size align) (i : Nat)
  (h₁ : i + (byteSize α).toNat ≤ size.toNat) : ST σ α :=
    ReadBytes.readBytesRefOffUnal br ⟨i, off_lt_usize_size i h₁⟩ h₁

def BytesRef.ugetOffElUnal {α σ size align} [ReadBytes α] (br : BytesRefImm σ size align)
  (i : USize) (h : i.toNat * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) : ST σ α :=
    ReadBytes.readBytesRefOffElUnal br i h

def BytesRef.getOffElUnal {α σ size align} [ReadBytes α] (br : BytesRefImm σ size align)
  (i : Nat) (h : i * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) : ST σ α :=
    ReadBytes.readBytesRefOffElUnal br ⟨i, offEl_lt_usize_size i h⟩ h

def BytesRef.get {α σ} [ReadBytes α] (br : BytesRefImm σ (byteSize α) (alignment α)) : ST σ α :=
  ReadBytes.readBytesRef br

def BytesRef.ugetOff {α σ size align} [ReadBytes α] (br : BytesRefImm σ size align) (i : USize)
  (h₁ : i.toNat + (byteSize α).toNat ≤ size.toNat)
  (h₂ : ∀ m, ∃ n, align * m + i.toNat = alignment α * n) : ST σ α :=
    ReadBytes.readBytesRefOff br i h₁ h₂

def BytesRef.getOff {α σ size align} [ReadBytes α] (br : BytesRefImm σ size align) (i : Nat)
  (h₁ : i + (byteSize α).toNat ≤ size.toNat)
  (h₂ : ∀ m, ∃ n, align * m + i = alignment α * n) : ST σ α :=
    ReadBytes.readBytesRefOff br ⟨i, off_lt_usize_size i h₁⟩ h₁ h₂

def BytesRef.ugetOffEl {α σ size} [ReadBytes α] (br : BytesRefImm σ size (alignment α))
  (i : USize) (h : i.toNat * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) : ST σ α :=
    ReadBytes.readBytesRefOffEl br i h

def BytesRef.getOffEl {α σ size} [ReadBytes α] (br : BytesRefImm σ size (alignment α))
  (i : Nat) (h : i * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) : ST σ α :=
    ReadBytes.readBytesRefOffEl br ⟨i, offEl_lt_usize_size i h⟩ h

def BytesView.getUnal {α align} [ReadBytes α] (bv : BytesView (byteSize α) align) : α :=
  ReadBytes.readBytesViewUnal bv

def BytesView.ugetOffUnal {α size align} [ReadBytes α] (bv : BytesView size align) (i : USize)
  (h₁ : i.toNat + (byteSize α).toNat ≤ size.toNat) : α :=
    ReadBytes.readBytesViewOffUnal bv i h₁

def BytesView.getOffUnal {α size align} [ReadBytes α] (bv : BytesView size align) (i : Nat)
  (h₁ : i + (byteSize α).toNat ≤ size.toNat) : α :=
    ReadBytes.readBytesViewOffUnal bv ⟨i, off_lt_usize_size i h₁⟩ h₁

def BytesView.ugetOffElUnal {α size align} [ReadBytes α] (bv : BytesView size align)
  (i : USize) (h : i.toNat * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) : α :=
    ReadBytes.readBytesViewOffElUnal bv i h

def BytesView.getOffElUnal {α size align} [ReadBytes α] (bv : BytesView size align)
  (i : Nat) (h : i * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) : α :=
    ReadBytes.readBytesViewOffElUnal bv ⟨i, offEl_lt_usize_size i h⟩ h

def BytesView.get {α} [ReadBytes α] (bv : BytesView (byteSize α) (alignment α)) : α :=
  ReadBytes.readBytesView bv

def BytesView.ugetOff {α size align} [ReadBytes α] (bv : BytesView size align) (i : USize)
  (h₁ : i.toNat + (byteSize α).toNat ≤ size.toNat)
  (h₂ : ∀ m, ∃ n, align * m + i.toNat = alignment α * n) : α :=
    ReadBytes.readBytesViewOff bv i h₁ h₂

def BytesView.getOff {α size align} [ReadBytes α] (bv : BytesView size align) (i : Nat)
  (h₁ : i + (byteSize α).toNat ≤ size.toNat)
  (h₂ : ∀ m, ∃ n, align * m + i = alignment α * n) : α :=
    ReadBytes.readBytesViewOff bv ⟨i, off_lt_usize_size i h₁⟩ h₁ h₂

def BytesView.ugetOffEl {α size} [ReadBytes α] (bv : BytesView size (alignment α))
  (i : USize) (h : i.toNat * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) : α :=
    ReadBytes.readBytesViewOffEl bv i h

def BytesView.getOffEl {α size} [ReadBytes α] (bv : BytesView size (alignment α))
  (i : Nat) (h : i * (byteSize α).toNat + (byteSize α).toNat ≤ size.toNat) : α :=
    ReadBytes.readBytesViewOffEl bv ⟨i, offEl_lt_usize_size i h⟩ h
