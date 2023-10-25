import Pod.Storable
import Pod.BytesRef
import Pod.BytesView

namespace Pod

class ReadBytes (α : Type) [Storable α] where
  readBytesRefOffUnal {σ size align} : BytesRefImm σ size align → (i : Nat) →
    i + byteSize α ≤ size → ST σ α

  readBytesRefUnal {σ align} (br : BytesRefImm σ (byteSize α) align) : ST σ α :=
    readBytesRefOffUnal br 0 (Nat.le_of_eq $ Nat.zero_add _)

  readBytesRefOffElUnal {σ size align} (br : BytesRefImm σ size align) (i : Nat)
    (h : i * byteSize α + byteSize α ≤ size) : ST σ α :=
      readBytesRefOffUnal br (i * byteSize α) h

  readBytesRefOff {σ size align} (br : BytesRefImm σ size align) (i : Nat)
    (h₁ : i + (byteSize α) ≤ size)
    (h₂ : (∀ m, ∃ n, align * m + i = alignment α * n)) : ST σ α :=
      readBytesRefOffUnal br i h₁

  readBytesRef {σ} (br : BytesRefImm σ (byteSize α) (alignment α)) : ST σ α :=
    readBytesRefOff br 0 (Nat.le_of_eq $ Nat.zero_add _) λ m ↦
      Exists.intro m (by rw [Nat.add_comm]; exact Nat.zero_add _)

  readBytesRefOffEl {σ size} (br : BytesRefImm σ size (alignment α)) (i : Nat)
    (h : i * byteSize α + byteSize α ≤ size) : ST σ α :=
      readBytesRefOff br (i * byteSize α) h (offEl_aligned i)

  readBytesViewOffUnal {size align} : BytesView size align → (i : Nat) →
    i + byteSize α ≤ size → α

  readBytesViewUnal {align} (bv : BytesView (byteSize α) align) : α :=
    readBytesViewOffUnal bv 0 (Nat.le_of_eq $ Nat.zero_add _)

  readBytesViewOffElUnal {size align} (bv : BytesView size align)
    (i : Nat) (h : i * byteSize α + byteSize α ≤ size) : α :=
      readBytesViewOffUnal bv (i * byteSize α) h

  readBytesViewOff {size align} : BytesView size align → (i : Nat) →
    i + byteSize α ≤ size →
    (∀ m, ∃ n, align * m + i = alignment α * n) → α

  readBytesView (bv : BytesView (byteSize α) (alignment α)) : α :=
    readBytesViewOff bv 0 (Nat.le_of_eq $ Nat.zero_add _) λ m ↦
      Exists.intro m (by rw [Nat.add_comm]; exact Nat.zero_add _)

  readBytesViewOffEl {size} (bv : BytesView size (alignment α))
    (i : Nat) (h : i * byteSize α + byteSize α ≤ size) : α :=
      readBytesViewOff bv (i * byteSize α) h (offEl_aligned i)

variable {α σ : Type} {align : Nat} [Storable α] [ReadBytes α]

def BytesRef.getUnal (br : BytesRefImm σ (byteSize α) align) : ST σ α :=
  ReadBytes.readBytesRefUnal br

def BytesRef.getOffUnal (br : BytesRefImm σ size align) (i : Nat)
  (h₁ : i + (byteSize α) ≤ size) : ST σ α :=
    ReadBytes.readBytesRefOffUnal br i h₁

def BytesRef.getOffElUnal (br : BytesRefImm σ size align)
  (i : Nat) (h : i * (byteSize α) + (byteSize α) ≤ size) : ST σ α :=
    ReadBytes.readBytesRefOffElUnal br i h

def BytesRef.get (br : BytesRefImm σ (byteSize α) (alignment α)) : ST σ α :=
  ReadBytes.readBytesRef br

def BytesRef.getOff (br : BytesRefImm σ size align) (i : Nat)
  (h₁ : i + (byteSize α) ≤ size)
  (h₂ : ∀ m, ∃ n, align * m + i = alignment α * n) : ST σ α :=
    ReadBytes.readBytesRefOff br i h₁ h₂

def BytesRef.getOffEl (br : BytesRefImm σ size (alignment α))
  (i : Nat) (h : i * (byteSize α) + (byteSize α) ≤ size) : ST σ α :=
    ReadBytes.readBytesRefOffEl br i h

def BytesView.getUnal (bv : BytesView (byteSize α) align) : α :=
  ReadBytes.readBytesViewUnal bv

def BytesView.getOffUnal (bv : BytesView size align) (i : Nat)
  (h₁ : i + (byteSize α) ≤ size) : α :=
    ReadBytes.readBytesViewOffUnal bv i h₁

def BytesView.getOffElUnal (bv : BytesView size align)
  (i : Nat) (h : i * (byteSize α) + (byteSize α) ≤ size) : α :=
    ReadBytes.readBytesViewOffElUnal bv i h

def BytesView.get (bv : BytesView (byteSize α) (alignment α)) : α :=
  ReadBytes.readBytesView bv

def BytesView.getOff (bv : BytesView size align) (i : Nat)
  (h₁ : i + (byteSize α) ≤ size)
  (h₂ : ∀ m, ∃ n, align * m + i = alignment α * n) : α :=
    ReadBytes.readBytesViewOff bv i h₁ h₂

def BytesView.getOffEl (bv : BytesView size (alignment α))
  (i : Nat) (h : i * (byteSize α) + (byteSize α) ≤ size) : α :=
    ReadBytes.readBytesViewOffEl bv i h
