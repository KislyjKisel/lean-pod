import Pod.Storable
import Pod.BytesRef
import Pod.BytesView

namespace Pod

class ReadBytes (α : Type) extends Storable α where
  readBytesRefOffUnal {σ size align} : BytesRefImm σ size align → (i : Nat) →
    i + byteSize ≤ size → ST σ α

  readBytesRefUnal {σ align} (br : BytesRefImm σ byteSize align) : ST σ α :=
    readBytesRefOffUnal br 0 (Nat.le_of_eq $ Nat.zero_add _)

  readBytesRefOffElUnal {σ size align} (br : BytesRefImm σ size align) (i : Nat)
    (h : i * byteSize + byteSize ≤ size) : ST σ α :=
      readBytesRefOffUnal br (i * byteSize) h

  readBytesRefOff {σ size align} (br : BytesRefImm σ size align) (i : Nat)
    (h₁ : i + byteSize ≤ size)
    (h₂ : (∀ m, ∃ n, align * m + i = alignment * n)) : ST σ α :=
      readBytesRefOffUnal br i h₁

  readBytesRef {σ} (br : BytesRefImm σ byteSize alignment) : ST σ α :=
    readBytesRefOff br 0 (Nat.le_of_eq $ Nat.zero_add _) λ m ↦
      Exists.intro m (by rw [Nat.add_comm]; exact Nat.zero_add _)

  readBytesRefOffEl {σ size} (br : BytesRefImm σ size alignment) (i : Nat)
    (h : i * byteSize + byteSize ≤ size) : ST σ α :=
      readBytesRefOff br (i * byteSize) h (offEl_aligned i)

  readBytesViewOffUnal {size align} : BytesView size align → (i : Nat) →
    i + byteSize ≤ size → α

  readBytesViewUnal {align} (bv : BytesView byteSize align) : α :=
    readBytesViewOffUnal bv 0 (Nat.le_of_eq $ Nat.zero_add _)

  readBytesViewOffElUnal {size align} (bv : BytesView size align)
    (i : Nat) (h : i * byteSize + byteSize ≤ size) : α :=
      readBytesViewOffUnal bv (i * byteSize) h

  readBytesViewOff {size align} : BytesView size align → (i : Nat) →
    i + byteSize ≤ size →
    (∀ m, ∃ n, align * m + i = alignment * n) → α

  readBytesView (bv : BytesView byteSize alignment) : α :=
    readBytesViewOff bv 0 (Nat.le_of_eq $ Nat.zero_add _) λ m ↦
      Exists.intro m (by rw [Nat.add_comm]; exact Nat.zero_add _)

  readBytesViewOffEl {size} (bv : BytesView size alignment)
    (i : Nat) (h : i * byteSize + byteSize ≤ size) : α :=
      readBytesViewOff bv (i * byteSize) h (offEl_aligned i)

def BytesRef.getUnal {α σ align} [ReadBytes α] (br : BytesRefImm σ (byteSize α) align) : ST σ α :=
  ReadBytes.readBytesRefUnal br

def BytesRef.getOffUnal {α σ size align} [ReadBytes α] (br : BytesRefImm σ size align) (i : Nat)
  (h₁ : i + (byteSize α) ≤ size) : ST σ α :=
    ReadBytes.readBytesRefOffUnal br i h₁

def BytesRef.getOffElUnal {α σ size align} [ReadBytes α] (br : BytesRefImm σ size align)
  (i : Nat) (h : i * (byteSize α) + (byteSize α) ≤ size) : ST σ α :=
    ReadBytes.readBytesRefOffElUnal br i h

def BytesRef.get {α σ} [ReadBytes α] (br : BytesRefImm σ (byteSize α) (alignment α)) : ST σ α :=
  ReadBytes.readBytesRef br

def BytesRef.getOff {α σ size align} [ReadBytes α] (br : BytesRefImm σ size align) (i : Nat)
  (h₁ : i + (byteSize α) ≤ size)
  (h₂ : ∀ m, ∃ n, align * m + i = alignment α * n) : ST σ α :=
    ReadBytes.readBytesRefOff br i h₁ h₂

def BytesRef.getOffEl {α σ size} [ReadBytes α] (br : BytesRefImm σ size (alignment α))
  (i : Nat) (h : i * (byteSize α) + (byteSize α) ≤ size) : ST σ α :=
    ReadBytes.readBytesRefOffEl br i h

def BytesView.getUnal {α align} [ReadBytes α] (bv : BytesView (byteSize α) align) : α :=
  ReadBytes.readBytesViewUnal bv

def BytesView.getOffUnal {α size align} [ReadBytes α] (bv : BytesView size align) (i : Nat)
  (h₁ : i + (byteSize α) ≤ size) : α :=
    ReadBytes.readBytesViewOffUnal bv i h₁

def BytesView.getOffElUnal {α size align} [ReadBytes α] (bv : BytesView size align)
  (i : Nat) (h : i * (byteSize α) + (byteSize α) ≤ size) : α :=
    ReadBytes.readBytesViewOffElUnal bv i h

def BytesView.get {α} [ReadBytes α] (bv : BytesView (byteSize α) (alignment α)) : α :=
  ReadBytes.readBytesView bv

def BytesView.getOff {α size align} [ReadBytes α] (bv : BytesView size align) (i : Nat)
  (h₁ : i + (byteSize α) ≤ size)
  (h₂ : ∀ m, ∃ n, align * m + i = alignment α * n) : α :=
    ReadBytes.readBytesViewOff bv i h₁ h₂

def BytesView.getOffEl {α size} [ReadBytes α] (bv : BytesView size (alignment α))
  (i : Nat) (h : i * (byteSize α) + (byteSize α) ≤ size) : α :=
    ReadBytes.readBytesViewOffEl bv i h
