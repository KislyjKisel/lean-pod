import Pod.Lemmas

namespace Pod

class Storable (α : Type _) where
  byteSize : Nat
  alignment : Nat
  byteSize_gt_zero : byteSize > 0 := by decide
  alignment_dvd_byteSize : ∃ k, byteSize = alignment * k := by exists 1

export Storable (byteSize byteSize_gt_zero alignment alignment_dvd_byteSize)

abbrev byteSizeArray (α : Type) [Storable α] (n : Nat) : Nat := n * byteSize α

theorem not_alignment_eq_zero {α} [Storable α] : ¬ alignment α = 0 := by
  intro h
  apply Nat.not_eq_zero_of_lt $ byteSize_gt_zero (α := α)
  apply (@alignment_dvd_byteSize α).elim
  intro k b
  rw [b, h]
  exact Nat.zero_mul k

abbrev bitWidth {α} [Storable α] : Nat := byteSize α * 8

instance : Storable UInt8 where
  byteSize := 1
  alignment := 1

instance : Storable UInt16 where
  byteSize := 2
  alignment := 2

instance : Storable UInt32 where
  byteSize := 4
  alignment := 4

@[extern "lean_pod_UInt64_getAlignment"]
private
opaque UInt64.getAlignment : @& Unit → { n : Nat // n = 4 ∨ n = 8 } := λ _ ↦ ⟨8, Or.inr rfl⟩

instance : Storable UInt64 where
  byteSize := 8
  alignment := (UInt64.getAlignment ()).val
  alignment_dvd_byteSize :=
    match (UInt64.getAlignment ()).property with
    | Or.inl h => Exists.intro 2 $ by rw [h]
    | Or.inr h => Exists.intro 1 $ by rw [h]

theorem alignment_UInt64_eq : alignment UInt64 = 4 ∨ alignment UInt64 = 8 :=
  (UInt64.getAlignment ()).property

instance : Storable USize where
  byteSize := if System.Platform.numBits = 32 then byteSize UInt32 else byteSize UInt64
  byteSize_gt_zero := match System.Platform.numBits, System.Platform.numBits_eq with
    | 32, Or.inl _ => byteSize_gt_zero
    | 64, Or.inr _ => byteSize_gt_zero
  alignment := if System.Platform.numBits = 32 then alignment UInt32 else alignment UInt64
  alignment_dvd_byteSize := match System.Platform.numBits, System.Platform.numBits_eq with
    | 32, Or.inl _ => alignment_dvd_byteSize
    | 64, Or.inr _ => alignment_dvd_byteSize

@[extern "lean_pod_Float_getAlignment"]
private
opaque Float.getAlignment : @& Unit → { n : Nat // n = 4 ∨ n = 8 } := λ _ ↦ ⟨8, Or.inr rfl⟩

instance : Storable Float where
  byteSize := 8
  alignment := (Float.getAlignment ()).val
  alignment_dvd_byteSize := match (Float.getAlignment ()).property with
    | Or.inl h => Exists.intro 2 $ by rw [h]
    | Or.inr h => Exists.intro 1 $ by rw [h]

theorem alignment_Float_eq : alignment Float = 4 ∨ alignment Float = 8 :=
  (Float.getAlignment ()).property

theorem offEl_aligned {α} [Storable α] (i : Nat) :
  ∀ m, ∃ n, alignment α * m + i * byteSize α = (alignment α) * n := λ m ↦
    (alignment_dvd_byteSize (α := α)).elim λ aib h₁ ↦
      Exists.intro (m + i * aib) $ by
        rewrite [Nat.left_distrib]
        apply congrArg (alignment α * m + ·)
        rw [Nat.mul_comm _ aib, ← Nat.mul_assoc, ← h₁, Nat.mul_comm]

end Pod
