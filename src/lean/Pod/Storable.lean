import Pod.Lemmas

namespace Pod

class Storable (α : Type) where
  byteSize : USize
  byteSize_gt_zero : byteSize.toNat > 0
  alignment : Nat
  alignment_dvd_byteSize : ∃ k, byteSize.toNat = alignment * k

export Storable (byteSize byteSize_gt_zero alignment alignment_dvd_byteSize)

theorem not_alignment_eq_zero {α} [Storable α] : ¬ alignment α = 0 := by
    intro h
    apply Nat.not_eq_zero_of_lt $ byteSize_gt_zero (α := α)
    apply (@alignment_dvd_byteSize α).elim
    intro k b
    rw [b, h]
    exact Nat.zero_mul k

def bitWidth {α} [Storable α] : USize := byteSize α * 8

instance : Storable UInt8 where
  byteSize := 1
  byteSize_gt_zero := Nat.lt_of_lt_of_eq (by constructor) (mod_usize_size_eq 1 $ by decide).symm
  alignment := 1
  alignment_dvd_byteSize := Exists.intro 1 (mod_usize_size_eq 1 $ by decide)

instance : Storable UInt16 where
  byteSize := 2
  byteSize_gt_zero := Nat.lt_of_lt_of_eq (by decide) (mod_usize_size_eq 2 $ by decide).symm
  alignment := 2
  alignment_dvd_byteSize := Exists.intro 1 (mod_usize_size_eq 2 $ by decide)

instance : Storable UInt32 where
  byteSize := 4
  byteSize_gt_zero := Nat.lt_of_lt_of_eq (by decide) (mod_usize_size_eq 4 $ by decide).symm
  alignment := 4
  alignment_dvd_byteSize := Exists.intro 1 (mod_usize_size_eq 4 $ by decide)

@[extern "lean_pod_UInt64_getAlignment"]
private
opaque UInt64.getAlignment : @& Unit → { n : Nat // n = 4 ∨ n = 8 } := λ _ ↦ ⟨8, Or.inr rfl⟩

instance : Storable UInt64 where
  byteSize := 8
  byteSize_gt_zero := Nat.lt_of_lt_of_eq (by decide) (mod_usize_size_eq 8 $ by decide).symm
  alignment := (UInt64.getAlignment ()).val
  alignment_dvd_byteSize := match (UInt64.getAlignment ()).property with
    | Or.inl h => Exists.intro 2 $ by show 8 % USize.size = _; rw [h, mod_usize_size_eq 8 $ by decide]
    | Or.inr h => Exists.intro 1 $ by show 8 % USize.size = _; rw [h, mod_usize_size_eq 8 $ by decide]

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
  byteSize_gt_zero := Nat.lt_of_lt_of_eq (by decide) (mod_usize_size_eq 8 $ by decide).symm
  alignment := (Float.getAlignment ()).val
  alignment_dvd_byteSize := match (Float.getAlignment ()).property with
    | Or.inl h => Exists.intro 2 $ by show 8 % USize.size = _; rw [h, mod_usize_size_eq 8 $ by decide]
    | Or.inr h => Exists.intro 1 $ by show 8 % USize.size = _; rw [h, mod_usize_size_eq 8 $ by decide]

theorem alignment_Float_eq : alignment Float = 4 ∨ alignment Float = 8 :=
  (Float.getAlignment ()).property

theorem offEl_no_overflow {α size} [Storable α] (i : USize)
  (h : i.toNat * (byteSize α).toNat + (byteSize α).toNat ≤ USize.toNat size) :
    (i * byteSize α).toNat = i.toNat * (byteSize α).toNat := by
      apply Nat.mod_eq_of_lt
      apply Nat.lt_of_le_of_lt
      · show i.toNat * (byteSize α).toNat + 0 ≤ i.toNat * (byteSize α).toNat + (byteSize α).toNat
        apply Nat.add_le_add_left
        exact Nat.zero_le _
      · exact Nat.lt_of_le_of_lt h size.val.isLt

theorem offEl_aligned {α size} [Storable α] (i : USize)
  (h : i.toNat * (byteSize α).toNat + (byteSize α).toNat ≤ USize.toNat size) :
  ∀ m, ∃ n, alignment α * m + (i * byteSize α).toNat = (alignment α) * n := λ m ↦
    (alignment_dvd_byteSize (α := α)).elim λ aib h₁ ↦
      Exists.intro (m + i.toNat * aib) $ by
        rewrite [Nat.left_distrib]
        apply congrArg (alignment α * m + ·)
        rewrite [Nat.mul_comm _ aib, ← Nat.mul_assoc, ← h₁, Nat.mul_comm]
        rw [offEl_no_overflow i h]

theorem off_lt_usize_size {α size} [Storable α] (i : Nat) (h : i + (byteSize α).toNat ≤ USize.toNat size) :
  i < USize.size := calc
    i ≤ i + (byteSize α).toNat := Nat.add_le_add_left (Nat.zero_le _) i
    _ ≤ size.toNat             := h
    _ < USize.size             := size.val.isLt

theorem offEl_lt_usize_size {α size} [Storable α] (i : Nat)
  (h : i * (byteSize α).toNat + (byteSize α).toNat ≤ USize.toNat size) :
    i < USize.size := calc
      i = i * 1                                       := Eq.symm (Nat.mul_one i)
      _ ≤ i * (byteSize α).toNat + 0                  := Nat.mul_le_mul_left i byteSize_gt_zero
      _ ≤ i * (byteSize α).toNat + (byteSize α).toNat := Nat.add_le_add_left (Nat.zero_le _) _
      _ ≤ size.toNat                                  := h
      _ < USize.size                                  := size.val.isLt

end Pod
