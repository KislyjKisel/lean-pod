namespace Pod

theorem _root_.Fin.toNat_sub_distrib {n} (a b : Fin n) (h : b ≤ a) :
  (a - b).val = a.val - b.val := by
  let aLt := a.isLt
  let a := a.val
  let bLt := b.isLt
  let b := b.val
  show (a + (n - b)) % n = a - b
  rw [
    ← Nat.add_sub_assoc (k := b) (Nat.le_of_lt bLt) a,
    Nat.add_comm,
    Nat.add_sub_assoc (m := a) (k := b) h n,
    Nat.mod_eq_sub_mod $ Nat.le_add_right n (a - b),
    Nat.add_sub_cancel_left,
    ]
  apply Nat.mod_eq_of_lt
  apply Nat.lt_of_le_of_lt
  · exact Nat.sub_le a b
  · exact aLt

theorem usize_size_ge_2_pow_32 : USize.size ≥ 2 ^ 32 :=
  match usize_size_eq with
    | Or.inl p => Nat.le_of_eq p.symm
    | Or.inr p => Nat.le_of_lt $ Nat.lt_of_lt_of_eq (by decide) p.symm

theorem mod_usize_size_eq (i : Nat) (h : i < 2^32) : i % USize.size = i :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h usize_size_ge_2_pow_32)
