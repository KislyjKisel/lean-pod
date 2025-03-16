namespace Pod

@[inline]
unsafe def Array.modifyGetImpl {α β} (a : Array α) (i : Nat) (h : i < a.size) (f : α → β × α) : β × Array α :=
  let v := a[i]
  let a' := a.set i (unsafeCast ())
  let (x, v) := f v
  (x, a'.set i v (Nat.lt_of_lt_of_eq h (Array.size_set a ..).symm))

@[implemented_by modifyGetImpl]
def Array.modifyGet {α β} (a : Array α) (i : Nat) (h : i < a.size) (f : α → β × α) : β × Array α :=
  let v := a[i]
  let (x, v) := f v
  (x, a.set i v)
