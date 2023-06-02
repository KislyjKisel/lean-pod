import Pod

def test : ByteArray :=
  let a := #[142, 142, 142, 142, 142]
  (ByteArray.mk a).withRef λ ref ↦ do
    let mut i : USize := 0
    while h: i < 5 do
      Pod.BytesRef.usetOffEl (Eq.ndrec (motive := Pod.BytesRefMut _ _) ref (by rfl)) i i.toUInt64.toUInt8 $ by
        show i.val.val * (1 % USize.size) + (1 % USize.size) ≤ 5 % USize.size
        rewrite [
          Nat.mod_eq_of_lt (a := 1) (Nat.lt_of_lt_of_le (by decide) Pod.usize_size_ge_2_pow_32),
          Nat.mul_one,
        ]
        apply Nat.succ_le_of_lt
        exact h
      i := i + 1

def main : IO Unit := do
  let bb := test.view
  IO.println $ bb[0]!
  IO.println $ bb[1]!
  IO.println $ bb[2]!
  IO.println $ bb[3]!
  IO.println $ bb[4]!

  let uv : Pod.UVector UInt64 3 := .replicate 42
  IO.print s!"UV: {uv[0]}, {uv[1]}, {uv[2]!} --> "
  let uv := ((uv.set! 2 (UInt64.complement 0)).set 0 0).set 1 ((UInt64.complement 0) / 3)
  IO.println s!"{uv[0]}, {uv[1]!}, {uv[2]}"

  let mut count := 10
  repeat do
    IO.println "HI"
    IO.sleep 100
    count := count - 1
    if count = 0 then break
